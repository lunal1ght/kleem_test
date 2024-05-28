//===-- ListenerService.cpp --------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LIB_CORE_LISTENERSERVICE_C_
#define LIB_CORE_LISTENERSERVICE_C_

#include <iterator>
#include <stddef.h>
#include <sys/time.h>

#include "llvm/IR/CallSite.h"
#include "llvm/Support/raw_ostream.h"
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>

#include "../Core/Executor.h"
#include "../Core/ExternalDispatcher.h"
#include "klee/Encode/DTAM.h"
#include "klee/Encode/Encode.h"
#include "klee/Encode/ListenerService.h"
#include "klee/Encode/PSOListener.h"
#include "klee/Encode/Prefix.h"
#include "klee/Encode/SymbolicListener.h"
#include "klee/Encode/TaintListener.h"
#include "klee/Thread/StackType.h"
#include "klee/Config/DebugMacro.h"
#include "klee/Support/ErrorHandling.h"

extern void *__dso_handle __attribute__((__weak__));

namespace klee {

ListenerService::ListenerService(Executor *executor) {
  rdManager = new RuntimeDataManager();
  interpreterHandler = executor->getHandlerPtr();
  encoder = NULL;
  dtam = NULL;
  cost = 0;
}

ListenerService::~ListenerService() {
  auto os = interpreterHandler->openKleemOutputFile("result.txt");
  assert(os && "Can't create file to log result.");
  *os << rdManager->getResultString();
  os->flush();
  interpreterHandler->setNumPathsDistrinct(rdManager->getTestedPathsNumber());
  for (auto listener : bitcodeListeners) {
    delete listener;
  }
  delete rdManager;
  delete encoder;
  delete dtam;
}

void ListenerService::pushListener(BitcodeListener *bitcodeListener) {
  bitcodeListeners.push_back(bitcodeListener);
}

void ListenerService::removeListener(BitcodeListener *bitcodeListener) {
  for (auto bit = bitcodeListeners.begin(), bie = bitcodeListeners.end(); bit != bie; ++bit) {
    if ((*bit) == bitcodeListener) {
      bitcodeListeners.erase(bit);
      break;
    }
  }
}

void ListenerService::removeListener(BitcodeListener::ListenerKind kind) {
  for (auto bit = bitcodeListeners.begin(), bie = bitcodeListeners.end(); bit != bie; ++bit) {
    if ((*bit)->kind == kind) {
      bitcodeListeners.erase(bit);
      break;
    }
  }
}

void ListenerService::popListener() {
  bitcodeListeners.pop_back();
}

RuntimeDataManager *ListenerService::getRuntimeDataManager() {
  return rdManager;
}

void ListenerService::beforeRunMethodAsMain(Executor *executor, ExecutionState &state, llvm::Function *f,
                                            MemoryObject *argvMO, std::vector<ref<Expr>> arguments, int argc,
                                            char **argv, char **envp) {

  Module *m = executor->kmodule->module.get();
  unsigned NumPtrBytes = Context::get().getPointerWidth() / 8;
  int envc;
  for (envc = 0; envp[envc]; ++envc)
    ;

  for (auto bit : bitcodeListeners) {
    state.currentStack = bit->stack[state.currentThread->threadId];
    state.currentStack->pushFrame(0, executor->kmodule->functionMap[f]);

    for (unsigned i = 0, e = f->arg_size(); i != e; ++i)
      executor->bindArgument(executor->kmodule->functionMap[f], i, state, arguments[i]);
    if (argvMO) {
      const ObjectState *argvOSCurrent = state.currentThread->addressSpace->findObject(argvMO);
      ObjectState *argvOS = executor->bindObjectInState(state, argvMO, false);
      for (int i = 0; i < argc + 1 + envc + 1 + 1; i++) {
        if (i == argc || i >= argc + 1 + envc) {
          // Write NULL pointer
          argvOS->write(i * NumPtrBytes, Expr::createPointer(0));
        } else {
          char *s = i < argc ? argv[i] : envp[i - (argc + 1)];
          int j, len = strlen(s);
          ref<Expr> argAddr = argvOSCurrent->read(i * NumPtrBytes, Context::get().getPointerWidth());
          ObjectPair op;
          bool success = executor->getMemoryObject(op, state, state.currentThread->addressSpace, argAddr);
          if (success) {
            const MemoryObject *arg = op.first;
            ObjectState *os = executor->bindObjectInState(state, arg, false);
            for (j = 0; j < len + 1; j++) {
              os->write8(j, s[j]);
            }
            argvOS->write(i * NumPtrBytes, arg->getBaseExpr());
          }
        }
      }
    }

    for (llvm::Module::const_global_iterator gitr = m->global_begin(), e = m->global_end(); gitr != e; ++gitr) {
      if (gitr->isDeclaration()) {
        Type *ty = gitr->getType()->getElementType();
        uint64_t size = executor->kmodule->targetData->getTypeStoreSize(ty);
        MemoryObject *mo = executor->globalObjects.find(&*gitr)->second;
        ObjectState *os = executor->bindObjectInState(state, mo, false);
        if (size) {
          void *addr;
          if (gitr->getName() == "__dso_handle") {
            addr = &__dso_handle; // wtf ?
          } else {
            addr = executor->externalDispatcher->resolveSymbol(gitr->getName());
          }
          for (unsigned offset = 0; offset < mo->size; offset++)
            os->write8(offset, ((unsigned char *)addr)[offset]);
        }
      } else {
        MemoryObject *mo = executor->globalObjects.find(&*gitr)->second;
        ObjectState *os = executor->bindObjectInState(state, mo, false);
        if (!gitr->hasInitializer())
          os->initializeToRandom();
      }
    }
    for (llvm::Module::const_global_iterator it = m->global_begin(), e = m->global_end(); it != e; ++it) {
      if (it->hasInitializer()) {
        MemoryObject *mo = executor->globalObjects.find(&*it)->second;
        const ObjectState *os = state.currentStack->addressSpace->findObject(mo);
        ObjectState *wos = state.currentStack->addressSpace->getWriteable(mo, os);
        executor->initializeGlobalObject(state, wos, it->getInitializer(), 0);
      }
    }

    bit->beforeRunMethodAsMain(state);

    state.currentStack = state.currentThread->stack;
  }
}

void ListenerService::beforeExecuteInstruction(Executor *executor, ExecutionState &state, KInstruction *ki) {
#if DEBUG_RUNTIME_LISTENER
  std::string instStr;
  raw_string_ostream str(instStr);
  ki->inst->print(str);
  kleem_debug("Thread %d, %s", state.currentThread->threadId, instStr.c_str());
#endif
  for (auto bit : bitcodeListeners) {
    state.currentStack = bit->stack[state.currentThread->threadId];
    bit->beforeExecuteInstruction(state, ki);
    state.currentStack = state.currentThread->stack;
  }

  Instruction *llvmInst = ki->inst;
  switch (llvmInst->getOpcode()) {
    case Instruction::Ret: {
      break;
    }
    case Instruction::Invoke: {
      break;
    }
    case Instruction::Call: {
      CallSite cs(llvmInst);
      unsigned numArgs = cs.arg_size();
      Value *fp = cs.getCalledValue();
      Function *func = executor->getTargetFunction(fp, state);
      if (!func) {
        assert(0 && "listenerSercive execute call");
      }
      if (func->getName().str().find("llvm.dbg.declare") != std::string::npos || func->getName().str().find("llvm.dbg.label") != std::string::npos)
        break;
      for (auto listener : bitcodeListeners) {
        state.currentStack = listener->stack[state.currentThread->threadId];
        listener->arguments.reserve(numArgs);
        for (unsigned j = 0; j < numArgs; ++j) {
          listener->arguments.push_back(executor->eval(ki, j + 1, state).value);
        }
        const FunctionType *fType = dyn_cast<FunctionType>(cast<PointerType>(func->getType())->getElementType());
        const FunctionType *fpType = dyn_cast<FunctionType>(cast<PointerType>(fp->getType())->getElementType());
        if (fType != fpType) {
          unsigned i = 0;
          for (auto arg : listener->arguments) {
            Expr::Width to, from = arg->getWidth();
            if (i < fType->getNumParams()) {
              to = executor->getWidthForLLVMType(fType->getParamType(i));
              if (from != to) {
                bool isSExt = cs.paramHasAttr(i + 1, llvm::Attribute::SExt);
                if (isSExt) {
                  listener->arguments[i] = SExtExpr::create(listener->arguments[i], to);
                } else {
                  listener->arguments[i] = ZExtExpr::create(listener->arguments[i], to);
                }
              }
            }
            i++;
          }
        }
        if (func->isDeclaration()) {
          switch (func->getIntrinsicID()) {
            case Intrinsic::not_intrinsic: {
              break;
            }
            case Intrinsic::vastart: {
              StackFrame &sf = state.currentStack->realStack.back();
              Expr::Width WordSize = Context::get().getPointerWidth();
              if (WordSize == Expr::Int32) {
                executor->executeMemoryOperation(state, true, listener->arguments[0], sf.varargs->getBaseExpr(), 0);
              } else {
                // gp_offset
                executor->executeMemoryOperation(state, true, listener->arguments[0], ConstantExpr::create(48, 32), 0);
                // fp_offset
                executor->executeMemoryOperation(state, true,
                                                 AddExpr::create(listener->arguments[0], ConstantExpr::create(4, 64)),
                                                 ConstantExpr::create(304, 32), 0);
                // overflow_arg_area
                executor->executeMemoryOperation(state, true,
                                                 AddExpr::create(listener->arguments[0], ConstantExpr::create(8, 64)),
                                                 sf.varargs->getBaseExpr(), 0);
                // reg_save_area
                executor->executeMemoryOperation(state, true,
                                                 AddExpr::create(listener->arguments[0], ConstantExpr::create(16, 64)),
                                                 ConstantExpr::create(0, 64), 0);
              }
              break;
            }
            default:
              break;
          }
        }
        state.currentStack = state.currentThread->stack;
      }
      break;
    }

    case Instruction::Alloca: {
      break;
    }
    case Instruction::Br: {
      break;
    }
    case Instruction::Switch: {
      break;
    }

    default: {
      for (auto bit : bitcodeListeners) {
        state.currentStack = bit->stack[state.currentThread->threadId];
        executor->executeInstruction(state, ki);
        state.currentStack = state.currentThread->stack;
      }
      break;
    }
  }
}

void ListenerService::afterExecuteInstruction(Executor *executor, ExecutionState &state, KInstruction *ki) {
  Instruction *i = ki->inst;
  switch (i->getOpcode()) {
    case Instruction::Ret: {
      for (auto bit : bitcodeListeners) {
        state.currentStack = bit->stack[state.currentThread->threadId];
        ReturnInst *ri = cast<ReturnInst>(i);
        KInstIterator kcaller = state.currentStack->realStack.back().caller;
        Instruction *caller = kcaller ? kcaller->inst : 0;
        bool isVoidReturn = (ri->getNumOperands() == 0);
        ref<Expr> result = ConstantExpr::alloc(0, Expr::Bool);
        if (!isVoidReturn) {
          result = executor->eval(ki, 0, state).value;
        }
        if (state.currentStack->realStack.size() <= 1) {

        } else {
          state.currentStack->popFrame();
          if (!isVoidReturn) {
            Type *t = caller->getType();
            if (t != Type::getVoidTy(i->getContext())) {
              Expr::Width from = result->getWidth();
              Expr::Width to = executor->getWidthForLLVMType(t);
              if (from != to) {
                CallSite cs =
                    (isa<InvokeInst>(caller) ? CallSite(cast<InvokeInst>(caller)) : CallSite(cast<CallInst>(caller)));
                bool isSExt = cs.paramHasAttr(0, llvm::Attribute::SExt);
                if (isSExt) {
                  result = SExtExpr::create(result, to);
                } else {
                  result = ZExtExpr::create(result, to);
                }
              }
              executor->bindLocal(kcaller, state, result);
            }
          }
          state.currentStack = state.currentThread->stack;
        }
      }
      break;
    }

    case Instruction::Invoke:
    case Instruction::Call: {
      for (auto bit : bitcodeListeners) {
        state.currentStack = bit->stack[state.currentThread->threadId];
        CallSite cs(i);
        Value *fp = cs.getCalledValue();
        Function *f = executor->getTargetFunction(fp, state);
        if (f) {
          if (f && f->isDeclaration()) {
            switch (f->getIntrinsicID()) {
              case Intrinsic::not_intrinsic:

                if (f->getName().str() == "pthread_create") {
                  CallInst *calli = dyn_cast<CallInst>(ki->inst);
                  Value *threadEntranceFP = calli->getArgOperand(2);
                  Function *threadEntrance = executor->getTargetFunction(threadEntranceFP, state);
                  if (!threadEntrance) {
                    ref<Expr> param = executor->eval(ki, 3, state).value;
                    ConstantExpr *functionPtr = dyn_cast<ConstantExpr>(param);
                    threadEntrance = (Function *)(functionPtr->getZExtValue());
                  }
                  KFunction *kthreadEntrance = executor->kmodule->functionMap[threadEntrance];
                  PointerType *pointerType = (PointerType *)(calli->getArgOperand(0)->getType());
                  IntegerType *elementType = (IntegerType *)(pointerType->getElementType());
                  Expr::Width type = elementType->getBitWidth();
                  ref<Expr> address = bit->arguments[0];
                  ObjectPair op;
                  bool success = executor->getMemoryObject(op, state, state.currentThread->addressSpace, address);
                  if (success) {
                    const MemoryObject *mo = op.first;
                    ref<Expr> offset = mo->getOffsetExpr(address);
                    const ObjectState *os = op.second;
                    ref<Expr> threadID = os->read(offset, type);
                    executor->executeMemoryOperation(state, true, address, threadID, 0);
                    executor->bindLocal(ki, state, ConstantExpr::create(0, Expr::Int32));

                    StackType *stack = new StackType(&(bit->addressSpace));
                    bit->stack[dyn_cast<ConstantExpr>(threadID)->getAPValue().getSExtValue()] = stack;
                    stack->realStack.reserve(10);
                    stack->pushFrame(0, kthreadEntrance);
                    state.currentStack = stack;
                    executor->bindArgument(kthreadEntrance, 0, state, bit->arguments[3]);
#if DEBUG_RUNTIME_LISTENER
                    llvm::errs() << "bit->arguments[3] : " << bit->arguments[3] << "\n";
#endif
                    state.currentStack = bit->stack[state.currentThread->threadId];
                  }

                } else if (f->getName().str() == "malloc" || f->getName().str() == "_ZdaPv" ||
                           f->getName().str() == "_Znaj" || f->getName().str() == "_Znam" ||
                           f->getName().str() == "valloc") {
                  ref<Expr> size = bit->arguments[0];
                  bool isLocal = false;
                  size = executor->toUnique(state, size);
                  if (dyn_cast<ConstantExpr>(size)) {
                    ref<Expr> addr = state.currentThread->stack->realStack.back().locals[ki->dest].value;
                    ObjectPair op;
                    bool success = executor->getMemoryObject(op, state, state.currentThread->addressSpace, addr);
                    if (success) {
                      const MemoryObject *mo = op.first;
#if DEBUG_RUNTIME_LISTENER
                      llvm::errs() << "mo address : " << mo->address << " mo size : " << mo->size << "\n";
#endif
                      ObjectState *os = executor->bindObjectInState(state, mo, isLocal);
                      os->initializeToRandom();
                      executor->bindLocal(ki, state, mo->getBaseExpr());
                    } else {
                      executor->bindLocal(ki, state, ConstantExpr::alloc(0, Context::get().getPointerWidth()));
                    }
                  }
                } else if (f->getName().str() == "_ZdlPv" || f->getName().str() == "_Znwj" ||
                           f->getName().str() == "_Znwm" || f->getName().str() == "free") {
                  ref<Expr> address = bit->arguments[0];
                  // llvm::errs() << "address: " << address << "\n ";
                  Executor::StatePair zeroPointer = executor->fork(state, Expr::createIsZero(address), true);
                  if (zeroPointer.first) {
                    if (ki)
                      executor->bindLocal(ki, *zeroPointer.first, Expr::createPointer(0));
                  }
                  if (zeroPointer.second) { // address != 0
                    Executor::ExactResolutionList rl;
                    executor->resolveExact(*zeroPointer.second, address, rl, "free");
                    for (Executor::ExactResolutionList::iterator it = rl.begin(), ie = rl.end(); it != ie; ++it) {
                      const MemoryObject *mo = it->first.first;
                      if (mo->isLocal) {
                        executor->terminateStateOnError(*it->second, "free of alloca", Executor::Unhandled, "free.err",
                                                        executor->getAddressInfo(*it->second, address));
                      } else if (mo->isGlobal) {
                        executor->terminateStateOnError(*it->second, "free of global", Executor::Unhandled, "free.err",
                                                        executor->getAddressInfo(*it->second, address));
                      } else {
                        it->second->currentStack->addressSpace->unbindObject(mo);
                        if (ki)
                          executor->bindLocal(ki, *it->second, Expr::createPointer(0));
                      }
                    }
                  }
                } else if (f->getName().str() == "calloc") {
                  ref<Expr> size = MulExpr::create(bit->arguments[0], bit->arguments[1]);
                  bool isLocal = false;
                  size = executor->toUnique(state, size);
                  if (dyn_cast<ConstantExpr>(size)) {
                    ref<Expr> addr = state.currentThread->stack->realStack.back().locals[ki->dest].value;
                    // llvm::errs() << "calloc address : "; addr->dump();
                    ObjectPair op;
                    bool success = executor->getMemoryObject(op, state, state.currentThread->addressSpace, addr);
                    if (success) {
                      const MemoryObject *mo = op.first;
                      // llvm::errs() << "calloc address ; " << mo->address << " calloc size : " << mo->size << "\n";
                      ObjectState *os = executor->bindObjectInState(state, mo, isLocal);
                      os->initializeToRandom();
                      executor->bindLocal(ki, state, mo->getBaseExpr());
                    } else {
                      executor->bindLocal(ki, state, ConstantExpr::alloc(0, Context::get().getPointerWidth()));
                    }
                  }
                } else if (f->getName().str() == "realloc") {
                  assert(0 && "realloc");
                } else {
                  //										(*bit)->addressSpace.copyInConcretes();
                  Type *resultType = ki->inst->getType();
                  if (resultType != Type::getVoidTy(i->getContext())) {
                    ref<Expr> e = state.currentThread->stack->realStack.back().locals[ki->dest].value;
                    executor->bindLocal(ki, state, e);
                  }
                }
                break;
              case Intrinsic::vastart: {
                break;
              }
              default:
                break;
            }
          } else {
            KFunction *kf = executor->kmodule->functionMap[f];
            state.currentStack->pushFrame(state.currentThread->prevPC, kf);
            unsigned callingArgs = bit->arguments.size();
            unsigned funcArgs = f->arg_size();
            if (f->isVarArg()) {
              Expr::Width WordSize = Context::get().getPointerWidth();
              StackFrame &sf = state.currentStack->realStack.back();
              MemoryObject *mo = sf.varargs = state.currentThread->stack->realStack.back().varargs;
              ObjectState *os = executor->bindObjectInState(state, mo, true);
              unsigned offset = 0;
              for (unsigned i = funcArgs; i < callingArgs; i++) {
                if (WordSize == Expr::Int32) {
                  os->write(offset, bit->arguments[i]);
                  offset += Expr::getMinBytesForWidth(bit->arguments[i]->getWidth());
                } else {
                  Expr::Width argWidth = bit->arguments[i]->getWidth();
                  if (argWidth > Expr::Int64) {
                    offset = llvm::alignOf(offset, 16);
                  }
                  os->write(offset, bit->arguments[i]);
                  offset += llvm::alignOf(argWidth, WordSize) / 8;
                }
              }
            }
            unsigned numFormals = f->arg_size();
            for (unsigned i = 0; i < numFormals; ++i) {
              executor->bindArgument(kf, i, state, bit->arguments[i]);
            }
          }
        } else {
          assert(0 && "listenerSercive execute call");
        }
        bit->arguments.clear();
        state.currentStack = state.currentThread->stack;
      }
      break;
    }

    case Instruction::Alloca: {
      AllocaInst *ai = cast<AllocaInst>(i);
      unsigned elementSize = executor->kmodule->targetData->getTypeStoreSize(ai->getAllocatedType());
      ref<Expr> size = Expr::createPointer(elementSize);
      if (ai->isArrayAllocation()) {
        ref<Expr> count = executor->eval(ki, 0, state).value;
        count = Expr::createZExtToPointerWidth(count);
        size = MulExpr::create(size, count);
      }
      bool isLocal = true;
      size = executor->toUnique(state, size);
      if (dyn_cast<ConstantExpr>(size)) {
        ref<Expr> addr = executor->getDestCell(state, ki).value;
        //					llvm::errs() << "alloc address : ";
        //					addr->dump();
        ObjectPair op;
        bool success = executor->getMemoryObject(op, state, state.currentThread->addressSpace, addr);
        if (success) {
          const MemoryObject *mo = op.first;
          //						llvm::errs() << "alloc address ; " << mo->address << " alloc size
          //:
          //"
          //<< mo->size << "\n";
          for (auto bit : bitcodeListeners) {
            state.currentStack = bit->stack[state.currentThread->threadId];
            ObjectState *os = executor->bindObjectInState(state, mo, isLocal);
            os->initializeToRandom();
            executor->bindLocal(ki, state, mo->getBaseExpr());
            state.currentStack = state.currentThread->stack;
          }
        } else {
          for (auto bit : bitcodeListeners) {
            state.currentStack = bit->stack[state.currentThread->threadId];
            executor->bindLocal(ki, state, ConstantExpr::alloc(0, Context::get().getPointerWidth()));
            state.currentStack = state.currentThread->stack;
          }
        }
      }
      break;
    }

    case Instruction::Br: {
      break;
    }
    case Instruction::Switch: {
      break;
    }

    default: {
      break;
    }
  }

  for (auto bit : bitcodeListeners) {
    state.currentStack = bit->stack[state.currentThread->threadId];
    bit->afterExecuteInstruction(state, ki);
    state.currentStack = state.currentThread->stack;
  }
}

void ListenerService::afterRunMethodAsMain(ExecutionState &state) {
  for (auto bit : bitcodeListeners) {
    bit->afterRunMethodAsMain(state);
  }
}

void ListenerService::executionFailed(ExecutionState &state, KInstruction *ki) {
  rdManager->getCurrentTrace()->traceType = Trace::FAILED;
}

void ListenerService::startControl(Executor *executor) {
  executor->executionNum++;

  BitcodeListener *PSOlistener = new PSOListener(executor, rdManager);
  pushListener(PSOlistener);
  BitcodeListener *Symboliclistener = new SymbolicListener(executor, rdManager);
  pushListener(Symboliclistener);
#if DO_DSTAM
  BitcodeListener *Taintlistener = new TaintListener(executor, rdManager);
  pushListener(Taintlistener);
#endif

  unsigned traceNum = executor->executionNum;
  if (traceNum == 1) {
    kleem_execution("%dth execution, initial run, id: Trace%d.", traceNum, traceNum);
  } else {
    kleem_execution("%dth execution, prefix-guided execution, prefix is %s.", traceNum,
                    executor->prefix->getName().c_str());
  }
  gettimeofday(&start, NULL);
}

void ListenerService::taintAnalysis() {
  gettimeofday(&start, NULL);
  dtam = new DTAM(rdManager);
  dtam->work();
  gettimeofday(&finish, NULL);
  cost = (double)(finish.tv_sec * 1000000UL + finish.tv_usec - start.tv_sec * 1000000UL - start.tv_usec) / 1000000UL;
  rdManager->DTAMCost += cost;
  rdManager->allDTAMCost.push_back(cost);

  gettimeofday(&start, NULL);
  encoder->symbolicTaintAnalysis();
  gettimeofday(&finish, NULL);
  cost = (double)(finish.tv_sec * 1000000UL + finish.tv_usec - start.tv_sec * 1000000UL - start.tv_usec) / 1000000UL;
  rdManager->PTSCost += cost;
  rdManager->allPTSCost.push_back(cost);

  Trace *trace = rdManager->getCurrentTrace();
  int size = trace->Send_Data_Expr.size();
  rdManager->Send_Data.push_back(size);
  size = 0;
  for (auto send : trace->Send_Data_Expr) {
    if (trace->DTAMSerial.find(send) != trace->DTAMSerial.end()) {
      size++;
    }
  }
  rdManager->Send_Data_Serial.push_back(size);
  for (auto send : trace->Send_Data_Expr) {
    for (auto pts : trace->taintPTS) {
      if (pts == send) {
        size++;
      }
    }
  }
  rdManager->Send_Data_PTS.push_back(size);

  size = 0;
  for (auto send : trace->Send_Data_Expr) {
    if (trace->DTAMParallel.find(send) != trace->DTAMParallel.end()) {
      size++;
    };
  }
  rdManager->Send_Data_Parallel.push_back(size);

  size = 0;
  for (auto send : trace->Send_Data_Expr) {
    if (trace->DTAMhybrid.find(send) != trace->DTAMhybrid.end()) {
      size++;
    };
  }
  rdManager->Send_Data_Hybrid.push_back(size);
}

void ListenerService::endControl(Executor *executor) {
  if (executor->execStatus != Executor::SUCCESS) {
    kleem_execution("Failed to execute, abandon this execution.");
    // executor->isFinished = true;
    return;
  }
  if (!rdManager->isCurrentTraceUntested()) {
    rdManager->getCurrentTrace()->traceType = Trace::REDUNDANT;
    kleem_execution("Found a old path.");
  } else {
    kleem_execution("Found a new path, id: Trace%d.", rdManager->getCurrentTrace()->Id);
    rdManager->getCurrentTrace()->traceType = Trace::UNIQUE;
    Trace *trace = rdManager->getCurrentTrace();

    unsigned allGlobal = 0;
    for (auto read : trace->readSet) {
      allGlobal += read.second.size();
    }
    for (auto write : trace->writeSet) {
      std::string varName = write.first;
      if (trace->readSet.find(varName) == trace->readSet.end()) {
        allGlobal += write.second.size();
      }
    }
    rdManager->allGlobal += allGlobal;

    gettimeofday(&finish, NULL);
    cost = (double)(finish.tv_sec * 1000000UL + finish.tv_usec - start.tv_sec * 1000000UL - start.tv_usec) / 1000000UL;
    rdManager->runningCost += cost;
    rdManager->allDTAMSerialCost.push_back(cost);

    gettimeofday(&start, NULL);
    encoder = new Encode(rdManager, executor->getHandlerPtr());
    encoder->constraintEncoding();
#if PRINT_DETAILED_TRACE
    printCurrentTrace(false);
#endif
    encoder->flipIfBranches();
    gettimeofday(&finish, NULL);
    cost = (double)(finish.tv_sec * 1000000UL + finish.tv_usec - start.tv_sec * 1000000UL - start.tv_usec) / 1000000UL;
    rdManager->solvingCost += cost;

#if DO_ASSERT_VERIFICATION
    kleem_verifyassert("Verify the assertions on current trace.");
    encoder->verifyAssertion();
    kleem_verifyassert("Assertion verification is over.");
#endif

#if DO_DSTAM
    kleem_dstam("Carry on taint analysis on current trace.");
    taintAnalysis();
    kleem_dstam("Taint analysis is over.");
#endif
  }

  while(!bitcodeListeners.empty()) {
    bitcodeListeners.pop_back();
  }
}

// file--true: output to file; file--false: output to terminal
void ListenerService::printCurrentTrace(bool toFile) {
  auto trace = rdManager->getCurrentTrace();
  kleem_debug("Display trace details.");
  if (toFile) {
    stringstream filename;
    filename << "trace_" << trace->Id << ".data";
    auto os = interpreterHandler->openKleemOutputFile(filename.str());
    assert(os && "Failed to create file.");
    trace->printExecutionTrace(*os);
    trace->printDetailedInfo(*os);
    os->flush();
  } else {
    trace->printExecutionTrace(llvm::errs());
    trace->printDetailedInfo(llvm::errs());
  }
  kleem_debug("Trace infomation is over.");
}

} // namespace klee

#endif
