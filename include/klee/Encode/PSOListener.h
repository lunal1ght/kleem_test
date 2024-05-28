//===-- PSOListener.h --------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef PSOLISTENER_H_
#define PSOLISTENER_H_

#include <map>
#include <sstream>
#include <string>

#include "klee/Config/Version.h"

#include "/tmp/klee_src/lib/Core/AddressSpace.h"
#include "/tmp/klee_src/lib/Core/ExecutionState.h"
#include "/tmp/klee_src/lib/Core/Executor.h"
#include "klee/ADT/Ref.h"
#include "klee/Encode/BarrierInfo.h"
#include "klee/Encode/BitcodeListener.h"
#include "klee/Encode/RuntimeDataManager.h"
#include "klee/Expr/Expr.h"
#include "klee/Thread/StackType.h"

namespace klee {
class RuntimeDataManager;
} /* namespace klee */

namespace llvm {
class Constant;
class ConstantExpr;
class Function;
} /* namespace llvm */

#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Type.h"

namespace klee {

class PSOListener : public BitcodeListener {
public:
  PSOListener(Executor *executor, RuntimeDataManager *rdManager);
  virtual ~PSOListener();

  void beforeRunMethodAsMain(ExecutionState &initialState);
  void beforeExecuteInstruction(ExecutionState &state, KInstruction *ki);
  void afterExecuteInstruction(ExecutionState &state, KInstruction *ki);
  void afterRunMethodAsMain(ExecutionState &state);
  void executionFailed(ExecutionState &state, KInstruction *ki);

private:
  Executor *executor;
  Event *currentEvent;

  std::stringstream ss;
  std::map<uint64_t, unsigned> loadRecord;
  std::map<uint64_t, unsigned> storeRecord;
  std::map<uint64_t, llvm::Type *> usedGlobalVariableRecord;
  std::map<uint64_t, BarrierInfo *> barrierRecord;

private:
  void handleInitializer(llvm::Constant *initializer, MemoryObject *mo, uint64_t &startAddress);
  void handleConstantExpr(llvm::ConstantExpr *expr);
  void insertGlobalVariable(ref<Expr> address, llvm::Type *type);
  ref<Expr> getExprFromMemory(ref<Expr> address, ObjectPair &op, llvm::Type *type);
  llvm::Constant *handleFunctionReturnValue(ExecutionState &state, KInstruction *ki);
  void handleExternalFunction(ExecutionState &state, KInstruction *ki);
  void analyzeInputValue(uint64_t &address, ObjectPair &op, llvm::Type *type);
  unsigned getLoadTimes(uint64_t address);
  unsigned getLoadTimeForTaint(uint64_t address);
  unsigned getStoreTime(uint64_t address);
  unsigned getStoreTimeForTaint(uint64_t address);
  llvm::Function *getPointeredFunction(ExecutionState &state, KInstruction *ki);
  std::string createGlobalVarFullName(std::string varName, unsigned time, bool isStore);

  std::string createVarName(unsigned memoryId, ref<Expr> address, bool isGlobal) {
    char signal;
    ss.str("");
    if (isGlobal) {
      signal = 'G';
    } else {
      signal = 'L';
    }
    ss << signal;
    ss << memoryId;
    ss << '_';
    ss << address;
    return ss.str();
  }
  std::string createVarName(unsigned memoryId, uint64_t address, bool isGlobal) {
    char signal;
    ss.str("");
    if (isGlobal) {
      signal = 'G';
    } else {
      signal = 'L';
    }
    ss << signal;
    ss << memoryId;
    ss << '_';
    ss << address;
    //				llvm::errs() << "create var name : " << ss.str() << "\n";
    return ss.str();
  }

  std::string createBarrierName(uint64_t address, unsigned releasedCount) {
    ss.str("");
    ss << address;
    ss << "#";
    ss << releasedCount;
    return ss.str();
  }
};

} // namespace klee

#endif /* PSOLISTENER_H_ */
