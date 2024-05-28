//===-- ListenerService.h ---------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LIB_CORE_LISTENERSERVICE_H_
#define LIB_CORE_LISTENERSERVICE_H_

#include <vector>

#include "/tmp/klee_src/lib/Core/ExecutionState.h"
#include "klee/Encode/BitcodeListener.h"
#include "klee/Encode/RuntimeDataManager.h"

namespace klee {
class DTAM;
class Encode;
} /* namespace klee */

namespace klee {

class ListenerService {

private:
  std::vector<BitcodeListener *> bitcodeListeners;
  RuntimeDataManager *rdManager;
  InterpreterHandler *interpreterHandler;
  Encode *encoder;
  DTAM *dtam;
  struct timeval start, finish;
  double cost;

public:
  ListenerService(Executor *executor);
  ~ListenerService();

  void pushListener(BitcodeListener *bitcodeListener);
  void removeListener(BitcodeListener *bitcodeListener);
  void removeListener(BitcodeListener::ListenerKind kind);
  void popListener();

  RuntimeDataManager *getRuntimeDataManager();
  void printCurrentTrace(bool);
  void Preparation();
  void beforeRunMethodAsMain(Executor *executor, ExecutionState &state, llvm::Function *f, MemoryObject *argvMO,
                             std::vector<ref<Expr>> arguments, int argc, char **argv, char **envp);
  void beforeExecuteInstruction(Executor *executor, ExecutionState &state, KInstruction *ki);
  void afterExecuteInstruction(Executor *executor, ExecutionState &state, KInstruction *ki);
  void afterRunMethodAsMain(ExecutionState &state);
  void executionFailed(ExecutionState &state, KInstruction *ki);

  void startControl(Executor *executor);
  void endControl(Executor *executor);

  void taintAnalysis();
};

} // namespace klee

#endif /* LIB_CORE_LISTENERSERVICE_H_ */
