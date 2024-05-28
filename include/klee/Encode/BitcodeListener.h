//===-- BitcodeListener.h ---------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef BITCODELISTENER_H_
#define BITCODELISTENER_H_

#include "/tmp/klee_src/lib/Core/AddressSpace.h"
#include "/tmp/klee_src/lib/Core/ExecutionState.h"
#include "klee/Encode/RuntimeDataManager.h"
#include "klee/Thread/StackType.h"
#include "klee/Config/DebugMacro.h"

#define BIT_WIDTH 64

namespace klee {

class BitcodeListener {
public:
  enum ListenerKind {
    defaultKind,
    PSOListenerKind,
    SymbolicListenerKind,
    TaintListenerKind,
    InputListenerKind,
    DebugerListenerKind
  };

  BitcodeListener(RuntimeDataManager *rdManager);
  virtual ~BitcodeListener();

  ListenerKind kind;

  RuntimeDataManager *rdManager;

  AddressSpace addressSpace;
  std::map<unsigned, StackType *> stack;

  std::vector<ref<Expr>> arguments;

  virtual void beforeRunMethodAsMain(ExecutionState &state) = 0;
  virtual void beforeExecuteInstruction(ExecutionState &state, KInstruction *ki) = 0;
  virtual void afterExecuteInstruction(ExecutionState &state, KInstruction *ki) = 0;
  virtual void afterRunMethodAsMain(ExecutionState &state) = 0;
  virtual void executionFailed(ExecutionState &state, KInstruction *ki) = 0;
};

} // namespace klee

#endif /* BITCODELISTENER_H_ */
