//===-- SymbolicListener.h --------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#ifndef LIB_CORE_SYMBOLICLISTENER_H_
#define LIB_CORE_SYMBOLICLISTENER_H_

#include "/tmp/klee_src/lib/Core/AddressSpace.h"
#include "/tmp/klee_src/lib/Core/ExecutionState.h"
#include "/tmp/klee_src/lib/Core/Executor.h"
#include "klee/ADT/Ref.h"
#include "klee/Encode/BitcodeListener.h"
#include "klee/Encode/Event.h"
#include "klee/Encode/FilterSymbolicExpr.h"
#include "klee/Encode/RuntimeDataManager.h"
#include "klee/Expr/Expr.h"
#include "klee/Thread/StackType.h"

#include <map>
#include <string>
#include <vector>

namespace llvm {
class Type;
class Constant;
} // namespace llvm

namespace klee {

class SymbolicListener : public BitcodeListener {
public:
  SymbolicListener(Executor *executor, RuntimeDataManager *rdManager);
  virtual ~SymbolicListener();

  void beforeRunMethodAsMain(ExecutionState &initialState);
  void beforeExecuteInstruction(ExecutionState &state, KInstruction *ki);
  void afterExecuteInstruction(ExecutionState &state, KInstruction *ki);
  void afterRunMethodAsMain(ExecutionState &state);
  void executionFailed(ExecutionState &state, KInstruction *ki);

private:
  Executor *executor;
  Event *currentEvent;
  FilterSymbolicExpr filter;

  std::map<std::string, std::vector<unsigned>> assertMap;
  bool kleeBr;

private:
  // add by hy
  ref<Expr> manualMakeSymbolic(ExecutionState &state, std::string name, unsigned size, bool isFloat);
  ref<Expr> readExpr(ExecutionState &state, ref<Expr> address, Expr::Width size);
};

} // namespace klee

#endif /* LIB_CORE_SYMBOLICLISTENER_H_ */
