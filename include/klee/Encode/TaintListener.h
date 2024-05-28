//===-- TaintListener.h -----------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LIB_CORE_TAINTLISTENER_H_
#define LIB_CORE_TAINTLISTENER_H_

#include "/tmp/klee_src/lib/Core/AddressSpace.h"
#include "/tmp/klee_src/lib/Core/ExecutionState.h"
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

class TaintListener : public BitcodeListener {
public:
  TaintListener(Executor *executor, RuntimeDataManager *rdManager);
  virtual ~TaintListener();

  void beforeRunMethodAsMain(ExecutionState &initialState);
  void beforeExecuteInstruction(ExecutionState &state, KInstruction *ki);
  void afterExecuteInstruction(ExecutionState &state, KInstruction *ki);
  void afterRunMethodAsMain(ExecutionState &state);
  void executionFailed(ExecutionState &state, KInstruction *ki);

private:
  Executor *executor;
  Event *currentEvent;
  FilterSymbolicExpr filter;

private:
  // add by hy
  ref<Expr> manualMakeTaintSymbolic(ExecutionState &state, std::string name, unsigned size);
  void manualMakeTaint(ref<Expr> value, bool isTaint);
  ref<Expr> readExpr(ExecutionState &state, ref<Expr> address, Expr::Width size);
};

} // namespace klee

#endif /* LIB_CORE_TAINTLISTENER_H_ */
