//===-- Encode.cpp ----------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include <llvm/ADT/APFloat.h>
#include <llvm/ADT/APInt.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/Value.h>
#include <llvm/Support/Casting.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/raw_ostream.h>

#include <assert.h>
#include <cctype>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <iterator>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <sys/time.h>
#include <vector>

#include "klee/ADT/Ref.h"
#include "klee/Config/DebugMacro.h"
#include "klee/Encode/Encode.h"
#include "klee/Encode/Prefix.h"
#include "klee/Expr/Expr.h"
#include "klee/Module/InstructionInfoTable.h"
#include "klee/Module/KInstruction.h"
#include "klee/Support/ErrorHandling.h"
#include "klee/Support/FileHandling.h"

#define BUFFERSIZE 300
#define BIT_WIDTH 64

using namespace llvm;
using namespace std;
using namespace z3;
namespace klee {

void Encode::encodeTraceToFormulas() {
#if PRINT_FORMULA
  kleem_debug("Display kinds of constaint formulas.");
#endif
  // Prepare
  // level: 0 bitcode; 1 source code; 2 block
  controlGranularity(1);

  buildInitValueFormula(z3_solver);
  buildPathCondition(z3_solver);
  buildMemoryModelFormula(z3_solver);
  buildPartialOrderFormula(z3_solver);
  buildReadWriteFormula(z3_solver);
  buildSynchronizeFormula(z3_solver);
#if CHECK_BUILD
  check_result result;
  try {
    result = z3_solver.check();
    if (result == z3::sat) {
      kleem_note("ncodeTraceToFormulas success.");
    } else {
      kleem_note("ncodeTraceToFormulas fail.");
    }
  } catch (z3::exception &ex) {
    kleem_note("Unexpected error: %s.", ex.msg());
  }
#endif
}

void Encode::buildPTSFormula() {
  buildInitValueFormula(z3_taint_solver);
  buildPathCondition(z3_taint_solver);
  buildReadWriteFormula(z3_taint_solver);

  buildMemoryModelFormula(z3_taint_solver);
  buildPartialOrderFormula(z3_taint_solver);
  buildSynchronizeFormula(z3_taint_solver);

  buildInitTaintFormula(z3_taint_solver);
  buildTaintMatchFormula(z3_taint_solver);
  buildTaintProgatationFormula(z3_taint_solver);
}

// true :: assert can't be violated. false :: assert can be violated.
bool Encode::verifyAssertion() {
  KQuery2Z3 *kq = new KQuery2Z3(z3_ctx);
  unsigned int totalAssertEvent = trace->assertEvent.size();
  unsigned int totalAssertSymbolic = trace->assertSymbolicExpr.size();
  assert(totalAssertEvent == totalAssertSymbolic && "the number of brEvent is not equal to brSymbolic");
  z3::expr res = z3_ctx.bool_val(true);
  for (unsigned int i = 0; i < totalAssertEvent; i++) {
    Event *event = trace->assertEvent[i];
    res = kq->getZ3Expr(trace->assertSymbolicExpr[i]);
    unsigned line = event->inst->info->line;
    if (line != 0)
      assertFormula.push_back(make_pair(event, res));
  }
#if PRINT_ASSERT_INFO
  printAssertionInfo();
#endif
  z3_solver.push(); // backtrack 1
  kleem_verifyassert("The number of assertions: %ld.", assertFormula.size());
  for (unsigned i = 0; i < assertFormula.size(); i++) {
    z3_solver.push(); // backtrack point 2
    encodeTraceToFormulas();

    Event *currAssert = assertFormula[i].first;
    z3_solver.add(!assertFormula[i].second);
    // 发生在当前assert语句之前的assert语句要保证不能failed
    for (unsigned j = 0; j < assertFormula.size(); j++) {
      if (j == i) {
        continue;
      }
      Event *temp = assertFormula[j].first;
      expr currIf = z3_ctx.int_const(currAssert->eventName.c_str());
      expr tempIf = z3_ctx.int_const(temp->eventName.c_str());
      expr constraint = z3_ctx.bool_val(1);
      if (currAssert->threadId == temp->threadId) {
        if (currAssert->eventId > temp->eventId)
          constraint = assertFormula[j].second;
      } else {
        constraint = implies(tempIf < currIf, assertFormula[j].second);
      }
      z3_solver.add(constraint);
    }
    // 发生在当前assert语句之前的if分支要保证不变
    for (unsigned j = 0; j < ifFormula.size(); j++) {
      Event *temp = ifFormula[j].first;
      expr currIf = z3_ctx.int_const(currAssert->eventName.c_str());
      expr tempIf = z3_ctx.int_const(temp->eventName.c_str());
      expr constraint = z3_ctx.bool_val(1);
      if (currAssert->threadId == temp->threadId) {
        if (currAssert->eventId > temp->eventId)
          constraint = ifFormula[j].second;
      } else
        constraint = implies(tempIf < currIf, ifFormula[j].second);
      z3_solver.add(constraint);
    }
    formulaNum = formulaNum + ifFormula.size() - 1;
    check_result result = z3_solver.check();
    solvingTimes++;

    if (result == z3::sat) {
      vector<Event *> vecEvent;
      computePrefix(vecEvent, assertFormula[i].first);
      Prefix *prefix = new Prefix(vecEvent, trace->createThreadPoint, "assert_" + assertFormula[i].first->eventName);
      runtimeData->addToScheduleSet(prefix);
      kleem_verifyassert("Assertion Failure at %s:L%d", assertFormula[i].first->inst->info->file.c_str(),
                         assertFormula[i].first->inst->info->line);
#if PRINT_SOLVING_RESULT
      printPrefixInfo(prefix, assertFormula[i].first);
      printSolvingSolution(prefix, assertFormula[i].second);
#endif
      // Once a assertion is failed, exit the verification.
      return false;
    }
    z3_solver.pop(); // backtrack point 2
#if PRINT_ASSERT_INFO
    stringstream ss;
    ss << "Trace" << trace->Id << "#" << assertFormula[i].first->inst->info->line << "#"
       << assertFormula[i].first->eventName << "#" << assertFormula[i].first->brCondition << "-"
       << !(assertFormula[i].first->brCondition) << "assert_bug";
    kleem_verifyassert("Verify assert %d @%s: %s", i + 1, ss.str().c_str(), solvingInfo(result).c_str());
#endif
  }
  z3_solver.pop(); // backtrack 1
  return true;
}

std::string Encode::solvingInfo(check_result result) {
  std::string ret;
  if (result == z3::sat) {
    ret = "Yes!\n";
  } else if (result == z3::unknown) {
    ret = "Unknown!\n";
  } else if (result == z3::unsat) {
    ret = "No!\n";
  }
  return ret;
}

void Encode::flipIfBranches() {
  kleem_exploration("Start to filp the branches on trace, totally %lu branches.", ifFormula.size());
  for (unsigned i = 0; i < ifFormula.size(); i++) {
    stringstream ss;
    ss << "Trace" << trace->Id << "-L" << ifFormula[i].first->inst->info->line << "-" << ifFormula[i].first->eventName
       << "-" << ifFormula[i].first->brCondition << "-" << !(ifFormula[i].first->brCondition);
    std::string prefixName = ss.str();
    // create a backstracking point
    z3_solver.push();
#if O2
    bool presolve = filter.filterUselessWithSet(trace, trace->brRelatedSymbolicExpr[i]);
#else
    bool presolve = true;
#endif
    if (presolve) {
      Event *curr = ifFormula[i].first;
#if O3
      concretizeReadValue(curr);
#endif
      z3_solver.add(!ifFormula[i].second);
      for (unsigned j = 0; j < ifFormula.size(); j++) {
        if (j == i) {
          continue;
        }
        Event *temp = ifFormula[j].first;
        expr currIf = z3_ctx.int_const(curr->eventName.c_str());
        expr tempIf = z3_ctx.int_const(temp->eventName.c_str());
        expr constraint = z3_ctx.bool_val(1);
        if (curr->threadId == temp->threadId) {
          if (curr->eventId > temp->eventId)
            constraint = ifFormula[j].second;
        } else {
          constraint = implies(tempIf < currIf, ifFormula[j].second);
        }
        z3_solver.add(constraint);
      }
      // statics
      formulaNum = formulaNum + ifFormula.size() - 1;
      struct timeval start, finish;
      gettimeofday(&start, NULL);
      check_result result;
      try {
        result = z3_solver.check();
      } catch (z3::exception &ex) {
        kleem_exploration("Flip branch %s, unexpected solving error: %s", prefixName.c_str(), ex.msg());
        continue;
      }
      gettimeofday(&finish, NULL);
      double cost =
          (double)(finish.tv_sec * 1000000UL + finish.tv_usec - start.tv_sec * 1000000UL - start.tv_usec) / 1000000UL;

      solvingTimes++;
      if (result == z3::sat) {
        vector<Event *> vecEvent;
        computePrefix(vecEvent, ifFormula[i].first);
        Prefix *prefix = new Prefix(vecEvent, trace->createThreadPoint, prefixName);
        runtimeData->addToScheduleSet(prefix);
        runtimeData->satBranch++;
        runtimeData->satCost += cost;
#if PRINT_SOLVING_RESULT
        printPrefixInfo(prefix, ifFormula[i].first);
        printSolvingSolution(prefix, ifFormula[i].second);
#endif
      } else {
        runtimeData->unSatBranchBySolve++;
        runtimeData->unSatCost += cost;
      }

      if (result == z3::sat) {
        kleem_exploration("Flip branch %s, spent %lf(s), Successful.", prefixName.c_str(), cost);
      } else if (result == z3::unsat) {
        kleem_exploration("Flip branch %s, spent %lf(s), Failed.", prefixName.c_str(), cost);
      } else {
        kleem_exploration("Flip branch %s, spent %lf(s), Unknown.", prefixName.c_str(), cost);
      }
    } else {
      runtimeData->unSatBranchByPreSolve++;
    }
    // backstracking
    z3_solver.pop();
  }
}

void Encode::concretizeReadValue(Event *curr) {
  //添加读写的解
  std::set<std::string> &RelatedSymbolicExpr = trace->RelatedSymbolicExpr;
  std::vector<ref<klee::Expr>> &rwSymbolicExpr = trace->rwSymbolicExpr;
  std::string varName;
  unsigned int totalRwExpr = rwFormula.size();
  for (unsigned int j = 0; j < totalRwExpr; j++) {
    varName = filter.getName(rwSymbolicExpr[j]->getKid(1));
    if (RelatedSymbolicExpr.find(varName) == RelatedSymbolicExpr.end()) {
      Event *temp = rwFormula[j].first;
      expr currIf = z3_ctx.int_const(curr->eventName.c_str());
      expr tempIf = z3_ctx.int_const(temp->eventName.c_str());
      expr constraint = z3_ctx.bool_val(1);
      if (curr->threadId == temp->threadId) {
        if (curr->eventId > temp->eventId)
          constraint = rwFormula[j].second;
      } else {
        constraint = implies(tempIf < currIf, rwFormula[j].second);
      }
      z3_solver.add(constraint);
    }
  }
}

void Encode::showInitTrace() {
  stringstream filename;
  filename << "Trace" << trace->Id << ".bitcode";
  auto os = interpreterHandler->openKleemOutputFile(filename.str());
  assert(os && "Failed to create file.");
  // bitcode
  for (unsigned i = 0; i < trace->path.size(); i++) {
    Event *currEvent = trace->path[i];
    if (trace->path[i]->inst->info->line == 0 || trace->path[i]->eventType != Event::NORMAL)
      continue;
    *os << i << "---" << trace->path[i]->threadId << "---" << trace->path[i]->eventName << "---"
        << trace->path[i]->inst->inst->getParent()->getParent()->getName().str() << "---"
        << trace->path[i]->inst->info->line << "---" << trace->path[i]->brCondition << "---";
    trace->path[i]->inst->inst->print(*os);
    if (currEvent->isGlobal) {
      *os << "--" << currEvent->globalName << "=";
      string str = currEvent->globalName;
      if (str == "") {
        *os << "\n";
        continue;
      }
    }
    *os << "\n";
  }
  os->flush();
  // source code
  printSourceLine("source_trace.txt", trace->path);
}

void Encode::symbolicTaintAnalysis() {
  buildPTSFormula();
  for (auto name : trace->DTAMParallel) {
    if (trace->DTAMSerial.find(name) == trace->DTAMSerial.end()) {
      trace->PTS.push_back(name);
    }
  }

  for (std::vector<std::string>::iterator it = trace->PTS.begin(); it != trace->PTS.end();) {
    z3_taint_solver.push();
    std::string varName = (*it) + "_tag";
    expr lhs = z3_ctx.bool_const(varName.c_str());
    expr rhs = z3_ctx.bool_val(true);
    z3_taint_solver.add(lhs == rhs);

    Event *curr = trace->getEvent((*it));
    for (unsigned j = 0; j < ifFormula.size(); j++) {
      Event *temp = ifFormula[j].first;
      expr currIf = z3_ctx.int_const(curr->eventName.c_str());
      expr tempIf = z3_ctx.int_const(temp->eventName.c_str());
      expr constraint = z3_ctx.bool_val(1);
      if (curr->threadId == temp->threadId) {
        if (curr->eventId > temp->eventId) {
          constraint = ifFormula[j].second;
        }
      } else {
        constraint = implies(tempIf < currIf, ifFormula[j].second);
      }
      z3_taint_solver.add(constraint);
    } // for

    check_result result;
    try {
      result = z3_taint_solver.check();
    } catch (z3::exception &ex) {
      kleem_dstam("Unexpected error: %s", ex.msg());
      continue;
    }
    if (result == z3::sat) {
      trace->taintPTS.push_back(*it);
      if (trace->DTAMhybrid.find(*it) == trace->DTAMhybrid.end()) {
        kleem_dstam("taintPTS: %s, DTAMhybrid does not find.", (*it).c_str());
      } else {
        kleem_dstam("taintPTS: %s, DTAMhybrid finds it, getLine: %s", (*it).c_str(), trace->getLine(*it).c_str());
      }
      model m = z3_taint_solver.get_model();
      for (std::vector<std::string>::iterator itt = it; itt != trace->PTS.end();) {
        stringstream ss;
        ss << m.eval(z3_ctx.bool_const((*itt).c_str()));
        long isTaint = atoi(ss.str().c_str());
        if (isTaint != 0) {
          trace->taintPTS.push_back(*itt);
          kleem_dstam("taintPTS: %s.", (*itt).c_str());
          itt = trace->PTS.erase(itt);
        } else {
          itt++;
        }
      }
    } else {
      trace->noTaintPTS.push_back(*it);
      if (trace->DTAMhybrid.find(*it) == trace->DTAMhybrid.end()) {
        kleem_dstam("noTaintPTS: %s, DTAMhybrid does not find.", (*it).c_str());
      } else {
        kleem_dstam("noTaintPTS: %s, DTAMhybrid finds it, getLine: %s", (*it).c_str(), trace->getLine(*it).c_str());
      }
    }
    it = trace->PTS.erase(it);
    z3_taint_solver.pop();
  } // for
  runtimeData->taint.push_back(trace->DTAMSerial.size());
  runtimeData->taintPTS.push_back(trace->taintPTS.size());
  runtimeData->noTaintPTS.push_back(trace->noTaintPTS.size());

  for (auto name : trace->DTAMSerial) {
    runtimeData->allTaintMap.insert(trace->getAssemblyLine(name));
    trace->taintMap.insert(trace->getAssemblyLine(name));
    // std::cerr << "DTAMSerial name : " << *it << " getLine : " << trace->getLine(*it) << "\n";
  }
  for (auto name : trace->taintPTS) {
    runtimeData->allTaintMap.insert(trace->getAssemblyLine(name));
    trace->taintMap.insert(trace->getAssemblyLine(name));
    // std::cerr << "taintPTS name : " << *it << " getLine : " << trace->getLine(*it) << "\n";
  }

  runtimeData->TaintAndPTSMap.push_back(trace->taintMap.size());
}

void Encode::computePrefix(vector<Event *> &vecEvent, Event *ifEvent) {
  vector<pair<int, Event *>> eventOrderPair;
  // get the order of event
  map<string, expr>::iterator it = eventNameInZ3.find(ifEvent->eventName);
  assert(it != eventNameInZ3.end());
  model m = z3_solver.get_model();
  stringstream ss;
  ss << m.eval(it->second);
  long ifEventOrder = atoi(ss.str().c_str());
  for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
    std::vector<Event *> &thread = trace->eventList[tid];
    if (thread.empty())
      continue;
    for (unsigned index = 0, size = thread.size(); index < size; index++) {
      if (thread.at(index)->eventType == Event::VIRTUAL)
        continue;

      it = eventNameInZ3.find(thread.at(index)->eventName);
      assert(it != eventNameInZ3.end());
      stringstream ss;
      ss << m.eval(it->second);
      long order = atoi(ss.str().c_str());
      // cut off segment behind the negated branch
      if (order > ifEventOrder)
        continue;
      if (order == ifEventOrder && thread.at(index)->threadId != ifEvent->threadId)
        continue;
      if (thread.at(index)->eventName == ifEvent->eventName && thread.at(index)->eventId > ifEvent->eventId)
        continue;
      eventOrderPair.push_back(make_pair(order, thread.at(index)));
    }
  }

  // sort all events according to order
  unsigned size = eventOrderPair.size();
  for (unsigned i = 0; i < size - 1; i++) {
    for (unsigned j = 0; j < size - i - 1; j++) {
      if (eventOrderPair[j].first > eventOrderPair[j + 1].first) {
        auto temp = eventOrderPair[j];
        eventOrderPair[j] = eventOrderPair[j + 1];
        eventOrderPair[j + 1] = temp;
      }
    }
  }

  // put the ordered events to vecEvent.
  for (unsigned i = 0; i < eventOrderPair.size(); i++) {
    vecEvent.push_back(eventOrderPair[i].second);
  }
}

void Encode::printAssertionInfo() {
  stringstream fileName;
  fileName << "Trace" << trace->Id << ".z3expr";
  auto out_file = interpreterHandler->openKleemOutputFile(fileName.str());
  assert(out_file && "Failed to create file.");
  *out_file << "\n" << z3_solver << "\n";
  *out_file << "\nifFormula\n";
  for (unsigned i = 0; i < ifFormula.size(); i++) {
    *out_file << "Trace" << trace->Id << "#" << ifFormula[i].first->inst->info->file << "#"
              << ifFormula[i].first->inst->info->line << "#" << ifFormula[i].first->eventName << "#"
              << ifFormula[i].first->brCondition << "-" << !(ifFormula[i].first->brCondition) << "\n";
    stringstream ss;
    ss << ifFormula[i].second;
    *out_file << ss.str() << "\n";
  }
  *out_file << "\nassertFormula\n";
  for (unsigned i = 0; i < assertFormula.size(); i++) {
    *out_file << "Trace" << trace->Id << "#" << assertFormula[i].first->inst->info->file << "#"
              << assertFormula[i].first->inst->info->line << "#" << assertFormula[i].first->eventName << "#"
              << assertFormula[i].first->brCondition << "-" << !(assertFormula[i].first->brCondition) << "\n";
    stringstream ss;
    ss << assertFormula[i].second;
    *out_file << ss.str() << "\n";
  }
  out_file->flush();
}

void Encode::printPrefixInfo(Prefix *prefix, Event *ifEvent) {
  vector<Event *> *orderedEventList = prefix->getEventList();
  unsigned size = orderedEventList->size();
  model m = z3_solver.get_model();
  // print counterexample at bitcode level
  auto os = interpreterHandler->openKleemOutputFile(prefix->getName() + ".bitcode");
  assert(os && "Failed to create file.");
  for (unsigned i = 0; i < size; i++) {
    Event *currEvent = orderedEventList->at(i);
    *os << currEvent->threadId << "---" << currEvent->eventName << "---"
        << currEvent->inst->inst->getParent()->getParent()->getName().str() << "---" << currEvent->inst->info->line
        << "---" << currEvent->brCondition << "---";
    currEvent->inst->inst->print(*os);
    if (currEvent->isGlobal) {
      *os << "--" << currEvent->globalName << "=";
      string str = currEvent->globalName;
      if (str == "") {
        *os << "\n";
        continue;
      }
      stringstream ss;
#if INT_ARITHMETIC
      ss << m.eval(z3_ctx.int_const(str.c_str()));
#else
      ss << m.eval(z3_ctx.bv_const(str.c_str(), BIT_WIDTH)); // just for
#endif
      *os << ss.str();
    }
    *os << "\n";
  }
  os->flush();
}

void Encode::printSolvingSolution(Prefix *prefix, expr ifExpr) {
  stringstream fileName;
  fileName << prefix->getName() << ".z3expr";
  auto out_file = interpreterHandler->openKleemOutputFile(fileName.str());
  assert(out_file && "Failed to create file.");
  stringstream ss;
  ss << !ifExpr;
  *out_file << "!ifFormula[i].second : " << ss.str() << "\n";
  *out_file << "\n" << z3_solver << "\n";
  model m = z3_solver.get_model();
  *out_file << "\nz3_solver.get_model()\n";
  *out_file << "\n" << m << "\n";
  out_file->flush();
}

/// called by showInitTrace to print initial trace
void Encode::printSourceLine(string fileName, vector<Event *> &trace) {
  auto out_to_file = interpreterHandler->openKleemOutputFile(fileName);
  assert(out_to_file && "Failed to create file.");
  *out_to_file << "threadId  "
               << "lineNum   "
               << "function                 "
               << "source"
               << "\n";
  unsigned preThreadId = 0, preCodeLine = 0;
  for (unsigned i = 0, size = trace.size(); i < size; i++) {
    if (trace[i]->eventType != Event::NORMAL)
      continue;
    if (trace[i]->inst->info->line == 0)
      continue;
    unsigned currCodeLine = trace[i]->inst->info->line;
    unsigned currThreadId = trace[i]->threadId;
    if (currThreadId == preThreadId && currCodeLine == preCodeLine)
      continue;
    //		string fileName = trace[i]->codeDir + "/" + trace[i]->codeFile;
    string fileName = trace[i]->inst->info->file;
    string source = readLine(fileName, trace[i]->inst->info->line);
    if (source == "")
      assert(0 && "blank line");
    if (source == "{" || source == "}")
      continue;
    // write to file
    int len;
    stringstream ss;
    ss << currThreadId;
    len = strlen(ss.str().c_str());
    for (int k = 0; k < 10 - len; k++)
      ss << " ";
    ss << currCodeLine;
    len = strlen(ss.str().c_str());
    for (int k = 0; k < 20 - len; k++)
      ss << " ";
    ss << trace[i]->inst->inst->getParent()->getParent()->getName().str();
    len = strlen(ss.str().c_str());
    for (int k = 0; k < 45 - len; k++)
      ss << " ";
    ss << source << "\n";
    *out_to_file << ss.str();

    preThreadId = currThreadId;
    preCodeLine = currCodeLine;
  }
  out_to_file->flush();
}

bool Encode::isAssert(string filename, unsigned line) {
  char source[BUFFERSIZE];
  ifstream ifile(filename.c_str());
  if (!ifile.is_open())
    assert(0 && "open file error");
  unsigned i = 0;
  while (i != line) {
    ifile.getline(source, BUFFERSIZE);
    i += 1;
  }
  ifile.close();
  string s(source);
  return s.find("assert", 0) != string::npos;
}

string Encode::readLine(string filename, unsigned line) {
  char source[BUFFERSIZE];
  ifstream ifile(filename.c_str());
  if (!ifile.is_open()) {
    std::cerr << filename << " line : " << line << "\n";
    assert(0 && "open file error");
  }
  unsigned i = 0;
  while (i != line) {
    ifile.getline(source, BUFFERSIZE);
    i += 1;
  }
  ifile.close();
  return stringTrim(source);
}

string Encode::stringTrim(char *source) {
  string ret;
  char dest[BUFFERSIZE];
  int k = 0;
  int s = 0, e = 0;
  int len = strlen(source);
  for (int i = 0; i < len; i++) {
    if (!isspace(source[i])) {
      s = i;
      break;
    }
  }
  for (int i = (len - 1); i >= 0; i--) {
    if (!isspace(source[i])) {
      e = i;
      break;
    }
  }
  for (int i = s; i <= e; i++) {
    dest[k++] = source[i];
  }
  dest[k] = '\0';
  ret = dest;
  return ret;
}
void Encode::logThreadStatisticsInfo() {
  unsigned threadNumber = 0;
  unsigned instNumber = 0;
  for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
    std::vector<Event *> &thread = trace->eventList[tid];
    if (thread.empty())
      continue;
    threadNumber++;
    instNumber += thread.size();
  }
  unsigned lockNumber = trace->all_lock_unlock.size();
  unsigned lockPairNumber = 0;
  std::map<std::string, std::vector<LockPair *>>::iterator it = trace->all_lock_unlock.begin();
  for (; it != trace->all_lock_unlock.end(); it++) {
    lockPairNumber += it->second.size();
  }
  unsigned signalNumber = trace->all_signal.size();
  unsigned waitNumber = trace->all_wait.size();
  unsigned sharedVarNumber = trace->global_variable_final.size();
  unsigned readNumber = trace->readSet.size();
  unsigned writeNumber = trace->writeSet.size();
  auto out = interpreterHandler->openKleemOutputFile("thread_statistics.txt");
  assert(out && "Failed to create file.");
  *out << "#Threads:" << threadNumber << "\n";
  *out << "#Instructions: " << instNumber << "\n";
  *out << "#Locks: " << lockNumber << "\n";
  *out << "#Lock/Unlock Pairs: " << lockPairNumber << "\n";
  *out << "#Signal/Wait: " << signalNumber << "/" << waitNumber << "\n";
  *out << "#Shared Variables: " << sharedVarNumber << "\n";
  *out << "#Read/Write of shared points: " << readNumber << "/" << writeNumber << "\n";
  out->flush();
}

void Encode::buildInitValueFormula(solver z3_solver_init) {
// for global initializer
#if PRINT_FORMULA
  std::cerr << "\nGlobal var initial value:\n";
  std::cerr << "Number: " << trace->global_variable_initializer.size() << "\n";
#endif
  std::map<std::string, llvm::Constant *>::iterator gvi = trace->global_variable_initializer_RelatedToBranch.begin();

  for (; gvi != trace->global_variable_initializer_RelatedToBranch.end(); gvi++) {
    // bitwidth may introduce bug!!!
    const Type *type = gvi->second->getType();
    const z3::sort varType(llvmTy_to_z3Ty(type));
    string str = gvi->first + "_Init";
    expr lhs = z3_ctx.constant(str.c_str(), varType);
    expr rhs = buildExprForConstantValue(gvi->second, false, "");
    z3_solver_init.add(lhs == rhs);

#if PRINT_FORMULA
    std::cerr << (lhs == rhs) << "\n";
#endif
  }
  // statics
  formulaNum += trace->global_variable_initializer_RelatedToBranch.size();
}

void Encode::buildOutputFormula() {
// for global var at last
// need to choose manually
#if PRINT_FORMULA
  std::cerr << "\nGlobal var final value:\n";
#endif
  std::map<std::string, llvm::Constant *>::iterator gvl = trace->global_variable_final.begin();
  for (; gvl != trace->global_variable_final.end(); gvl++) {
    const Type *type = gvl->second->getType();
    const z3::sort varType(llvmTy_to_z3Ty(type));
    string str = gvl->first + "_Final";
    expr lhs = z3_ctx.constant(str.c_str(), varType);
    expr rhs = buildExprForConstantValue(gvl->second, false, "");
    expr finalValue = (lhs == rhs);
    expr constrait = z3_ctx.bool_val(1);

    vector<Event *> maybeRead;
    map<int, map<string, Event *>>::iterator atlw = allThreadLastWrite.begin();
    for (; atlw != allThreadLastWrite.end(); atlw++) {
      map<string, Event *>::iterator it = atlw->second.find(gvl->first);
      if (it != atlw->second.end()) {
        maybeRead.push_back(it->second);
      }
    }
    if (maybeRead.size() == 0) { // be equal with initial value!
      string str = gvl->first + "_Init";
      expr init = z3_ctx.constant(str.c_str(), varType);
      constrait = (lhs == init);
    } else { // be equal with the last write in some threads
      vector<expr> allReads;
      for (unsigned i = 0; i < maybeRead.size(); i++) {
        // build the equation
        expr write = z3_ctx.constant(maybeRead[i]->globalName.c_str(), varType); // used write event
        expr eq = (lhs == write);
        // build the constrait of equation
        expr writeOrder = z3_ctx.int_const(maybeRead[i]->eventName.c_str());
        vector<expr> beforeRelation;
        for (unsigned j = 0; j < maybeRead.size(); j++) {
          if (j == i)
            continue;
          expr otherWriteOrder = z3_ctx.int_const(maybeRead[j]->eventName.c_str());
          expr temp = (otherWriteOrder < writeOrder);
          beforeRelation.push_back(temp);
        }
        expr tmp = makeExprsAnd(beforeRelation);
        allReads.push_back(eq && tmp);
      }
      constrait = makeExprsOr(allReads);
    }

    pair<expr, expr> temp = make_pair(finalValue, constrait);
#if PRINT_FORMULA
    std::cerr << "\n" << finalValue << "-------" << constrait;
#endif
    globalOutputFormula.push_back(temp);
  }
}

void Encode::markLatestWriteForGlobalVar() {
  for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
    std::vector<Event *> &thread = trace->eventList[tid];
    if (thread.empty())
      continue;
    for (unsigned index = 0; index < thread.size(); index++) {
      Event *event = thread.at(index);
      //			if (event->usefulGlobal) {
      if (event->isGlobal) {
        Instruction *I = event->inst->inst;
        if (StoreInst::classof(I)) { // write
          latestWriteOneThread[event->name] = event;
        } else { // read
          Event *writeEvent;
          map<string, Event *>::iterator it;
          it = latestWriteOneThread.find(event->name);
          if (it != latestWriteOneThread.end()) {
            writeEvent = it->second;
          } else {
            writeEvent = NULL;
          }
          event->latestWriteEventInSameThread = writeEvent;
        }
      }
    }
    // post operations
    allThreadLastWrite[tid] = latestWriteOneThread;
    latestWriteOneThread.clear();
  }
}

void Encode::buildPathCondition(solver z3_solver_pc) {
#if PRINT_FORMULA
  std::cerr << "\nPath Condition:\n";
#endif

  KQuery2Z3 *kq = new KQuery2Z3(z3_ctx);
  unsigned int totalExpr = trace->pathConditionRelatedToBranch.size();
  for (unsigned int i = 0; i < totalExpr; i++) {
    z3::expr temp = kq->getZ3Expr(trace->pathConditionRelatedToBranch[i]);
    z3_solver_pc.add(temp);
#if PRINT_FORMULA
    std::cerr << temp << "\n";
#endif
  }
}

void Encode::constraintEncoding() {
  Trace *trace = runtimeData->getCurrentTrace();
#if O1
  filter.filterUnusedExprs(trace);
#endif

  unsigned brGlobal = 0;
  for (auto &itr : trace->readSet) {
    brGlobal += itr.second.size();
  }
  for (auto &itw : trace->writeSet) {
    std::string varName = itw.first;
    if (trace->readSet.find(varName) == trace->readSet.end()) {
      brGlobal += itw.second.size();
    }
  }
  runtimeData->brGlobal += brGlobal;

  KQuery2Z3 *kq = new KQuery2Z3(z3_ctx);
  for (unsigned int i = 0; i < trace->brEvent.size(); i++) {
    Event *event = trace->brEvent[i];
    z3::expr res = kq->getZ3Expr(trace->brSymbolicExpr[i]);
    if (event->isConditionInst == true) {
      ifFormula.push_back(make_pair(event, res));
    } else if (event->isConditionInst == false) {
      z3_solver.add(res);
    }
  }

  for (unsigned int i = 0; i < trace->rwSymbolicExpr.size(); i++) {
    Event *event = trace->rwEvent[i];
    z3::expr res = kq->getZ3Expr(trace->rwSymbolicExpr[i]);
    rwFormula.push_back(make_pair(event, res));
  }
  encodeTraceToFormulas();
}

expr Encode::buildExprForConstantValue(Value *V, bool isLeft, string currInstPrefix) {
  assert(V && "V is null!");
  expr ret = z3_ctx.bool_val(1);
  // llvm type to z3 type, except load and store inst which contain pointer
  const z3::sort varType(llvmTy_to_z3Ty(V->getType()));
  //
  if (ConstantInt *ci = dyn_cast<ConstantInt>(V)) {
    int val = ci->getSExtValue();
    unsigned num_bit = ((IntegerType *)V->getType())->getBitWidth();
    if (num_bit == 1)
      ret = z3_ctx.bool_val(val);
    else
#if INT_ARITHMETIC
      ret = z3_ctx.int_val(val);
#else
      ret = z3_ctx.bv_val(val, BIT_WIDTH);
#endif
  } else if (ConstantFP *cf = dyn_cast<ConstantFP>(V)) {
    double val;
    APFloat apf = cf->getValueAPF();
    const struct llvm::fltSemantics &semantics = apf.getSemantics();
    if (apf.semanticsPrecision(semantics) == 53)
      val = apf.convertToDouble();
    else if (apf.semanticsPrecision(semantics) == 24)
      val = apf.convertToFloat();
    else
      assert(0 && "Wrong with Float Type!");

    //		std::cerr << setiosflags(ios::fixed) << val << "\n";
    char s[200];
    sprintf(s, "%f", val);
    ret = z3_ctx.real_val(s);
  } else if (dyn_cast<ConstantPointerNull>(V)) {
    //%cmp = icmp eq %struct.bounded_buf_tag* %tmp, null
#if INT_ARITHMETIC
    ret = z3_ctx.int_val(0);
#else
    ret = z3_ctx.bv_val(0, BIT_WIDTH);
#endif
  } else if (llvm::ConstantExpr *constantExpr = dyn_cast<llvm::ConstantExpr>(V)) {
    Instruction *inst = constantExpr->getAsInstruction();
    if (IntToPtrInst::classof(inst)) {
      // cmp26 = icmp eq i8* %tmp19, inttoptr (i32 -1 to i8*)
      IntToPtrInst *ptrtoint = dyn_cast<IntToPtrInst>(inst);
      ConstantInt *ci = dyn_cast<ConstantInt>(ptrtoint->getOperand(0));
      assert(ci && "Impossible!");
      int val = ci->getValue().getLimitedValue();
#if INT_ARITHMETIC
      ret = z3_ctx.int_val(val);
#else
      ret = z3_ctx.bv_val(val, BIT_WIDTH); // to pointer, the default is 32bit.
#endif
    } else {
      assert(0 && "unknown type of Value:1");
    }
  } else {
    assert(0 && "unknown type of Value:2");
  }

  return ret;
}

z3::sort Encode::llvmTy_to_z3Ty(const Type *typ) {
  switch (typ->getTypeID()) {
    case Type::VoidTyID:
      assert(0 && "void return value!");
      break;
    case Type::HalfTyID:
    case Type::FloatTyID:
    case Type::DoubleTyID:
      return z3_ctx.real_sort();
    case Type::X86_FP80TyID:
      assert(0 && "couldn't handle X86_FP80 type!");
      break;
    case Type::FP128TyID:
      assert(0 && "couldn't handle FP128 type!");
      break;
    case Type::PPC_FP128TyID:
      assert(0 && "couldn't handle PPC_FP128 type!");
      break;
    case Type::LabelTyID:
      assert(0 && "couldn't handle Label type!");
      break;
    case Type::MetadataTyID:
      assert(0 && "couldn't handle Metadata type!");
      break;
    case Type::X86_MMXTyID:
      assert(0 && "couldn't handle X86_MMX type!");
      break;
    case Type::IntegerTyID: {
      unsigned num_bit = ((IntegerType *)typ)->getBitWidth();
      if (num_bit == 1) {
        return z3_ctx.bool_sort();
        ;
      } else {
#if INT_ARITHMETIC
        return z3_ctx.int_sort();
#else
        return z3_ctx.bv_sort(BIT_WIDTH);
#endif
      }
      break;
    }
    case Type::FunctionTyID:
      assert(0 && "couldn't handle Function type!");
      break;
    case Type::StructTyID:
#if INT_ARITHMETIC
      return z3_ctx.int_sort();
#else
      return z3_ctx.bv_sort(BIT_WIDTH);
#endif
      break;
    case Type::ArrayTyID:
      assert(0 && "couldn't handle Array type!"); // must
      break;
    case Type::PointerTyID:
#if INT_ARITHMETIC
      return z3_ctx.int_sort();
#else
      return z3_ctx.bv_sort(BIT_WIDTH);
#endif
    case Type::FixedVectorTyID:
      assert(0 && "couldn't handle Vector type!");
      break;
    default:
      assert(0 && "No such type!");
      break;
  }
#if INT_ARITHMETIC
      return z3_ctx.int_sort();
#else
      return z3_ctx.bv_sort(BIT_WIDTH);
#endif
    case Type::ScalableVectorTyID:
      assert(0 && "couldn't handle Vector type!");
      break;
    default:
      assert(0 && "No such type!");
      break;
  }
#if INT_ARITHMETIC
  return z3_ctx.int_sort();
#else
  return z3_ctx.bv_sort(BIT_WIDTH);
#endif
} //

void Encode::buildMemoryModelFormula(solver z3_solver_mm) {
#if PRINT_FORMULA
  std::cerr << "\nMemory Model Formula:\n";
#endif
  z3_solver_mm.add(z3_ctx.int_const("E_INIT") == 0);
  // statics
  formulaNum++;
  // initial and final
  for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
    std::vector<Event *> &thread = trace->eventList[tid];
    if (thread.empty())
      continue;
    // initial
    Event *firstEvent = thread.at(0);
    expr init = z3_ctx.int_const("E_INIT");
    expr firstEventExpr = z3_ctx.int_const(firstEvent->eventName.c_str());
    expr temp1 = (init < firstEventExpr);
#if PRINT_FORMULA
    std::cerr << temp1 << "\n";
#endif
    z3_solver_mm.add(temp1);

    // final
    Event *finalEvent = thread.back();
    expr final = z3_ctx.int_const("E_FINAL");
    expr finalEventExpr = z3_ctx.int_const(finalEvent->eventName.c_str());
    expr temp2 = (finalEventExpr < final);
#if PRINT_FORMULA
    std::cerr << temp2 << "\n";
#endif
    z3_solver_mm.add(temp2);
    // statics
    formulaNum += 2;
  }

  // normal events
  int uniqueEvent = 1;
  for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
    std::vector<Event *> &thread = trace->eventList[tid];
    if (thread.empty())
      continue;
    for (unsigned index = 0, size = thread.size(); index < size - 1; index++) {
      Event *pre = thread.at(index);
      Event *post = thread.at(index + 1);
      // by clustering
      if (pre->eventName == post->eventName)
        continue;
      uniqueEvent++;
      expr preExpr = z3_ctx.int_const(pre->eventName.c_str());
      expr postExpr = z3_ctx.int_const(post->eventName.c_str());
      expr temp = (preExpr < postExpr);
#if PRINT_FORMULA
      std::cerr << temp << "\n";
#endif
      z3_solver_mm.add(temp);
      // statics
      formulaNum++;

      // eventNameInZ3 will be used at flipIfBranches
      eventNameInZ3.insert(map<string, expr>::value_type(pre->eventName, preExpr));
      eventNameInZ3.insert(map<string, expr>::value_type(post->eventName, postExpr));
    }
  }
  z3_solver_mm.add(z3_ctx.int_const("E_FINAL") == z3_ctx.int_val(uniqueEvent) + 100);
  // statics
  formulaNum++;
}

// level: 0--bitcode; 1--source code; 2--block
void Encode::controlGranularity(int level) {
  //	map<string, InstType> record;
  if (level == 0)
    return;
  else if (level == 1) {
    for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
      std::vector<Event *> &thread = trace->eventList[tid];
      if (thread.empty())
        continue;
      Event *pre = thread.at(0);
      int preLineNum = pre->inst->info->line;
      InstType preInstType = getInstOpType(thread.at(0));
      string preEventName = thread.at(0)->eventName;

      for (unsigned index = 1, size = thread.size(); index < size; index++) {
        Event *curr = thread.at(index);
        InstType currInstType = getInstOpType(curr);

        // debug
        //				curr->inst->inst->print(std::cerr);
        //				if (currInstType == NormalOp)
        //					std::cerr << "\noptype : NormalOp\n";
        //				else if (currInstType == GlobalVarOp)
        //					std::cerr << "\noptype : GlobalVarOp\n";
        //				else if (currInstType == ThreadOp)
        //					std::cerr << "\noptype : ThreadOp\n";
        //				else
        //					assert(0);

        int currLineNum = thread.at(index)->inst->info->line;

        if (currLineNum == preLineNum) {
          if (preInstType == NormalOp) {
            curr->eventName = preEventName;
            preInstType = currInstType;
          } else {
            if (currInstType == NormalOp) {
              curr->eventName = preEventName;
            } else {
              preInstType = currInstType;
              preEventName = curr->eventName;
            }
          }
        } else {
          preLineNum = currLineNum;
          preInstType = currInstType;
          preEventName = curr->eventName;
        }
      }
    }
  } else {
    for (unsigned tid = 0; tid < trace->eventList.size(); tid++) {
      std::vector<Event *> &thread = trace->eventList[tid];
      if (thread.empty())
        continue;
      Event *pre = thread.at(0);
      InstType preInstType = getInstOpType(pre);
      string preEventName = pre->eventName;

      for (unsigned index = 1, size = thread.size(); index < size; index++) {
        Event *curr = thread.at(index);
        InstType currInstType = getInstOpType(curr);

        // debug
        //				std::cerr << "enent name " << curr->eventName << " inst type : ";
        //				if (currInstType == NormalOp)
        //					std::cerr << "NormalOp!\n";
        //				else if (currInstType == GlobalVarOp)
        //					std::cerr << "GlobalVarOp!\n";
        //				else if (currInstType == ThreadOp)
        //					std::cerr << "ThreadOp!\n";

        if (preInstType == NormalOp) {
          curr->eventName = preEventName;
        } else {
          preEventName = curr->eventName;
        }
        preInstType = currInstType;
      }
    }
  }
}

InstType Encode::getInstOpType(Event *event) {
  if (event->isGlobal) {
    return GlobalVarOp;
  }
  Instruction *I = event->inst->inst;
  //	if (BranchInst::classof(I)) {
  //		BranchInst* brI = dyn_cast<BranchInst>(I);
  //		if (brI->isConditional()) {
  //			return GlobalVarOp; //actually it's a br. just using
  //		}
  //	}
  if (!CallInst::classof(I)) {
    return NormalOp;
  }
  // switch
  //	CallInst* callI = dyn_cast<CallInst>(I);
  //	if (callI->getCalledFunction() == NULL)
  if (event->calledFunction == NULL) {
    return NormalOp;
  }
  // switch
  //	const char* functionName = callI->getCalledFunction()->getName().data();
  const char *functionName = event->calledFunction->getName().data();

  if (strncmp("pthread", functionName, 7) == 0) {
    return ThreadOp;
  }
  return NormalOp;
}

void Encode::buildPartialOrderFormula(solver z3_solver_po) {
#if PRINT_FORMULA
  std::cerr << "\nPartial Order Formula:";
  std::cerr << "\nthread_create:\n";
#endif
  // handle thread_create
  std::map<Event *, uint64_t>::iterator itc = trace->createThreadPoint.begin();
  for (; itc != trace->createThreadPoint.end(); itc++) {
    // the event is at the point of creating thread
    string creatPoint = itc->first->eventName;
    // the event is the first step of created thread
    if (trace->eventList[itc->second].size() != 0) {
      string firstStep = trace->eventList[itc->second].at(0)->eventName;
      expr prev = z3_ctx.int_const(creatPoint.c_str());
      expr back = z3_ctx.int_const(firstStep.c_str());
      expr twoEventOrder = (prev < back);
#if PRINT_FORMULA
      std::cerr << twoEventOrder << "\n";
#endif
      z3_solver_po.add(twoEventOrder);
    }
  }
  // statics
  formulaNum += trace->createThreadPoint.size();
#if PRINT_FORMULA
  std::cerr << "\nthread_join:\n";
#endif
  // handle thread_join
  std::map<Event *, uint64_t>::iterator itj = trace->joinThreadPoint.begin();
  for (; itj != trace->joinThreadPoint.end(); itj++) {
    // the event is at the point of joining thread
    string joinPoint = itj->first->eventName;
    // the event is the last step of joined thread
    string lastStep = trace->eventList[itj->second].back()->eventName;
    expr prev = z3_ctx.int_const(lastStep.c_str());
    expr back = z3_ctx.int_const(joinPoint.c_str());
    expr twoEventOrder = (prev < back);
#if PRINT_FORMULA
    std::cerr << "Jion Point: " << joinPoint << ", ";
    std::cerr << "Last Step: " << lastStep << " => ";
    std::cerr << twoEventOrder << "\n";
#endif
    z3_solver_po.add(twoEventOrder);
  }
  // statics
  formulaNum += trace->joinThreadPoint.size();
}

void Encode::buildReadWriteFormula(solver z3_solver_rw) {
#if PRINT_FORMULA
  std::cerr << "\nRead-Write Formula:\n";
#endif
  // prepare
  markLatestWriteForGlobalVar();
  //	std::cerr << "size : " << trace->readSet.size()<<"\n";
  //	std::cerr << "size : " << trace->writeSet.size()<<"\n";
  map<string, vector<Event *>>::iterator read;
  map<string, vector<Event *>>::iterator write;

  map<string, vector<Event *>>::iterator ir = trace->readSetRelatedToBranch.begin(); // key--variable,
  Event *currentRead;
  Event *currentWrite;
  for (; ir != trace->readSetRelatedToBranch.end(); ir++) {
    map<string, vector<Event *>>::iterator iw = trace->writeSetRelatedToBranch.find(ir->first);
    // maybe use the initial value from Initialization.@2014.4.16
    // if(iw == writeSet.end())
    // continue;
    for (unsigned k = 0; k < ir->second.size(); k++) {
      vector<expr> oneVarAllRead;
      currentRead = ir->second[k];
      expr r = z3_ctx.int_const(currentRead->eventName.c_str());

      // compute the write set that may be used by currentRead;
      vector<Event *> mayBeRead;
      unsigned currentWriteThreadId;
      if (iw != trace->writeSetRelatedToBranch.end()) {
        for (unsigned i = 0; i < iw->second.size(); i++) {
          if (iw->second[i]->threadId == currentRead->threadId)
            continue;
          else
            mayBeRead.push_back(iw->second[i]);
        }
      }
      if (currentRead->latestWriteEventInSameThread != NULL) {
        //					llvm::errs() << "currentRead->latestWriteEventInSameThread : " <<
        // currentRead->latestWriteEventInSameThread->globalName << "\n";
        mayBeRead.push_back(currentRead->latestWriteEventInSameThread);
      } else {
        // if this read don't have the corresponding write, it may use from Initialization operation.
        // so, build the formula constrainting this read uses from Initialization operation

        vector<expr> oneVarOneRead;
        expr equal = z3_ctx.bool_val(1);
        bool flag = readFromInitFormula(currentRead, equal);
        if (flag != false) {
          // statics
          formulaNum++;
          oneVarOneRead.push_back(equal);
          for (unsigned j = 0; j < mayBeRead.size(); j++) {
            currentWrite = mayBeRead[j];
            expr w = z3_ctx.int_const(currentWrite->eventName.c_str());
            expr order = r < w;
            oneVarOneRead.push_back(order);
          }
          // statics
          formulaNum += mayBeRead.size();
          expr readFromInit = makeExprsAnd(oneVarOneRead);
          oneVarAllRead.push_back(readFromInit);
        }
      }
      //

      for (unsigned i = 0; i < mayBeRead.size(); i++) {
        // cause the write operation of every thread is arranged in the executing order
        currentWrite = mayBeRead[i];
        currentWriteThreadId = currentWrite->threadId;
        vector<expr> oneVarOneRead;
        expr equal = readFromWriteFormula(currentRead, currentWrite, ir->first);
        oneVarOneRead.push_back(equal);

        expr w = z3_ctx.int_const(currentWrite->eventName.c_str());
        expr rw = (w < r);
        // statics
        formulaNum += 2;
        //-----optimization-----//
        // the next write in the same thread must be behind this read.
        if (i + 1 <= mayBeRead.size() - 1 && // short-circuit
            mayBeRead[i + 1]->threadId == currentWriteThreadId) {
          expr nextw = z3_ctx.int_const(mayBeRead[i + 1]->eventName.c_str());
          // statics
          formulaNum++;
          rw = (rw && (r < nextw));
        }
        //

        oneVarOneRead.push_back(rw);

        unsigned current = i;
        for (unsigned j = 0; j < mayBeRead.size(); j++) {
          if (current == j || currentWriteThreadId == mayBeRead[j]->threadId)
            continue;
          expr temp = enumerateOrder(currentRead, currentWrite, mayBeRead[j]);
          // statics
          formulaNum += 2;
          oneVarOneRead.push_back(temp);
        }
        // equal if-and-only-if possibleOrder
        expr if_and_only_if = makeExprsAnd(oneVarOneRead);
        oneVarAllRead.push_back(if_and_only_if);
      }

      if (oneVarAllRead.size() > 0) {
        expr oneReadExprs = makeExprsOr(oneVarAllRead);
#if PRINT_FORMULA
        std::cerr << oneReadExprs << "\n";
#endif
        z3_solver_rw.add(oneReadExprs);
      }
    }
  }
}

expr Encode::readFromWriteFormula(Event *read, Event *write, string var) {
  Instruction *I = read->inst->inst;
  const Type *type = I->getType();
  while (type->getTypeID() == Type::PointerTyID) {
    type = type->getPointerElementType();
  }
  // assert(I->getType()->getTypeID() == Type::PointerTyID && "Wrong Type!");
  const z3::sort varType(llvmTy_to_z3Ty(type));
  expr r = z3_ctx.constant(read->globalName.c_str(), varType);
  string writeVarName = "";
  writeVarName = write->globalName;

  expr w = z3_ctx.constant(writeVarName.c_str(), varType);
  return r == w;
}
/**
 * build the formula representing equality to initial value
 */
bool Encode::readFromInitFormula(Event *read, expr &ret) {
  Instruction *I = read->inst->inst;
  const Type *type = I->getType();
  while (type->getTypeID() == Type::PointerTyID) {
    type = type->getPointerElementType();
  }
  const z3::sort varType(llvmTy_to_z3Ty(type));
  expr r = z3_ctx.constant(read->globalName.c_str(), varType);
  string globalVar = read->name;
  std::map<std::string, llvm::Constant *>::iterator tempIt =
      trace->global_variable_initializer_RelatedToBranch.find(globalVar);
  if (tempIt == trace->global_variable_initializer_RelatedToBranch.end())
    return false;
  string str = tempIt->first + "_Init";
  expr w = z3_ctx.constant(str.c_str(), varType);
  ret = r == w;
  return true;
}

expr Encode::taintReadFromWriteFormula(Event *read, Event *write, string var) {

  string strr = read->globalName + "_tag";
  expr r = z3_ctx.bool_const(strr.c_str());
  string writeVarName = "";
  writeVarName = write->globalName;
  string str = writeVarName + "_tag";
  expr w = z3_ctx.bool_const(str.c_str());
  return r == w;
}

bool Encode::taintReadFromInitFormula(Event *read, expr &ret) {

  string strr = read->globalName + "_tag";
  expr r = z3_ctx.bool_const(strr.c_str());
  string globalVar = read->name;
  std::map<std::string, llvm::Constant *>::iterator tempIt = trace->global_variable_initializer.find(globalVar);
  if (tempIt == trace->global_variable_initializer.end())
    return false;
  string str = tempIt->first + "_Init_tag";
  expr w = z3_ctx.bool_const(str.c_str());
  ret = r == w;
  return true;
}

expr Encode::enumerateOrder(Event *read, Event *write, Event *anotherWrite) {
  expr prev = z3_ctx.int_const(write->eventName.c_str());
  expr back = z3_ctx.int_const(read->eventName.c_str());
  expr another = z3_ctx.int_const(anotherWrite->eventName.c_str());
  expr o = another < prev || another > back;
  return o;
}

void Encode::buildSynchronizeFormula(solver z3_solver_sync) {
#if PRINT_FORMULA
  std::cerr << "\nSynchronization Formula:\n";
  std::cerr << "The sum of locks:" << trace->all_lock_unlock.size() << "\n";
#endif

  // lock/unlock
  map<string, vector<LockPair *>>::iterator it = trace->all_lock_unlock.begin();
  for (; it != trace->all_lock_unlock.end(); it++) {
    vector<LockPair *> tempVec = it->second;
    int size = tempVec.size();
    /////////////////////debug/////////////////////////////
    // print out all the read and write insts of global vars.
    if (false) {
      std::cerr << it->first << "\n";
      for (int k = 0; k < size; k++) {
        std::cerr << "#lock#: " << tempVec[k]->lockEvent->eventName;
        std::cerr << "  #unlock#: " << tempVec[k]->unlockEvent->eventName << "\n";
      }
    }
    /////////////////////debug/////////////////////////////
    for (int i = 0; i < size - 1; i++) {
      expr oneLock = z3_ctx.int_const(tempVec[i]->lockEvent->eventName.c_str());
      if (tempVec[i]->unlockEvent == NULL) { // imcomplete lock pair
        continue;
      }
      expr oneUnlock = z3_ctx.int_const(tempVec[i]->unlockEvent->eventName.c_str());
      for (int j = i + 1; j < size; j++) {
        if (tempVec[i]->threadId == tempVec[j]->threadId)
          continue;

        expr twoLock = z3_ctx.int_const(tempVec[j]->lockEvent->eventName.c_str());
        expr twinLockPairOrder = z3_ctx.bool_val(1);
        if (tempVec[j]->unlockEvent == NULL) { // imcomplete lock pair
          twinLockPairOrder = oneUnlock < twoLock;
          // statics
          formulaNum++;
        } else {
          expr twoUnlock = z3_ctx.int_const(tempVec[j]->unlockEvent->eventName.c_str());
          twinLockPairOrder = (oneUnlock < twoLock) || (twoUnlock < oneLock);
          // statics
          formulaNum += 2;
        }
        z3_solver_sync.add(twinLockPairOrder);
#if PRINT_FORMULA
        std::cerr << twinLockPairOrder << "\n";
#endif
      }
    }
  }

// new method
// wait/signal
#if PRINT_FORMULA
  std::cerr << "The sum of wait:" << trace->all_wait.size() << "\n";
  std::cerr << "The sum of signal:" << trace->all_signal.size() << "\n";
#endif
  map<string, vector<Wait_Lock *>>::iterator it_wait = trace->all_wait.begin();
  map<string, vector<Event *>>::iterator it_signal;

  for (; it_wait != trace->all_wait.end(); it_wait++) {
    it_signal = trace->all_signal.find(it_wait->first);
    if (it_signal == trace->all_signal.end())
      assert(0 && "Something wrong with wait/signal data collection!");
    vector<Wait_Lock *> waitSet = it_wait->second;
    string currCond = it_wait->first;
    for (unsigned i = 0; i < waitSet.size(); i++) {
      vector<expr> possibleMap;
      vector<expr> possibleValue;
      expr wait = z3_ctx.int_const(waitSet[i]->wait->eventName.c_str());
      expr lock_wait = z3_ctx.int_const(waitSet[i]->lock_by_wait->eventName.c_str());
      vector<Event *> signalSet = it_signal->second;
      for (unsigned j = 0; j < signalSet.size(); j++) {
        if (waitSet[i]->wait->threadId == signalSet[j]->threadId)
          continue;
        expr signal = z3_ctx.int_const(signalSet[j]->eventName.c_str());
        // Event_wait < Event_signal < lock_wait
        expr exprs_0 = wait < signal && signal < lock_wait;

        // m_w_s = 1
        stringstream ss;
        ss << currCond << "_" << waitSet[i]->wait->eventName << "_" << signalSet[j]->eventName;
        expr map_wait_signal = z3_ctx.int_const(ss.str().c_str());
        expr exprs_1 = (map_wait_signal == 1);
        // range: p_w_s = 0 or p_w_s = 1
        expr exprs_2 = map_wait_signal >= 0 && map_wait_signal <= 1;

        possibleMap.push_back(exprs_0 && exprs_1);
        possibleValue.push_back(exprs_2);
        // statics
        formulaNum += 3;
      }
      expr one_wait = makeExprsOr(possibleMap);
      expr wait_value = makeExprsAnd(possibleValue);
#if PRINT_FORMULA
      std::cerr << one_wait << "\n";
#endif
      z3_solver_sync.add(one_wait);
      z3_solver_sync.add(wait_value);
    }
  }

  // Sigma m_w_s <= 1
  it_signal = trace->all_signal.begin();
  for (; it_signal != trace->all_signal.end(); it_signal++) {
    it_wait = trace->all_wait.find(it_signal->first);
    if (it_wait == trace->all_wait.end())
      continue;
    vector<Event *> signalSet = it_signal->second;
    string currCond = it_signal->first;
    for (unsigned i = 0; i < signalSet.size(); i++) {
      vector<Wait_Lock *> waitSet = it_wait->second;
      string currSignalName = signalSet[i]->eventName;
      vector<expr> mapLabel;
      for (unsigned j = 0; j < waitSet.size(); j++) {
        stringstream ss;
        ss << currCond << "_" << waitSet[j]->wait->eventName << "_" << currSignalName;
        expr map_wait_signal = z3_ctx.int_const(ss.str().c_str());
        mapLabel.push_back(map_wait_signal);
      }
      expr sum = makeExprsSum(mapLabel);
      expr relation = (sum <= 1);
      z3_solver_sync.add(relation);
    }
  }

  // Sigma m_s_w >= 1
  it_wait = trace->all_wait.begin();
  for (; it_wait != trace->all_wait.end(); it_wait++) {
    it_signal = trace->all_signal.find(it_wait->first);
    if (it_signal == trace->all_signal.end())
      continue;
    vector<Wait_Lock *> waitSet = it_wait->second;
    string currCond = it_wait->first;
    for (unsigned i = 0; i < waitSet.size(); i++) {
      vector<Event *> signalSet = it_signal->second;
      string currWaitName = waitSet[i]->wait->eventName;
      vector<expr> mapLabel;
      for (unsigned j = 0; j < signalSet.size(); j++) {
        stringstream ss;
        ss << currCond << "_" << currWaitName << "_" << signalSet[j]->eventName;
        expr map_wait_signal = z3_ctx.int_const(ss.str().c_str());
        mapLabel.push_back(map_wait_signal);
      }
      expr sum = makeExprsSum(mapLabel);
      expr relation = (sum >= 1);
      z3_solver_sync.add(relation);
    }
  }

  // wipe off the w/s matching in the same thread
  it_wait = trace->all_wait.begin();
  for (; it_wait != trace->all_wait.end(); it_wait++) {
    it_signal = trace->all_signal.find(it_wait->first);
    if (it_signal == trace->all_signal.end())
      continue;
    vector<Wait_Lock *> waitSet = it_wait->second;
    string currCond = it_wait->first;
    for (unsigned i = 0; i < waitSet.size(); i++) {
      vector<Event *> signalSet = it_signal->second;
      string currWaitName = waitSet[i]->wait->eventName;
      unsigned currThreadId = waitSet[i]->wait->threadId;
      for (unsigned j = 0; j < signalSet.size(); j++) {
        if (currThreadId == signalSet[j]->threadId) {
          stringstream ss;
          ss << currCond << "_" << currWaitName << "_" << signalSet[j]->eventName;
          expr map_wait_signal = z3_ctx.int_const(ss.str().c_str());
          z3_solver_sync.add(map_wait_signal == 0);
        }
      }
    }
  }

// barrier
#if PRINT_FORMULA
  std::cerr << "The sum of barrier:" << trace->all_barrier.size() << "\n";
#endif
  map<string, vector<Event *>>::iterator it_barrier = trace->all_barrier.begin();
  for (; it_barrier != trace->all_barrier.end(); it_barrier++) {
    vector<Event *> temp = it_barrier->second;
    for (unsigned i = 0; i < temp.size() - 1; i++) {
      if (temp[i]->threadId == temp[i + 1]->threadId)
        assert(0 && "Two barrier event can't be in a same thread!");
      expr exp1 = z3_ctx.int_const(temp[i]->eventName.c_str());
      expr exp2 = z3_ctx.int_const(temp[i + 1]->eventName.c_str());
      expr relation = (exp1 == exp2);

#if PRINT_FORMULA
      std::cerr << relation << "\n";
#endif
      z3_solver_sync.add(relation);
    }
  }
}

expr Encode::makeExprsAnd(vector<expr> exprs) {
  unsigned size = exprs.size();
  if (size == 0)
    return z3_ctx.bool_val(1);
  if (size == 1)
    return exprs[0];
  expr ret = exprs[0];
  for (unsigned i = 1; i < size; i++)
    ret = ret && exprs[i];
  ret.simplify();
  return ret;
}

expr Encode::makeExprsOr(vector<expr> exprs) {
  unsigned size = exprs.size();
  if (size == 0)
    return z3_ctx.bool_val(1);
  if (size == 1)
    return exprs[0];
  expr ret = exprs[0];
  for (unsigned i = 1; i < size; i++)
    ret = ret || exprs[i];
  ret.simplify();
  return ret;
}

expr Encode::makeExprsSum(vector<expr> exprs) {
  unsigned size = exprs.size();
  if (size == 0)
    assert(0 && "Wrong!");
  if (size == 1)
    return exprs[0];
  expr ret = exprs[0];
  for (unsigned i = 1; i < size; i++)
    ret = ret + exprs[i];
  ret.simplify();
  return ret;
}

void Encode::buildInitTaintFormula(solver z3_solver_it) {
#if PRINT_FORMULA
  std::cerr << "Initial Taint Formula\n";
#endif
  std::map<std::string, llvm::Constant *>::iterator gvi = trace->global_variable_initializer.begin();
  for (; gvi != trace->global_variable_initializer.end(); gvi++) {
    string str = gvi->first + "_Init_tag";
    expr lhs = z3_ctx.bool_const(str.c_str());
    expr rhs = z3_ctx.bool_val(false);
    z3_solver_it.add(lhs == rhs);
#if PRINT_FORMULA
    std::cerr << (lhs == rhs) << "\n";
#endif
  }
}

void Encode::buildTaintMatchFormula(solver z3_solver_tm) {
#if PRINT_FORMULA
  std::cerr << "\nTaint Match Formula:\n";
#endif

  map<string, vector<Event *>>::iterator read;
  map<string, vector<Event *>>::iterator write;

  // debug
  // print out all the read and write insts of global vars.
  if (false) {
    read = trace->allReadSet.begin();
    for (; read != trace->allReadSet.end(); read++) {
      std::cerr << "global var read:" << read->first << "\n";
      for (unsigned i = 0; i < read->second.size(); i++) {
        std::cerr << read->second[i]->eventName << "---" << read->second[i]->globalName << "\n";
      }
    }
    write = trace->allWriteSet.begin();
    for (; write != trace->allWriteSet.end(); write++) {
      std::cerr << "global var write:" << write->first << "\n";
      for (unsigned i = 0; i < write->second.size(); i++) {
        std::cerr << write->second[i]->eventName << "---" << write->second[i]->globalName << "\n";
      }
    }
  }

  std::set<std::string> &potentialTaintSymbolicExpr = trace->potentialTaint;

  map<string, vector<Event *>>::iterator ir = trace->allReadSet.begin(); // key--variable,
  Event *currentRead;
  Event *currentWrite;
  for (; ir != trace->allReadSet.end(); ir++) {
    if (potentialTaintSymbolicExpr.find(ir->first) != potentialTaintSymbolicExpr.end()) {
      //			std::cerr << "trace->allReadSet : " << ir->first << "\n";
      map<string, vector<Event *>>::iterator iw = trace->allWriteSet.find(ir->first);
      for (unsigned k = 0; k < ir->second.size(); k++) {
        vector<expr> oneVarAllRead;
        currentRead = ir->second[k];
        expr r = z3_ctx.int_const(currentRead->eventName.c_str());
        // compute the write set that may be used by currentRead;
        vector<Event *> mayBeRead;
        unsigned currentWriteThreadId;
        if (iw != trace->allWriteSet.end()) {
          for (unsigned i = 0; i < iw->second.size(); i++) {
            if (iw->second[i]->threadId == currentRead->threadId)
              continue;
            else
              mayBeRead.push_back(iw->second[i]);
          }
        }
        if (currentRead->latestWriteEventInSameThread != NULL) {
          mayBeRead.push_back(currentRead->latestWriteEventInSameThread);
        } else {
          // if this read don't have the corresponding write, it may use from Initialization operation.
          // so, build the formula constrainting this read uses from Initialization operation

          vector<expr> oneVarOneRead;
          expr equal = z3_ctx.bool_val(1);
          bool flag = taintReadFromInitFormula(currentRead, equal);
          if (flag != false) {
            // statics
            formulaNum++;
            oneVarOneRead.push_back(equal);
            for (unsigned j = 0; j < mayBeRead.size(); j++) {
              currentWrite = mayBeRead[j];
              expr w = z3_ctx.int_const(currentWrite->eventName.c_str());
              expr order = r < w;
              oneVarOneRead.push_back(order);
            }
            // statics
            formulaNum += mayBeRead.size();
            expr readFromInit = makeExprsAnd(oneVarOneRead);
            oneVarAllRead.push_back(readFromInit);
          }
        }
        //

        for (unsigned i = 0; i < mayBeRead.size(); i++) {
          // cause the write operation of every thread is arranged in the executing order
          currentWrite = mayBeRead[i];
          currentWriteThreadId = currentWrite->threadId;
          vector<expr> oneVarOneRead;
          expr equal = taintReadFromWriteFormula(currentRead, currentWrite, ir->first);
          oneVarOneRead.push_back(equal);

          expr w = z3_ctx.int_const(currentWrite->eventName.c_str());
          expr rw = (w < r);
          // statics
          formulaNum += 2;
          //-----optimization-----//
          // the next write in the same thread must be behind this read.
          if (i + 1 <= mayBeRead.size() - 1 && // short-circuit
              mayBeRead[i + 1]->threadId == currentWriteThreadId) {
            expr nextw = z3_ctx.int_const(mayBeRead[i + 1]->eventName.c_str());
            // statics
            formulaNum++;
            rw = (rw && (r < nextw));
          }
          oneVarOneRead.push_back(rw);
          unsigned current = i;
          for (unsigned j = 0; j < mayBeRead.size(); j++) {
            if (current == j || currentWriteThreadId == mayBeRead[j]->threadId)
              continue;
            expr temp = enumerateOrder(currentRead, currentWrite, mayBeRead[j]);
            // statics
            formulaNum += 2;
            oneVarOneRead.push_back(temp);
          }
          // equal if-and-only-if possibleOrder
          expr if_and_only_if = makeExprsAnd(oneVarOneRead);
          oneVarAllRead.push_back(if_and_only_if);
        }
        expr oneReadExprs = makeExprsOr(oneVarAllRead);
#if PRINT_FORMULA
        std::cerr << oneReadExprs << "\n";
#endif
        z3_solver_tm.add(oneReadExprs);
      }
    } else {
      // std::cerr << "not find : " << ir->first << "\n";
      for (unsigned k = 0; k < ir->second.size(); k++) {
        std::string varName = ir->second[k]->globalName + "_tag";
        // std::cerr << "varName : " << varName << "\n";
        expr lhs = z3_ctx.bool_const(varName.c_str());
        expr rhs = z3_ctx.bool_val(false);
        z3_solver_tm.add(lhs == rhs);
      }
    }
  }
}

void Encode::buildTaintProgatationFormula(solver z3_solver_tp) {
  std::vector<ref<klee::Expr>> taintExpr = trace->taintExpr;
  std::set<std::string> initTaintSymbolicExpr = trace->initTaintSymbolicExpr;
  for (std::vector<ref<klee::Expr>>::iterator it = taintExpr.begin(), ie = taintExpr.end(); it != ie; it++) {
    ref<klee::Expr> value = *it;
    // std::cerr << "value : " << value << "\n";
    ref<klee::Expr> right = value->getKid(1);
    std::string varName = filter.getGlobalName(right);
    // std::cerr << "varName : " << varName << "\n";
    std::string varTaintName = varName + "_tag";
    if (initTaintSymbolicExpr.find(varName) != initTaintSymbolicExpr.end()) {
      expr rhs = z3_ctx.bool_const(varTaintName.c_str());
      expr lhs = z3_ctx.bool_val(true);
      // td::cerr << lhs << " = " << rhs << " initTaintSymbolicExpr\n";
      z3_solver_tp.add(lhs == rhs);
    } else {
      ref<klee::Expr> left = value->getKid(0);
      expr rhs = z3_ctx.bool_const(varTaintName.c_str());
      expr lhs = makeOrTaint(left);
      // std::cerr << lhs << " = " << rhs << "\n";
      z3_solver_tp.add(lhs == rhs);
    }
  }
}

expr Encode::makeOrTaint(ref<klee::Expr> value) {
  //	std::cerr << "value->getKind : " << value->getKind() << "\n";
  expr res = z3_ctx.bool_val(false);
  if (value->getKind() == Expr::Concat || value->getKind() == Expr::Read) {

    std::string varName = filter.getGlobalName(value) + "_tag";
    //		std::cerr << "makeOrTaint varName : " << varName << "\n";
    res = z3_ctx.bool_const(varName.c_str());
  } else if (value->getKind() == Expr::Constant) {

  } else {
    unsigned kidsNum = value->getNumKids();
    if (kidsNum == 1) {
      res = makeOrTaint(value->getKid(0));
    } else if (kidsNum == 2) {
      res = (makeOrTaint(value->getKid(0)) || makeOrTaint(value->getKid(1)));
    }
  }
  return res;
}

} // namespace klee
