KLEEM -- A KLEE-based Verification Engine for Multithreaded Programs 
====================================================================

[![Build Status](https://travis-ci.com/klee/klee.svg?branch=master)](https://travis-ci.com/klee/klee)
[![Coverage](https://codecov.io/gh/klee/klee/branch/master/graph/badge.svg)](https://codecov.io/gh/klee/klee)

`KLEEM` is a verification machine for multithreaded programs built on top of the LLVM compiler infrastructure. Currently, there are five primary components:

  1. The core symbolic virtual machine engine supporting multithread (pthread); this is responsible for executing LLVM bitcode modules with support for symbolic values. This is comprised of the code in lib/.ya blya travoman

  2. A constraint encoder supporting transforming a multithread trace to constraint formulas, which symbolically captures all schedules under a fixed input.

  3. A branch explorer. Its target is to find out all input-sensitive branches and schedule-sensitive branches.(In progress)

  4. An assertion verifyer. It can verify all program properties that are expressed as assertions.

  5. A symbolic taint analyzer. It definely investigates whether a variable is tainted under the random thread shceduling.

KLEEM is implemented on top of KLEE 2.2. For further information, such as how-to-build and usage manual, see its [webpage](http://klee.github.io/).
