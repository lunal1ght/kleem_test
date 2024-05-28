//===-- StackType.h ---------------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LIB_THREAD_STACKTYPE_H_
#define LIB_THREAD_STACKTYPE_H_

#include <iostream>
#include <vector>

#include "klee/Module/KInstIterator.h"
#include "klee/Thread/StackFrame.h"
#include "/tmp/klee_src/lib/Core/AddressSpace.h"
#include "klee/Module/KModule.h"

namespace klee {

	class StackType {
		public:
			StackType(AddressSpace *addressSpace);
			StackType(AddressSpace *addressSpace, StackType *stack);
			virtual ~StackType();

			void pushFrame(KInstIterator caller, KFunction *kf);
			void popFrame();
			void dumpStack(llvm::raw_ostream &out, KInstIterator prevPC) const;

		public:
			std::vector<StackFrame> realStack;
			AddressSpace *addressSpace;
	};

} /* namespace klee */

#endif /* LIB_THREAD_STACKTYPE_H_ */
