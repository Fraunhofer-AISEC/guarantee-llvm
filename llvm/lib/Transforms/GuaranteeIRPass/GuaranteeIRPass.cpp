//===-- GuaranteeIRPass.cpp -----------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// Authors:
//    Benedikt Kopf <benedikt.kopf@aisec.fraunhofer.de>, Fraunhofer AISEC
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/Triple.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/BinaryFormat/MachO.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Comdat.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/ConstantRange.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DerivedUser.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ModuleSummaryIndex.h"
#include "llvm/IR/ModuleSummaryIndexYAML.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Value.h"
#include "llvm/MC/MCSectionMachO.h"
#include "llvm/Pass.h"
#include "llvm/Support/Allocator.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/ScopedPrinter.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"

using namespace llvm;

#define DEBUG_TYPE "guaranteeirpass"

/* Each ID with most significant bit set is a jump target */
#define JUMP_TARGET_MASK 0x8000000000000000

namespace {
  struct GuaranteeIRPass : public ModulePass {
    static char ID; // Pass identification, replacement for typeid
    GuaranteeIRPass() : ModulePass(ID) {}

    /*
     * Function: insertBeforeInstr
     *      Inserts a call to the trampoline with the given ID before the given instruction
     *
     *      Parameters:
     *          M: The module the instruction is inside
     *          BB: The basic block the instruction is inside
     *          I: The instruction which is then directly after the trampoline call
     *          identifier: The ID passed to the trampoline
     */
    void insertBeforeInstr(Module &M, BasicBlock &BB, Instruction *I, uint64_t identifier)
    {
      IRBuilder<> IRB(&BB);
      llvm::Constant *id = ConstantInt::get(Type::getInt64Ty(M.getContext()), identifier, false);
      llvm::DebugLoc DL = BB.getTerminator()->getDebugLoc();

      if (!DL) {
        if (BB.getParent()->getSubprogram()) {
          DL = DILocation::get(M.getContext(), 0, 0, BB.getParent()->getSubprogram());
        } else {
          DL = DebugLoc();
        }
      }

      // Insert call to CFI function
      Function *Callee = M.getFunction("trampoline");
      std::vector<Value *> Args(1, id);
      IRB.SetInsertPoint(I);
      IRB.CreateCall(Callee, Args, None)->setDebugLoc(DL);
    }

    /*
     * Function: insertBeforeBasicBlock
     *      Inserts a call to the trampoline with the given ID at the beginning of the given
     *      basic block
     *
     *      Parameters:
     *          M: The module the basic block is inside
     *          BB: The basic block which should be modified
     *          identifier: The ID passed to the trampoline
     */
    void insertBeforeBasicBlock(Module &M, BasicBlock &BB, uint64_t identifier)
    {
      IRBuilder<> IRB(&BB);
      llvm::Constant *id = ConstantInt::get(Type::getInt64Ty(M.getContext()), identifier, false);
      llvm::DebugLoc DL = BB.getTerminator()->getDebugLoc();

      if (!DL) {
        if (BB.getParent()->getSubprogram()) {
          DL = DILocation::get(M.getContext(), 0, 0, BB.getParent()->getSubprogram());
        } else {
          DL = DebugLoc();
        }
      }

      // Insert call to CFI function
      Function *Callee = M.getFunction("trampoline");
      std::vector<Value *> Args(1, id);
      IRB.SetInsertPoint(&BB, BB.getFirstInsertionPt());
      IRB.CreateCall(Callee, Args, None)->setDebugLoc(DL);
    }

    /*
     * Function: insertAfterBasicBlock
     *      Inserts a call to the trampoline with the given ID at the end of the given
     *      basic block
     *
     *      Parameters:
     *          M: The module the basic block is inside
     *          BB: The basic block which should be modified
     *          identifier: The ID passed to the trampoline
     */
    void insertAfterBasicBlock(Module &M, BasicBlock &BB, uint64_t identifier)
    {
      IRBuilder<> IRB(&BB);
      llvm::Constant *id = ConstantInt::get(Type::getInt64Ty(M.getContext()), identifier, false);
      llvm::DebugLoc DL = BB.getTerminator()->getDebugLoc();

      // Do not insert a trampoline call at end of the basic block if the last instruction is
      // a return. It will be inserted in the backend anyway.
      if (dyn_cast<ReturnInst>(BB.getTerminator())) {
        return;
      }

      // Do not insert a trampoline call at end of the basic block if the last instruction is
      // a call. It will be inserted by the instrumentation of the function calls.
      if (dyn_cast<CallInst>(BB.getTerminator())) {
        return;
      }

      if (!DL) {
        if (BB.getParent()->getSubprogram()) {
          DL = DILocation::get(M.getContext(), 0, 0, BB.getParent()->getSubprogram());
        } else {
          DL = DebugLoc();
        }
      }

      // Insert call to CFI function
      Function *Callee = M.getFunction("trampoline");
      std::vector<Value *> Args(1, id);
      IRB.SetInsertPoint(BB.getTerminator());
      IRB.CreateCall(Callee, Args, None)->setDebugLoc(DL);
    }

    /*
     * Function: runOnModule
     *      The function is called on each module of the compilation unit. This pass is part of
     *      the instrumentation for guarantee.
     */
    bool runOnModule(Module &M) override {
      uint64_t counter = 1;
      uint64_t functionID = 1;

      // Register trampoline function in module
      std::vector<Type*> TrampArg(1, Type::getInt64Ty(M.getContext()));
      FunctionType *FT = FunctionType::get(Type::getVoidTy(M.getContext()), TrampArg, false);
      Function::Create(FT, Function::ExternalLinkage, "trampoline", M);

      for (Function &F : M) {
        /* Each function gets an unique ID to generate unique IDs in the backend */
        llvm::Constant *fncID = ConstantInt::get(Type::getInt64Ty(M.getContext()), functionID, false);
        MDNode *N = MDNode::get(F.getContext(), ConstantAsMetadata::get(fncID));
        F.setMetadata("guarantee.function.id", N);
        functionID++;

        for (BasicBlock &BB : F) {
          /* Before basic block */
          insertBeforeBasicBlock(M, BB, counter | JUMP_TARGET_MASK);
          counter++;

          /* After basic block */
          insertAfterBasicBlock(M, BB, counter);
          counter++;

          /* Handle hardcoded call instructions */
          for (Instruction &I : BB) {
            if (llvm::CallInst *CI = dyn_cast<llvm::CallInst>(&I)) {
              if (CI->getCalledFunction() != NULL && !CI->getCalledFunction()->getName().equals("trampoline")) {
                if (CI->getIntrinsicID() == Intrinsic::not_intrinsic) {
                  /* Before call instruction */
                  insertBeforeInstr(M, BB, &I, counter);
                  counter++;

                  /* After call instruction */
                  insertBeforeInstr(M, BB, I.getNextNode(), counter | JUMP_TARGET_MASK);
                  counter++;
                }
              }
            }
          }
        }
      }
      return true;
    }
  };
}

char GuaranteeIRPass::ID = 0;
static RegisterPass<GuaranteeIRPass> X("guaranteeirpass", "Guarantee IR Pass");
