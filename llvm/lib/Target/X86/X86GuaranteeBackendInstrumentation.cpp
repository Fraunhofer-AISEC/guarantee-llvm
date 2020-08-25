//===-- X86GuaranteeBackendInstrumentation.cpp ----------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
// Authors:
//    Benedikt Kopf <benedikt.kopf@aisec.fraunhofer.de>, Fraunhofer AISEC
//
//===----------------------------------------------------------------------===//

#include "X86.h"
#include "X86InstrBuilder.h"
#include "X86InstrInfo.h"
#include "X86MachineFunctionInfo.h"
#include "X86Subtarget.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/ProfileData/SampleProf.h"
#include "llvm/ProfileData/SampleProfReader.h"
#include "llvm/Transforms/IPO/SampleProfile.h"

using namespace llvm;

/* Each ID with most significant bit set is a jump target */
#define JUMP_TARGET_MASK 0x8000000000000000
#define LOW_BYTES        0x00FFFFFFFFFFFFFF

namespace {

    class X86GuaranteeBackendInstrumentation : public llvm::MachineFunctionPass {

    bool runOnMachineFunction(MachineFunction &MF) override;

    public:
        static char ID;
        X86GuaranteeBackendInstrumentation();

        StringRef getPassName() const override {
            return "X86 Guarantee Backend Instrumentation Pass";
        };

    private:

    };
}

char X86GuaranteeBackendInstrumentation::ID = 0;

X86GuaranteeBackendInstrumentation::X86GuaranteeBackendInstrumentation() : MachineFunctionPass(ID) {}

/*
* Function: runOnMachineFunction
*      The function is called on every machine function. This backend pass is part of
*      the instrumentation for guarantee.
*/
bool X86GuaranteeBackendInstrumentation::runOnMachineFunction(MachineFunction &MF)
{
    bool changed = false;
    const X86InstrInfo *TII = MF.getSubtarget<llvm::X86Subtarget>().getInstrInfo();
    uint64_t counter;

    llvm::MDNode *Node = MF.getFunction().getMetadata("guarantee.function.id");
    if (Node) {
        llvm::Value *MetaConst = dyn_cast<ConstantAsMetadata>(Node->getOperand(0))->getValue();
        counter = dyn_cast<ConstantInt>(MetaConst)->getZExtValue();
        /* Initialize the counter with the function ID shifted to the left. Because the function ID
           is unique in the module, this guarantees unique counter values for all trampoline calls
           across different functions. */
        counter = counter << 32;
    } else {
        /* Return if no function ID found */
        return false;
    }

    for (MachineBasicBlock &MBB : MF) {
        MachineBasicBlock::iterator MBBI = MBB.begin();

        while (MBBI != MBB.end()) {
            if (MBBI->isCall() && MBBI->getOpcode() == X86::CALL64r) { /* Indirect calls */
                /* Before the call */
                MachineInstr *MI = dyn_cast_or_null<MachineInstr>(&(*MBBI));
                if (MI) {
                    MachineOperand &MOp = MI->getOperand(0);

                    Register R1 = MOp.getReg();
                    Register R2 = X86::R11;
                    if (R1.id() == X86::R11) {
                        R2 = X86::R10;
                    }

                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::PUSH64r), R1);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::PUSH64r), R2);
                    addRegOffset(BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::LEA64r), R2), X86::RIP, true, 0);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::SUB64rr), R1).addReg(R1).addReg(R2);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::MOV64ri), R2).addImm(LOW_BYTES);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::AND64rr), R1).addReg(R1).addReg(R2);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::MOV64ri), R2).addImm(counter);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::XOR64rr), R2).addReg(R2).addReg(R1);
                    if (R2.id() != X86::R11) {
                        BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::MOV64rr), X86::R11).addReg(R2);
                    }
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::CALL64pcrel32)).addExternalSymbol("trampoline_i", 0);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::POP64r), R2);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::POP64r), R1);
                    counter++;
                    /* After the call */
                    MBBI++;
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::MOV64ri), X86::RDI).addImm(counter | JUMP_TARGET_MASK);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::CALL64pcrel32)).addExternalSymbol("trampoline_ia", 0);

                    counter++;
                    changed = true;
                }
            } else if (MBBI->isBranch() && MBBI->getOpcode() == X86::JMP64r) { /* Indirect branches */
                MachineInstr *MI = dyn_cast_or_null<MachineInstr>(&(*MBBI));
                if (MI) {
                    MachineOperand &MOp = MI->getOperand(0);

                    Register R1 = MOp.getReg();
                    Register R2 = X86::R11;
                    if (R1.id() == X86::R11) {
                        R2 = X86::R10;
                    }

                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::PUSH64r), R1);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::PUSH64r), R2);
                    addRegOffset(BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::LEA64r), R2), X86::RIP, true, 0);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::SUB64rr), R1).addReg(R1).addReg(R2);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::MOV64ri), R2).addImm(LOW_BYTES);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::AND64rr), R1).addReg(R1).addReg(R2);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::MOV64ri), R2).addImm(counter);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::XOR64rr), R2).addReg(R2).addReg(R1);
                    if (R2.id() != X86::R11) {
                        BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::MOV64rr), X86::R11).addReg(R2);
                    }
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::CALL64pcrel32)).addExternalSymbol("trampoline_i", 0);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::POP64r), R2);
                    BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::POP64r), R1);

                    counter++;
                    changed = true;
                }
            } else if (MBBI->isReturn()) { /* Returns */
                addRegOffset(BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::MOV64rm), X86::RDI), X86::RSP, true, 0);
                addRegOffset(BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::LEA64r), X86::RDX), X86::RIP, true, 0);
                BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::SUB64rr), X86::RDI).addReg(X86::RDI).addReg(X86::RDX);
                BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::MOV64ri), X86::RCX).addImm(LOW_BYTES);
                BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::AND64rr), X86::RDI).addReg(X86::RDI).addReg(X86::RCX);
                BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::MOV64ri), X86::RSI).addImm(counter);
                BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::XOR64rr), X86::RDI).addReg(X86::RDI).addReg(X86::RSI);
                /* Push something to preserve stack alignment to 16 bytes before call */
                BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::SUB64ri8), X86::RSP).addReg(X86::RSP).addImm(8);
                BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::CALL64pcrel32)).addExternalSymbol("trampoline_ia", 0);
                BuildMI(MBB, MBBI, MBBI->getDebugLoc(), TII->get(X86::ADD64ri8), X86::RSP).addReg(X86::RSP).addImm(8);

                counter++;
                changed = true;
            }
            MBBI++;
        }
    }

    return changed;
}


FunctionPass *llvm::createX86GuaranteeBackendInstrumentationPass()
{
  return new X86GuaranteeBackendInstrumentation();
}
