/*
write a dynamic analysis that computes the branch Ias on a per-function basis: 
    count the number of times conditional branch instructions are executed and the number of times conditional branch instructions are taken. 
    Note that we only consider conditional branches. A conditional branch is considered taken if its condition evaluates to true. 
Each instrumented function should output these two counts before function termination. 
EX
    taken\t[count of taken]\n
    total\t[count of total]\n
*/

// LLVM lib
#include "llvm/Pass.h"
// Function -> BasicBlock -> Iterator
#include "llvm/IR/Function.h"   
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Value.h"

// IRBuilder        #include "llvm/IR/IRBuilder.h”
//     IRBuilder::SetInsertPoint    /// This specifies that created instructions should be appended to the end of the specified block.
//     IRBuilder::CreateCall        /// \brief Create a callbr instruction.
// https://llvm.org/doxygen/IRBuilder_8h_source.html
#include "llvm/IR/IRBuilder.h"

// FunctionType
//     ConstantDataArray::get
//     ArrayType::get
//     IntegerType::get
//     ConstantInt::get
// https://llvm.org/doxygen/Type_8h_source.html
#include "llvm/IR/Type.h"

// Module
//     Module::getOrInsertFunction       /// the returned value is a FunctionCallee wrapper around the 'FunctionType *T' passed in, 
//      as well as a 'Value*' either of the Function or the Itcast to the function.
// https://llvm.org/doxygen/Module_8h_source.html
#include "llvm/IR/Module.h"

// C++ STL
#include <string>
#include <vector>

using namespace llvm;
using namespace std;

namespace {
	struct BranchIas : public FunctionPass {
        static char ID;

        BranchIas() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            /*
                mainly use the two APIs  updateBranchInfo AND  printOutInstrInfo to update the 
                branch_count[2]  in /lib231/lib231.cpp
		    */
            // step 1. access the instr_map in lib231.cpp with updateInstrInfo() and  printOutInstrInfo()
            Module *module = F.getParent();
            LLVMContext &context = module->getContext();

            //void updateBranchInfo(bool taken)
            // If taken is true, then a conditional branch is taken;
            // If taken is false, then a conditional branch is not taken.
            FunctionCallee updateFunc = module->getOrInsertFunction("updateBranchInfo", 
                                        Type::getVoidTy(context), 
                                        Type::getInt1Ty(context)    // taken
                                        );
            //void printOutBranchInfo()
            FunctionCallee printFunc = module->getOrInsertFunction("printOutBranchInfo", 
                                        Type::getVoidTy(context)
                                        );
            
            // step 2. only need to traverse basic blocks in a function to check if its terminator 
            // instruction is a condition branch OR end of a function
            for (BasicBlock &BB : F){
                IRBuilder<> Builder(&BB);
                Builder.SetInsertPoint(BB.getTerminator());
				auto I = BB.getTerminator();

                if ( (string) I->getOpcodeName() == "br" && I->getNumOperands() > 1){
					IRBuilder<> Builder(&*I);
					vector<Value *> args;
					args.push_back(I->getOperand(0));
					Builder.CreateCall(updateFunc, args);
				}
                
                if((string) I->getOpcodeName() == "ret"){
                    // errs() << (string) I->getOpcodeName() << "\n"; 

					IRBuilder<> Builder(&*I);
					Builder.CreateCall(printFunc);
				}
			}

            return false;
        }
	};
}

char BranchIas::ID = 0; 
static RegisterPass<BranchIas> X("cse231-bb", "computes the branch Ias on a per-function basis",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);