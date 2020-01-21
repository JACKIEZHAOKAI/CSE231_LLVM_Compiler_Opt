#include <iostream>
// LLVM lib
#include "llvm/Pass.h"
// Function -> BasicBlock -> Iterator
#include "llvm/IR/Function.h"   
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Value.h"
// #include "llvm/IR/Constants.h"

// IRBuilder        #include "llvm/IR/IRBuilder.h”
/// This provides a uniform API for creating instructions and inserting
/// them into a basic block: either at the end of a BasicBlock, or at a specific
/// iterator location in a block.

/// SetInsertPoint() specifies that created instructions should be inserted before the specified instruction.
//     IRBuilder::SetInsertPoint    /// This specifies that created instructions should be appended to the end of the specified block.

//  create... methods on the IRBuilder instance insert instructions at the specified point.
//     IRBuilder::CreateCall        /// brief Create a callbr instruction.
//     IRBuilder::CreatePointerCast // Value *CreatePointerCast(Value *V, Type *DestTy, const Twine &Name = "")

// https://llvm.org/doxygen/IRBuilder_8h_source.html
#include "llvm/IR/IRBuilder.h"

// FunctionType =>  derived from Type Class
//     ArrayType::get
//     IntegerType::get
//     ConstantInt::get
// https://llvm.org/doxygen/Type_8h_source.html
#include "llvm/IR/Type.h"

// Module
//     Module::getOrInsertFunction       /// the returned value is a FunctionCallee wrapper around the 'FunctionType *T' passed in, 
//      as well as a 'Value*' either of the Function or the bitcast to the function.
// https://llvm.org/doxygen/Module_8h_source.html
#include "llvm/IR/Module.h"

// C++ STL
#include <map>
#include <string>
#include <vector>

using namespace llvm;
using namespace std;

namespace {
	struct CountDynamicInstructions : public FunctionPass {
        /*
            mainly use the two APIs  updateInstrInfo AND  printOutInstrInfo to update the 
            instr_map  in /lib231/lib231.cpp
		*/
        static char ID;

		CountDynamicInstructions() : FunctionPass(ID) {}

		bool runOnFunction(Function &F) override {
            // step 1. access the instr_map in lib231.cpp with updateInstrInfo() and  printOutInstrInfo()
			Module *module = F.getParent();     // access module symbol table
            LLVMContext &context = module->getContext();    //get syntax environment context?

            // FunctionCallee derived from Type Class
            // getOrInsertFunction - Look up the specified function in the module symbol
            // table.  If it does not exist, add a prototype for the function and return
            // it.  This is nice because it allows most passes to get away with not handling
            // the symbol table directly for this common task.

            // updateInstrInfo update the instr_map during each basic block     F1
            FunctionCallee updateFunc = module->getOrInsertFunction("updateInstrInfo", 
                                        Type::getVoidTy(context),       // return void 
                                        // unsigned num, uint32_t * keys, uint32_t * values
                                        Type::getInt32Ty(context),      // num: the number of unique instructions in the basic block. It is the length of keys and values.
                                        Type::getInt32PtrTy(context),   // keys: the array of the opcodes of the instructions
                                        Type::getInt32PtrTy(context)    // values: the array of the counts of the instructions
                                        );
            // print out all entries in the instr_map       F2
            FunctionCallee printFunc = module->getOrInsertFunction("printOutInstrInfo", 
                                        Type::getVoidTy(context)    // return void 
                                        );

            // step 2. traverse basic blocks in the input function and update the instr_map in lib231.cpp

            //  A basic block is simply a container of instructions that execute sequentially. 
            //  Basic blocks are Values because they are referenced by instructions such as branches and switch tables. 
            //  The type of a BasicBlock is "Type::LabelTy" because the basic block represents a label to which a branch can jump.

            // A basic block is a single-entry, single-exit section of code. 
            // For this reason, you are guaranteed that if execution enters a basic block, 
            // all instructions in the basic block will be executed in a straight line. 
            // You can use this to your advantage to avoid instrumenting every instruction individually.
            for (BasicBlock &B : F){
 
                // step 2.1 count the instructions in this basic block in local
                // and transform into key lists and value lists
                map<unsigned, unsigned>  counter;   // map unique instruction to its freq
                for (Instruction &I : B){
                    ++counter[I.getOpcode()];
                }
                
                unsigned num_unique_instr = counter.size(); // para feed into F1.1 updateInstrInfo() 
                vector<uint32_t> keys;      // para feed into F1.2
                vector<uint32_t> vals;      // para feed into F1.3
                
                // transform the counter map to two array
                for(const auto& it : counter){
                    keys.push_back(it.first);
                    vals.push_back(it.second);
                }
               
                // step 2.2 construct GlobalVariable to store keys array and vals array
                vector<Value*> args;    //arg list
                
                ArrayType* array_type = ArrayType::get(IntegerType::get(context, 32), num_unique_instr);
                Constant * keys_const = ConstantDataArray::get(context, *(new ArrayRef<uint32_t>(keys)));
                Constant * vals_const = ConstantDataArray::get(context, *(new ArrayRef<uint32_t>(vals)));

                GlobalVariable* keys_global = new GlobalVariable(
                                        *module,
                                        array_type,
                                        true,
                                        GlobalValue::InternalLinkage,
                                        keys_const,
                                        "key_global");

                GlobalVariable* values_global = new GlobalVariable(
                                        *module,
                                        array_type,
                                        true,
                                        GlobalValue::InternalLinkage,
                                        vals_const,
                                        "val_global");

                // step 2.3 add all three para into the args list, and function call to updateInstrInfo()
                IRBuilder<> irBuilder(&B);
                
                args.push_back(ConstantInt::get(Type::getInt32Ty(context), num_unique_instr));
                args.push_back(irBuilder.CreatePointerCast(keys_global, Type::getInt32PtrTy(context)));
                args.push_back(irBuilder.CreatePointerCast(values_global, Type::getInt32PtrTy(context)));

                irBuilder.SetInsertPoint(B.getTerminator());    
                irBuilder.CreateCall(updateFunc, args);         //call updateFunc()->updateInstrInfo()

                // step 2.4  check if ends of any funciton(function call inside the main function), 
                // if so, function call to printOutInstrInfo()
                for (Instruction &I : B){
                    if ((string) I.getOpcodeName() == "ret") {
                        irBuilder.SetInsertPoint(&I);       //OR B.getTerminator()   
                        irBuilder.CreateCall(printFunc);    //call printFunc()->printOutInstrInfo()
                    }
                }
            }
            return false;
		}
	};
}

char CountDynamicInstructions::ID = 0; //initialize pass ID here. LLVM uses ID’s address to identify a pass, so initialization value is not important.
static RegisterPass<CountDynamicInstructions> X("cse231-cdi", "counts the number of each unique instruction in a function dynamically",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);