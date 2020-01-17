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
//     IRBuilder::SetInsertPoint    /// This specifies that created instructions should be appended to the end of the specified block.
//     IRBuilder::CreateCall        /// \brief Create a callbr instruction.
//     IRBuilder::CreatePointerCast
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
		static char ID;

		CountDynamicInstructions() : FunctionPass(ID) {}

		bool runOnFunction(Function &F) override {
			Module *module = F.getParent();
      LLVMContext &context = module->getContext();

      // set the insertion point of updateFunc and printFunc 
      // To insert calls to a function, you will find the following functions useful:
          // FunctionType::get
          // Module::getOrInsertFunction
          // IRBuilder::CreateCall
      FunctionCallee updateFunc = module->getOrInsertFunction("updateInstrInfo", 
                                  Type::getVoidTy(context), 
                                  Type::getInt32Ty(context), 
                                  Type::getInt32PtrTy(context), 
                                  Type::getInt32PtrTy(context)
                                  );

      FunctionCallee printFunc = module->getOrInsertFunction("printOutInstrInfo", 
                                  Type::getVoidTy(context)
                                  );
      // A basic block is a single-entry, single-exit section of code. 
      // For this reason, you are guaranteed that if execution enters a basic block, 
      // all instructions in the basic block will be executed in a straight line. 
      // You can use this to your advantage to avoid instrumenting every instruction individually.
      
      // traverse blocks in a function
      // for (Function::iterator B = F.begin(), BE = F.end(); B != BE; ++B) {
      for (BasicBlock &B : F){
          // traverse instructions in a block and add to counter map
          map<uint32_t,uint32_t> counter;   // map unique instruction to its freq
          // for (BasicBlock::iterator it = B->begin(), IE = B->end(); it != IE; ++it) {
          for (Instruction &I : B){
            ++counter[I.getOpcode()];
          }

          uint32_t numKey = counter.size();

          IRBuilder<> irBuilder(&B);     // construct a irBuilder obj
          irBuilder.SetInsertPoint(B.getTerminator()); //IRBuilder::SetInsertPoint sets the insertion point

          // traverse the counter map 
          std::vector<Value*> args;
          std::vector<uint32_t> keys;
          std::vector<uint32_t> vals;          
          
          for(auto it = counter.begin(); it != counter.end(); ++it){
              keys.push_back(it->first);
              vals.push_back(it->second);
              // errs() << (it->first) << "\t" << it->second << "\n"; 
          }

          Constant * keys_const = ConstantDataArray::get(context, *(new ArrayRef<uint32_t>(keys)));
          Constant * vals_const = ConstantDataArray::get(context, *(new ArrayRef<uint32_t>(vals)));

          ArrayType* arrayTy = ArrayType::get(IntegerType::get(context, 32), numKey);

          GlobalVariable* keys_global = new GlobalVariable(
                                  *module,
                                  arrayTy,
                                  true,
                                  GlobalValue::InternalLinkage,
                                  keys_const,
                                  "key_global");

          GlobalVariable* vals_global = new GlobalVariable(
                                  *module,
                                  arrayTy,
                                  true,
                                  GlobalValue::InternalLinkage,
                                  vals_const,
                                  "val_global");

          args.push_back(ConstantInt::get(Type::getInt32Ty(context), numKey));
          args.push_back(irBuilder.CreatePointerCast(keys_global, Type::getInt32PtrTy(context)));
          args.push_back(irBuilder.CreatePointerCast(vals_global, Type::getInt32PtrTy(context)));

          //create... methods on the IRBuilder instance insert instructions at the specified point.
          irBuilder.CreateCall(updateFunc, args);   

          // for (BasicBlock::iterator I = B->begin(), IE = B->end(); I != IE; ++I) {
          for (Instruction &I : B){

              errs() << (string) I.getOpcodeName()  << "\n"; 

              if ((string) I.getOpcodeName() == "ret") {
                  irBuilder.SetInsertPoint(&I); // &*I
                  irBuilder.CreateCall(printFunc);
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
