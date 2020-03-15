/* part4  global constant analysis
    Call Graph
        A call graph is a graph which describes the calling relationships between procedures. 
        LLVM builds a call graph for a given module, which consists of nodes representing functions in the module. 
    Edges in the graph are directed edges from caller functions to callees

    The following calculation are supposed to be made in each of the methods -
        1   bool doInitialization(CallGraph &CG)
        You'll build your MPT and LMOD data structures in this method. 
        Just one run across the call graph is sufficient for calculating them

        Remember that since you have the call graph with you, you have access to all the functions in the module.

        2   bool runOnSCC(CallGraphSCC &SCC)
        You'll build your CMOD data structures in this method

        The SCC will give you all the caller-callee relationship that you can use to calculate the MOD for the functions in your module.
        You'll get the LMOD[caller] and then you'll get the MOD[callee] . The union of these two things is MOD[caller]

        3   bool doFinalization(CallGraph &CG)
        The above two functions would have built the MOD map and MPT set.

        This is the function where you'll iterate over the entire call graph and call the worklist algorithm that you had 
        written in 231DFA.h to do the Constant Prop Analysis on each function and print the analysis results.

    LMOD stands for Local MOD and CMOD stands for Callee MOD. 
    Trivially, the variables that may be modified in the body of a function are -
        LMOD ---  the variables modified locally in the body of the function by any instruction excluding calls
        CMOD ---  variables modified in the body of other functions by calls
*/
#include "231DFA.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/Analysis/CallGraph.h"

#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Module.h"

#include "llvm/IR/ConstantFolder.h" 
// use LLVM's ConstantFolder to fold in unary and binary(binaryOp, cmp, select) expressions with constant operands into a constant. 

#include <string>
#include <vector>
#include <set>
#include <map>

using namespace llvm;
using namespace std;   

namespace {

    std::set <Value*> MPTSet;   //  May-point-to set (MPT)   ---  a set of all modified global vars 

    std::map<Function*, set <GlobalVariable*>> MODMap;    //union of LMOD and CMOD sets --- map a function to a set of global variables modified in the function
                                                          // used for inter procedure calls 
    
    class ConstPropInfo : public Info {
        public:
            /*  Lattice
                For this analysis, you will map every global variable to a single constant value, top (not constant), or bottom (all constants). 
                using a lattice of height 2 for every variable guarantees termination in the worklist algorithm.
            */
            enum ConstState{Bottom, Const, Top};    // enum to store which state the operand belongs to
            
            struct Const {  
                ConstState state;
                Constant* value; 
                bool operator == (const Const& other) const{
                    return state == other.state && value == other.value;
                }
            };

            std::map<Value*, struct Const> constMap;   // the map used by ConstPropInfo to store the consts

            // ##############################################################
            // helper fucntion to access constMap
            // ##############################################################
            Constant* getConst(Value* val){
                if(constMap.find(val) != constMap.end()){
                    return constMap[val].value; 
                }
                errs()<< *val <<"Not found "<<"\n";
                return nullptr;
            }

            void setConst(Value * val, Constant * c){
                constMap[val].state = Const;
                constMap[val].value = c;
            }

            void setTop(Value * val){
                constMap[val].state = Top;
                constMap[val].value = nullptr;
            }

            void setBottom(Value * val){
                constMap[val].state = Bottom;
                constMap[val].value = nullptr;
            }

            void copy(Value * src, Value * dst){    
                // copy is very important, need to handle the case where dst is in the constMap or not!!!
                if(constMap.find(dst) != constMap.end()){
                    constMap[dst] = constMap[src];       //Debug fixed
                }
                else{
                    constMap.insert( std::pair<Value*, struct Const>(dst, constMap[src])); 
                }
            }
            
            ConstPropInfo(): Info() { }

            ConstPropInfo(const ConstPropInfo& other): Info(other) {
                constMap = other.constMap;
            }

            ~ConstPropInfo() {}

            void print() {
                for (auto keyval : constMap){
                    Value* val = keyval.first;
                    ConstState state = keyval.second.state;
                    Constant* const_value = keyval.second.value;

                    GlobalVariable* globalVar = dyn_cast<GlobalVariable>(val);
                    if(globalVar){
                        if(state == Const){
                            errs()<< globalVar->getName().str() << '=' << *const_value << '|';
                        }
                        if(state == Bottom){
                            errs()<< globalVar->getName().str() << "=⊥|";
                        }
                        if(state == Top){
                            errs()<< globalVar->getName().str() << "=⊤|";
                        }
                    }
                }
                errs()<<"\n";
            }

            static bool equals(ConstPropInfo * info1, ConstPropInfo * info2) {
                return info1->constMap == info2->constMap;
            }

            static void join(ConstPropInfo * info1, ConstPropInfo * info2, ConstPropInfo * result){
 
                // info1 is for aggregating the result, traverse info2 (incoming Info) to update result !!!
                for( auto keyval : info2->constMap){            //Debug fixed
                    Value* val = keyval.first;
                    //consider condition for state being top or constant in info1 or info2
                    if ( info1->constMap[val].state == Top || info2->constMap[val].state == Top ){ 
                        result->setTop(val);
                    }
                    else if( info1->constMap[val].value && info2->constMap[val].value && info1->constMap[val].value != info2->constMap[val].value){
                        result->setTop(val);
                    }
                    else if( info1->constMap[val].state == Const) {
                        result->setConst(val, info1->constMap[val].value);
                    }
                    else if( info2->constMap[val].state == Const) {
                        result->setConst(val, info2->constMap[val].value);
                    }
                    else{
                        //if state in both infos is neither top nor constant
                        result->setBottom(val);
                    }
                }
            } 
    };

    /*
        class ConstPropAnalysis performs const propagation analysis. 
        It should be a subclass of DataFlowAnalysis. 
    */
    template <class Info, bool Direction>
    class ConstPropAnalysis : public DataFlowAnalysis<ConstPropInfo, Direction> {
    public:
        ConstPropAnalysis(ConstPropInfo &bottom, ConstPropInfo &initialState):   
            DataFlowAnalysis<Info, Direction>::DataFlowAnalysis(bottom, initialState) {}

        ~ConstPropAnalysis() {}

        void flowfunction(  Instruction * I, 
                            vector<unsigned> & IncomingEdges,
                            vector<unsigned> & OutgoingEdges, 
                            vector<Info *> & Infos){
            
            ConstantFolder FOLDER;
            auto *result = new ConstPropInfo();
            unsigned index = this->getIndexFromInstr(I);
            // string opName(I->getOpcodeName());
            // errs()<< "####################  opName  "   << opName<<"\n"; 

            // ##################################################
            // Step 1: merge all incoming edges with the join operation.
            // ##################################################
            for (auto incoming : IncomingEdges)
            {
                auto edge = make_pair(incoming, index);
                Info::join(result, this->getInfoFromEdge(edge), result);  
            }

            // ##################################################
            // Step 2: identify the opcode name 
            // Ref  Inst:   https://llvm.org/doxygen/classllvm_1_1Instruction.html
            // ##################################################
            // 1. Binary operator  (Unary, CMP, Select)    BinaryOperator -> Instruction
            // <result> = add <ty> <op1>, <op2>          ; yields ty:result
            // AND            
            // 2. Bitwise    BitCastInst -> CastInst -> UnaryInst -> Instruction         
            if (BinaryOperator* bin_op = dyn_cast<BinaryOperator>(I)){

                // 1    check if x and y are const 
                Value* x = bin_op->getOperand(0);
                Value* y = bin_op->getOperand(1);

                Constant* const_x = dyn_cast<Constant>(x);
                Constant* const_y = dyn_cast<Constant>(y);

                // 2    check in constMap
                //A = x + y
                //4 possibilities - x -> {constant, not constant}, y->{constant, not constant}
                if(! const_x){
                    const_x = result->getConst(x);
                }
                if(! const_y){
                    const_y = result->getConst(y);
                }   

                // 3    setConst  OR  Top
                // Const analysis is a Must Analysis, 
                // only if both x and y are const, we can say a is const
                if(const_x && const_y){
                    result->setConst(I, FOLDER.CreateBinOp(bin_op->getOpcode(), const_y, const_x)); 
                }
                else{
                    result->setTop(I);
                }
            }

            //3. Unary  UnaryOperator -> UnaryInstruction ->  Instruction
            // <result> = fneg [fast-math flags]* <ty> <op1>   ; yields ty:result
            if (UnaryOperator* unary_op = dyn_cast<UnaryOperator>(I)){

                Value* x = unary_op->getOperand(0);
                Constant* const_x = dyn_cast<Constant>(x);

                if (!const_x){
                    const_x = result->getConst(x);
                }
                if(const_x){
                    result->setConst(I, FOLDER.CreateUnOp(unary_op->getOpcode(), const_x)); 
                }
                else{
                    result->setTop(I);
                }
            }
            
            //4. load  LoadInst -> Instruction
            if (LoadInst* load_inst = dyn_cast<LoadInst>(I)){
                Value* val = load_inst->getPointerOperand();  
                result->copy(val, I);
            }

            //5. store  StoreInst -> Instruction
            //store [volatile] <ty> <value>, <ty>* <pointer>
            if (StoreInst* store_inst = dyn_cast<StoreInst>(I)){
                
                Value* val = store_inst->getValueOperand();                  
                Value* ptr = store_inst->getPointerOperand();    
                
                if (LoadInst* load_inst = dyn_cast<LoadInst>(ptr)){
                    //case1: *ptr = ...
                    // when we encounter an instruction which modifies a dereferenced pointer, set all variables in MPT to top.
                    // *var = ....  (load and store)        
                    for(Value* mptVar : MPTSet){
                        result->setTop(mptVar);
                    }
                }
                else{
                    //case2: y = 3
                    if (Constant * const_val = dyn_cast<Constant>(val)){
                        result->setConst(ptr, const_val); 
                    }
                    //case3: y = x
                    else{
                        result->copy(val, ptr);
                    }
                }
            }

            //###############################################################
            //6. call   CallInst -> CallBase -> Instruction
            //  To simplify the analysis, after a call instruction we set all variables in the callee's MOD set to top 
            //  (we assume every variable in MOD was modified to some non constant value).
            if (CallInst* call_inst = dyn_cast<CallInst>(I)){
                for(auto glob : MODMap[call_inst->getCalledFunction()]){
                    result->setTop(glob);
                }
            }

            //###############################################################
            //7. icmp -- int compare       ICmpInst -> CmpInst  ->  Instruction
            // The ‘icmp’ instruction takes three operands. The first operand is the condition code indicating the kind of comparison to perform.
            // It is not a value, just a keyword. The possible condition codes are:
            // <result> = icmp <cond> <ty> <op1>, <op2>   ; yields i1 or <N x i1>:result
            if (ICmpInst* icmp_inst = dyn_cast<ICmpInst>(I)){

                auto pred = icmp_inst->getPredicate();
                Value* x = icmp_inst->getOperand(0);
                Value* y = icmp_inst->getOperand(1);

                Constant * const_x = dyn_cast<Constant>(x);
                Constant * const_y = dyn_cast<Constant>(y);
                
                if (!const_x){
                    const_x = result->getConst(x);
                }
                if (!const_y){
                    const_y = result->getConst(y);
                }
                if(const_x && const_y){
                    result->setConst(I, FOLDER.CreateICmp (pred, const_x, const_y)); 
                }
                else{
                    result->setTop(I);
                }
            }

            //8. fcmp -- flow compare      FCmpInst -> CmpInst  ->  Instruction
            // <result> = fcmp [fast-math flags]* <cond> <ty> <op1>, <op2>     ; yields i1 or <N x i1>:result
            if (FCmpInst* fcmp_inst = dyn_cast<FCmpInst>(I)){

                auto pred = fcmp_inst->getPredicate ();
                Value* x = fcmp_inst->getOperand(0);
                Value* y = fcmp_inst->getOperand(1);

                Constant * const_x = dyn_cast<Constant>(x);
                Constant * const_y = dyn_cast<Constant>(y);
                
                if (!const_x){
                    const_x = result->getConst(x);
                }
                if (!const_y){
                    const_y = result->getConst(y);
                }
                if(const_x && const_y){
                    result->setConst(I, FOLDER.CreateFCmp (pred, const_x, const_y)); 
                }
                else{
                    result->setTop(I);
                }
            }

            //###############################################################
            //9. phi     PHINode          similar to reachingDef 
            // The ‘phi’ instruction is used to implement the φ node in the SSA graph representing the function.
            // <result> = phi [fast-math-flags] <ty> [ <val0>, <label0>], ...
            if (PHINode* phi_node = dyn_cast<PHINode>(I)){
                
                Value* val = phi_node->hasConstantValue();

                if(val){
                    Constant* const_val = dyn_cast<Constant>(val);
                    if(!const_val){
                        const_val = result->getConst(val);
                    }
                    if(const_val){
                        result->setConst(I, const_val);
                    }
                }
                else{
                    // Incoming values not all the same. return nullptr
                    result->setTop(I);
                }
            }

            //###############################################################
            //10. select  SelectInst -> Instruction
            // <result> = select [fast-math flags] selty <cond>, <ty> <val1>, <ty> <val2>             ; yields ty
            // %X = select i1 true, i8 17, i8 42          ; yields i8:17
            if (SelectInst* select_inst = dyn_cast<SelectInst>(I)){

                Value* operand1 = select_inst->getTrueValue();
                Value* operand2 = select_inst->getFalseValue();
                Value* cond = select_inst->getCondition();
                
                Constant* operand1_const = dyn_cast<Constant>(operand1);
                Constant* operand2_const = dyn_cast<Constant>(operand2);
                Constant* cond_const = dyn_cast<Constant>(cond);
                
                if (!operand1_const){
                    operand1_const = result->getConst(operand1);
                }
                if (!operand2_const){
                    operand2_const = result->getConst(operand2);
                }
                if (!cond_const){
                    cond_const = result->getConst(cond);
                }
                
                //You'll only set it to constant if -
                //      the predicate(condition), op1 and op2 are constants
                //      op1 and op2 are equal and are constant (condition becomes irrelevant in this case)
                if(cond_const && operand1_const && operand2_const){
                    result->setConst(I, FOLDER.CreateSelect(cond_const, operand1_const, operand2_const)); 
                }
                else if(operand1_const && operand2_const && operand1_const == operand2_const){
                    result->setConst(I, operand1_const); 
                }
                else{
                    result->setTop(I);
                }
            }

            // ##################################################
            // Step 3: Add result to outgoing edges
            // ##################################################
            for(unsigned i=0; i<OutgoingEdges.size(); i++){
                // Infos[i]->constMap = result->constMap;
                Infos[i]->constMap.insert(result->constMap.begin(), result->constMap.end()); 
            }
            
            delete result;
        }
    };

 
    struct ConstPropAnalysisPass : public CallGraphSCCPass 
    {
        static char ID;
        
        ConstPropAnalysisPass() : CallGraphSCCPass(ID) {}
        
        /*
        // Part 1   Mod Analysis
        // inter-procedural modified global variables analysis.
            1    Calculate a MPT set for your module;
            2    Calculate an LMOD set of each function in your module;
            3    Iteratively calculate CMOD until you reach a fixed set.
            4    You may assume no composite-typed variables exist in the module. 
            5    You should be writing test cases as you design this analysis pass to make sure you're calculating every set correctly.
            6    You will only be using the information you calculate here (the final MOD set for each function) in your next analysis, so there's no need to print any output.
        */
        // 1.1 traverse the CallGraph to build  MPT and LMOD data structures
        bool doInitialization(CallGraph & CG) override {
            
            set<Function*> StarFuncSet;
            
            for(Function& F : CG.getModule().functions()){
                
                for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I){

                    string opName(I->getOpcodeName());
                    
                    if (opName == "store"){     // y = &x
                            
                        // If you read the address of any variable (for example X = &Y), 
                        // the variable must be added to the MPT set.   store src , dst
                        Value* valueOperand = I->getOperand(0);       //Y
                        Value* pointerOperand = I->getOperand(1);     //X

                        MPTSet.insert(valueOperand);    

                        // If an instruction modifies a global variable, the global variable must be added to LMOD, glob = ....
                        // Add glob to the LMOD set for that function
                        if (GlobalVariable* globalVar = dyn_cast<GlobalVariable>(pointerOperand)){   
                            MODMap[&F].insert(globalVar);
                        }

                        // If an instruction modifies a dereferenced pointer in any given function F, 
                        // *var = ....  (load and store)
                        // you'll need to add the subset of MPT containing GlobalVariables to the LMOD for that particular function.
                        if (dyn_cast<LoadInst>(pointerOperand)){
                            StarFuncSet.insert(&F);
                        }
                    }

                    if (opName == "call" || opName == "ret" ){
                        for (Use& operand : I->operands()) {
                            // If you encounter an operand in a function that is being passed by reference, 
                            // you need to add it to the MPT set as well.  EX   function foo (....&operand....){
                            MPTSet.insert(operand);
                        }
                    }
                }
            }

            for(Function* F : StarFuncSet){
                // add the subset of MPT containing GlobalVariables to the LMOD for that particular function.
                for (auto Val : MPTSet){
                    if (GlobalVariable *globalVar = dyn_cast<GlobalVariable>(Val)){
                        MODMap[F].insert(globalVar);
                    }
                }
            }
            
            return false;
        }	
        
        //1.2  build your CMOD data structures 
        /*     
            MOD[caller] = LMOD[caller] U MOD[callee]

            The SCC will give you all the caller-callee relationship that you can use to calculate the MOD for the functions in your module. 
            You'll get the LMOD[caller] and then you'll get the MOD[callee] . The union of these two things is MOD[caller]

            !!! CallGraphSCCPass does a bottom-up traversal on the CallGraph, 
            i.e., it starts from the leaf nodes.
            The callee info would have been calculated before we go to the caller

            Ref: https://llvm.org/doxygen/classllvm_1_1CallGraphNode.html#a5235ef73c96bae36f342bb61e9b02071
                 https://llvm.org/doxygen/CallGraph_8h_source.html#l00187
        */
        bool runOnSCC(CallGraphSCC &SCC) override{
           
            set<GlobalVariable*> currSCCModSet; // all graphNode has the same MOD set

            //Get CallGraphNode *caller_node from SCC
            for(CallGraphNode* caller_node : SCC){

                //Get Function* caller from the caller_node (using getFunction())
                Function* caller_F = caller_node->getFunction();

                // Get CallGraphNode *callee_node from the *caller_node
                for (auto callrecord : (*caller_node)){
                    // Get Function* callee from the callee_node (using getFunction())
                    Function* callee_F = callrecord.second->getFunction();

                    // Union Callee’s MOD with the Caller’s MOD (set of GlobalVariable*)
                    if(callee_F && caller_F){
                       MODMap[caller_F].insert(MODMap[callee_F].begin(), MODMap[callee_F].end());
                    }  
                }
                // add MODMap[caller_F] into currSCCModSet
                currSCCModSet.insert(MODMap[caller_F].begin(), MODMap[caller_F].end());                    
            }

            // update MOD of all F in the SCC            
            for(CallGraphNode* caller_node : SCC){
                Function* caller_F = caller_node->getFunction();
                MODMap[caller_F] = currSCCModSet;
            }

            //##################################################
            // debug 
            //##################################################
            // errs()<< "############### SCC ###################\n";
            // errs()<< "MPTSet";
            // for (Value* val : MPTSet){
            //     errs()<< *val << "\n";
            // }
            // errs()<< "\nMODMap";
            // for (auto entry : MODMap){
            //     errs()<< entry.first << "==> ";
            //     for (GlobalVariable* gb : entry.second){
            //         errs()<< *gb << "   ";
            //     } 
            //     errs()<< "\n";
            // }
            //##################################################   
            return false;
        }

        //#################################################################################
        // Part2    Constant Propagation Analysis
        //  In part 4, you will also need to implement a constant propagation analysis based on the data-flow analysis framework you used earlier in the project.
        //  The analysis describes at each point in the program which global variables must be a constant value, and their corresponding constant values
        bool doFinalization(CallGraph &CG) override {
            
            for(Function& F : CG.getModule().functions()){
                ConstPropInfo top, bot;
                // set all global to top
                for(GlobalVariable& glob : CG.getModule().getGlobalList()){
                    top.setTop(&glob);
                }
                for(GlobalVariable& glob : CG.getModule().getGlobalList()){
                    bot.setBottom(&glob);
                }
                ConstPropAnalysis<ConstPropInfo,true> cpa(bot, top);    //buttom, initStte
                cpa.runWorklistAlgorithm(&F);
                cpa.print();                    
            }
            
            return false;
        }
    };
}

char ConstPropAnalysisPass::ID = 0;
static RegisterPass<ConstPropAnalysisPass> X("cse231-constprop", "ConstPropAnalysisPass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);