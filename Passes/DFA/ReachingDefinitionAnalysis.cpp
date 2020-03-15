/*	Part 2.1
 implement a reaching definition analysis based on the framework you implemented.
 
 Control Flow Graph (CFG)
    LLVM builds a CFG for a given function, and this CFG is available when your function pass is running. 
    Let us call it LLVM CFG. 
    
    The function void initializeForwardMap(Function * func) in 231DFA.h also builds a CFG of the given function func for forward analyses. 
    Let us call it DFA CFG. Analyses based on 231DFA.h should work on DFA CFGs. 
*/
#include "231DFA.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"

#include <string>
#include <vector>
#include <set>

using namespace llvm;
using namespace std;

namespace {
    
    /*
        class ReachingInfo is the class represents the information at each program point for your 
        reaching definition analysis. It should be a subclass of class Info in 231DFA.h;
    */
    class ReachingInfo : public Info {
        public:
            set<unsigned> definedInsts;
            
            ReachingInfo(): Info() { }

            // the domain D for this analysis is Powerset(S) where S is a set of the indices of all the instructions in the function. 
            // The bottom is the empty set
            ReachingInfo(const ReachingInfo& other): Info(other) {
                definedInsts = other.definedInsts;
            }

            ~ReachingInfo() { }
            
            /*
            * Print out the information
            *
            * Direction:
            *   In your subclass you should implement this function according to the project specifications.
            */
            void print() {
                for (auto def : definedInsts){
                    errs()<<def<<'|';
                }
                errs()<<"\n";
            }

            /*
            * Compare two pieces of information
            *
            * Direction:
            *   In your subclass you need to implement this function.
            */
            static bool equals(ReachingInfo * info1, ReachingInfo * info2) {
                return info1->definedInsts == info2->definedInsts;
            }

            /*
            * Join two pieces of information.
            * The third parameter points to the result.
            *
            * Direction:
            *   In your subclass you need to implement this function.
            */
            static Info* join(ReachingInfo * info1, ReachingInfo * info2, ReachingInfo * result){
                result->definedInsts = info1->definedInsts;
                result->definedInsts.insert(info2->definedInsts.begin(), info2->definedInsts.end());
                return result;
            } 
    };

    /*
        class ReachingDefinitionAnalysis performs reaching definition analysis. 
        It should be a subclass of DataFlowAnalysis. 
    */
    template <class Info, bool Direction>
    class ReachingDefinitionAnalysis : public DataFlowAnalysis<Info, Direction> {
    public:
        ReachingDefinitionAnalysis(Info &bottom, Info &initialState):   
            DataFlowAnalysis<Info, Direction>::DataFlowAnalysis(bottom, initialState) {}

        ~ReachingDefinitionAnalysis() {}

        void flowfunction(  Instruction * I, vector<unsigned> & IncomingEdges,
                            vector<unsigned> & OutgoingEdges, vector<Info *> & Infos){
            
            unsigned index = this->getIndexFromInstr(I);
            string opcodeName(I->getOpcodeName());

            ReachingInfo *info_in = new ReachingInfo();     // merge info in 

            //Step1: traverse all the IncomingEdges and merge their info sets
            for (auto incoming : IncomingEdges){
                auto edge = make_pair(incoming, index);
                Info* info_neighbour = this->getInfoFromEdge(edge);
                Info::join(info_in, info_neighbour, info_in);
            }

            //Step2: identify the three categories AND add into definedInsts in info_in if need.
            //Every instruction above falls into one of the three categories. 
            //  If an instruction has multiple outgoing edges, all edges have the same information. 
            //  Any other IR instructions that are not mentioned above should be treated as IR instructions that do not return a value
            set<string> cat1 = {"alloca","load","getelementptr","icmp","fcmp","select"};
            set<string> cat2 = {"br","switch","store"};
            set<string> cat3 = {"phi"};
            
            if (I->isBinaryOp() || cat1.find(opcodeName)!=cat1.end()){
                //First Category: IR instructions that return a value (defines a variable)
                //  where index is the index of the IR instruction, which corresponds to the variable <result> being defined.
                info_in->definedInsts.insert(index);
            } 
            if(cat2.find(opcodeName)!=cat2.end()){
                //Second Category: IR instructions that do not return a value
                //  do nothing 
            } 
            if(cat3.find(opcodeName)!=cat3.end()){
                //Third Category: phi instructions
                //At runtime, the ‘phi’ instruction logically takes on the value specified by the pair 
                //corresponding to the predecessor basic block that executed just prior to the current block.
                //ref: https://llvm.org/docs/LangRef.html#phi-instruction
                //  In the LLVM CFG, these phi instructions are connected sequentially. 
                //  In the DFA CFG, phi 1 has an outgoing edge connecting to the first non-phi instruction %res = add %a, %b directly.
                //we want to adapth LLVM CFG to DFA CFG by traversing the phi connected sequences
                unsigned i=index;
                
                //find the ending of phi by finding the first non phi
                Instruction * firstNonPhi = I->getParent()->getFirstNonPHI();
                unsigned indexOfFirstNonPhi = this->getIndexFromInstr(firstNonPhi);

                //traverse from first phi to the first nonPhi
                while( i < indexOfFirstNonPhi) {
                    info_in->definedInsts.insert(i);
                    i++;
                }
            }

            //Step3: add the newly computed information into the flow function result called Infos
            for(unsigned i=0; i<OutgoingEdges.size(); i++){
                Infos.push_back(new Info());
                Infos[i]->definedInsts = info_in->definedInsts;
            }
            delete info_in;
        }
    };

    /*
        A function pass called ReachingDefinitionAnalysisPass in ReachingDefinitionAnalysis.cpp: 
        This pass should be registered by the name cse231-reaching.
        
        After processing a function, this pass should print out the reaching definition information at each progrm point to stderr. 
        The output should be in the following form:
            Edge[space][src]->Edge[space][dst]: [def 1]|[def 2]| ... [def K]|\n
        where [src] is the index of the instruction that is the start of the edge, 
        [dst] is the index of the instruction that is the end of the edge, 
        [def 1], [def 2] ... [def K] are indices of instructions (definitions) that reach at this program point. 
    */
    struct ReachingDefinitionAnalysisPass : public FunctionPass {
        static char ID;

        ReachingDefinitionAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
            ReachingInfo baseInfo;
            ReachingDefinitionAnalysis<ReachingInfo,true> rda(baseInfo, baseInfo);
            rda.runWorklistAlgorithm(&F);   // call method of parent class "DataFlowAnalysis"
            rda.print();                    // call overriden print()
            return false;
        }
    };
}

char ReachingDefinitionAnalysisPass::ID = 0;
static RegisterPass<ReachingDefinitionAnalysisPass> X("cse231-reaching", "ReachingDefinitionAnalysis",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);