/*part 3
Liveness Analysis
    Your first task for this part is to implement a liveness analysis based on the framework implemented in the previous assignment. 
    Recall that a variable is live at a particular point in the program if its value at that point will be used in the future. It is dead otherwise.
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
    // similar to ReachingInfo class implemented in ReachingDefinitionAnalysis.cpp
    class LivenessInfo : public Info {
        public:
            set<unsigned> info;
            
            LivenessInfo() : Info() {}

            LivenessInfo(const LivenessInfo &other) : Info(other)
            {
                info = other.info;
            }

            ~LivenessInfo() {}

            void print()
            {
                for (auto l : info)
                {
                    errs() << l << '|';
                }
                errs() << "\n";
            }

            static bool equals(LivenessInfo *info1, LivenessInfo *info2)
            {
                return info1->info == info2->info;
            }
            
            static void join(LivenessInfo * info1, LivenessInfo * info2, LivenessInfo * result){
                result->info = info1->info;
                result->info.insert(info2->info.begin(), info2->info.end());
            } 
        };

    class LivenessAnalysis : public DataFlowAnalysis<LivenessInfo, false>{
    
        public:
            LivenessAnalysis(LivenessInfo &bottom, LivenessInfo &initialState) : 
            DataFlowAnalysis<LivenessInfo, false>::DataFlowAnalysis(bottom, initialState) {}

            ~LivenessAnalysis() {}

        /*  Flow Functions
        You are asked to implement flow functions that process IR instructions. 
        The flow functions are specified below. You need to implement them in flowfunction in your subclass of DataFlowAnalysis. 

        There are three categories of IR instructions:

            First Category: IR instructions that return a value (define a variable)
           
            Second Category: IR instructions that do not return a value

            Third Category: phi instructions !!!
        */
        void flowfunction(Instruction *I,
                        std::vector<unsigned> &IncomingEdges,
                        std::vector<unsigned> &OutgoingEdges,
                        std::vector<LivenessInfo *> &Infos)
        {
            unsigned index = this->getIndexFromInstr(I);
            string opname(I->getOpcodeName());

            //get instructions for new live vars
            LivenessInfo *livenessInfo = new LivenessInfo();
            for (unsigned i = 0; i < I->getNumOperands(); ++i)
            {
                Instruction *instr = (Instruction *)I->getOperand(i);
                if (this->countInstructions(instr) != 0){   
                    livenessInfo->info.insert(this->getIndexFromInstr(instr));
                }
            }

            //traverse all the IncomingEdges and merge into info_in
            LivenessInfo *info_in = new LivenessInfo();
            for (auto incoming : IncomingEdges)
            {
                auto edge = make_pair(incoming, index);
                LivenessInfo::join(info_in, this->getInfoFromEdge(edge), info_in);
            }

            //identify the categories 
            set<string> cat1 = {"alloca","load","getelementptr","icmp","fcmp","select"};
            set<string> cat2 = {"br","switch","store"};
            set<string> cat3 = {"phi"};

            if (cat1.find(opname) != cat1.end() || I->isBinaryOp())
            {
                // remove the index
                info_in->info.erase(index);
            }
            if (cat2.find(opname) != cat2.end()){
                // do nothing
            }
            // The ‘phi’ instruction is used to implement the φ node in the SSA graph representing the function.
            // http://releases.llvm.org/9.0.0/docs/LangRef.html#phi-instruction
            if (cat3.find(opname) != cat3.end())
            {
                Instruction *firstNonPhiInstr = I->getParent()->getFirstNonPHI();
                unsigned firstNonPhiIndex = this->getIndexFromInstr(firstNonPhiInstr);

                // remove all phi in
                for (unsigned i_phi = index; i_phi < firstNonPhiIndex; i_phi++)
                {
                    info_in->info.erase(i_phi);
                }

                for(unsigned i = 0; i < OutgoingEdges.size(); i++){
                    Infos[i]->info = info_in->info;
                }

                for (unsigned i_phi = index; i_phi < firstNonPhiIndex; i_phi++){
                    
                    // PHINode class: https://llvm.org/doxygen/classllvm_1_1PHINode.html
                    Instruction *instr = this->getInstrFromIndex(i_phi);
                    PHINode *instr_phi = (PHINode*) instr;  
                    
                    for(unsigned j_operand = 0; j_operand < instr_phi->getNumIncomingValues(); j_operand++){
                        
                        Instruction* phiValue = (Instruction*)instr_phi->getIncomingValue(j_operand);
                        
                        if(countInstructions(phiValue)!=0){
                            BasicBlock* phiLabel = instr_phi->getIncomingBlock(j_operand);
                            Instruction* prevInstr = (Instruction *)phiLabel->getTerminator();
                            unsigned prevIndex = getIndexFromInstr(prevInstr);

                            for(unsigned i = 0; i < OutgoingEdges.size(); i++){
                                if(OutgoingEdges[i] == prevIndex){
                                    Infos[i]->info.insert(getIndexFromInstr(phiValue));
                                }
                            }
                        }                        
                    }
                }
                return;
            }

            // Union all info in 
            LivenessInfo::join(info_in, livenessInfo, info_in);
            for (unsigned i = 0; i < Infos.size(); i++)
            {
                Infos[i]->info = info_in->info;
            }

            delete livenessInfo;
            delete info_in;
        }
    };

    struct LivenessAnalysisPass : public FunctionPass{
        static char ID;

        LivenessAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override
        {
            LivenessInfo bot;
            LivenessAnalysis la(bot, bot);
            la.runWorklistAlgorithm(&F);
            la.print();
            return false;
        }
    };
}

char LivenessAnalysisPass::ID = 0;
static RegisterPass<LivenessAnalysisPass> X("cse231-liveness", "livenessAnalysis ",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
                             
                             
