/*  May-point-to Analysis
    In part 3, you will also need to implement a may-point-to analysis based on the framework you implemented.
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

namespace
{
    class MayPointToInfo : public Info
    {
    public:
        /*  Let Pointers be the set of the DFA identifiers of the pointers in the function (including IR pointers and memory pointers) 
            and MemoryObjects the set of the DFA identifiers of the memory objects allocated in the function. 
            The domain D for this analysis is Powerset(S), where S={p → o | p ∊ Pointers && o ∊ MemoryObjects}. 
        */
        map<unsigned, set<unsigned>> pointerMap;

        MayPointToInfo() : Info() {}

        MayPointToInfo(const MayPointToInfo &other) : Info(other)
        {
            pointerMap = other.pointerMap;
        }

        ~MayPointToInfo() {}

        /*
            The output should be in the following form:
                Edge[space][src]->Edge[space][dst]:[point-to 1]|[point-to 2]| ... [point-to K]|

            EX
            opt -load  submission_pt3.so  -cse231-maypointto </tests/test-example/test1.ll>   /dev/null
            Edge 0->Edge 1:
            Edge 1->Edge 2:R1->(M1/)|
            Edge 2->Edge 3:R1->(M1/)|R2->(M2/)|
            Edge 3->Edge 4:R1->(M1/)|R2->(M2/)|
            Edge 4->Edge 5:R1->(M1/)|R2->(M2/)|
            Edge 5->Edge 6:R1->(M1/)|R2->(M2/)|
            Edge 6->Edge 7:R1->(M1/)|R2->(M2/)|
            Edge 7->Edge 8:R1->(M1/)|R2->(M2/)|
            Edge 7->Edge 12:R1->(M1/)|R2->(M2/)|
            Edge 8->Edge 9:R1->(M1/)|R2->(M2/)|
            Edge 9->Edge 10:R1->(M1/)|R2->(M2/)|
            Edge 10->Edge 11:R1->(M1/)|R2->(M2/)|
            Edge 11->Edge 16:R1->(M1/)|R2->(M2/)|
            Edge 12->Edge 13:R1->(M1/)|R2->(M2/)|
            Edge 13->Edge 14:R1->(M1/)|R2->(M2/)|
            Edge 14->Edge 15:R1->(M1/)|R2->(M2/)|
            Edge 15->Edge 16:R1->(M1/)|R2->(M2/)|
            Edge 16->Edge 17:R1->(M1/)|R2->(M2/)|
            Edge 17->Edge 18:R1->(M1/)|R2->(M2/)|
            Edge 18->Edge 19:R1->(M1/)|R2->(M2/)|
        */
        void print()
        {
            for (auto entry: pointerMap) {
				if (entry.second.size() == 0)
					continue;

				errs() << "R" << entry.first << "->(";

				for (auto mi : entry.second) {
					errs() << "M" << to_string(mi & (~(1 << 15))) << "/";
				}
				errs() << ")|";
			}
			errs() << "\n";
        }

        static bool equals(MayPointToInfo *info1, MayPointToInfo *info2)
        {
            return info1->pointerMap == info2->pointerMap;
        }

        static void *join(MayPointToInfo *info1, MayPointToInfo *info2, MayPointToInfo *result)
        {
            result->pointerMap = info1->pointerMap;
            for (auto entry : info2->pointerMap)
            {
                if (!entry.second.empty())
                {
                    result->pointerMap[entry.first].insert(entry.second.begin(), entry.second.end());
                }
            }
            return nullptr;
        }
    };

    class MayPointToAnalysis : public DataFlowAnalysis<MayPointToInfo, true>
    {
    public:
        MayPointToAnalysis(MayPointToInfo &bottom, MayPointToInfo &initialState) : 
        DataFlowAnalysis<MayPointToInfo, true>::DataFlowAnalysis(bottom, initialState) {}

        ~MayPointToAnalysis() {}

        void flowfunction(Instruction *I,
                        std::vector<unsigned> &IncomingEdges,
                        std::vector<unsigned> &OutgoingEdges,
                        std::vector<MayPointToInfo *> &Infos)
        {
            auto *infoIn = new MayPointToInfo();
            unsigned index = this->getIndexFromInstr(I);
            
            // Step 1: merge all incoming edges with the join operation.
            for (auto start : IncomingEdges)
            {
                auto edge = make_pair(start, index);
                MayPointToInfo::join(infoIn, this->getInfoFromEdge(edge), infoIn);
            }

            // Step 2: identify the opcode name 
            string opName(I->getOpcodeName());

            /*  alloca
                out = in U {Ri->Mi} */
            if (opName == "alloca")
            {
                // convert IR to MemoryObject and allocate the instruction into pointerMap
                unsigned instrIndex = index | (1 << 15);
                infoIn->pointerMap[index].insert(instrIndex);
            }

            /*  bitcast OR  getelementptr
                out = in U {Ri->X | Rv -> X } 
                where Rv is the DFA identifier of <value>.  */
            if (opName == "bitcast" || opName == "getelementptr")
            {
                Instruction *instruction = (Instruction *)I->getOperand(0);
                // not duplicated instruction
                if (this->countInstructions(instruction) != 0)
                {
                    unsigned instructionIndex = this->getIndexFromInstr(instruction);
                    set<unsigned> RVPointToSet = infoIn->pointerMap[instructionIndex];
                    if (RVPointToSet.size() != 0)
                    {
                        // add RVPointToSet into pointerMap of this instruction
                        infoIn->pointerMap[index].insert(RVPointToSet.begin(), RVPointToSet.end());
                    }
                }
            }

            /*  load
                out = in U {Ri->Y | Rp -> X and X -> Y} 
                where Rp is the DFA identifier of <pointer>.*/
            if (opName == "load")
            {
                if (I->getType()->isPointerTy())
                {
                    Instruction *instruction = (Instruction *)I->getOperand(0);
                   
                    if (this->countInstructions(instruction) != 0)
                    {
                        unsigned Y = this->getIndexFromInstr(instruction);
                        
                        for (auto X : infoIn->pointerMap[Y])
                        {
                            set<unsigned> RPPointToSet = infoIn->pointerMap[X];
                            if (RPPointToSet.size() != 0)
                            {
                                // add RPPointToSet into pointerMap of this instruction
                                infoIn->pointerMap[index].insert(RPPointToSet.begin(), RPPointToSet.end());
                            }
                        }
                    }
                }
            }

            /*  store
                out = in U {Y->X | Rv -> X and Rp -> Y} 
                where Rv and Rp are the DFA identifiers of <value> and <pointer>, respectively.*/
            if (opName == "store")
            {
                Instruction *VInstr = (Instruction *)I->getOperand(0);
                Instruction *PInstr = (Instruction *)I->getOperand(1);
                // no duplicated instruction
                if (this->countInstructions(VInstr) != 0 && this->countInstructions(PInstr) != 0)
                {
                    unsigned VIndex = this->getIndexFromInstr(VInstr);
                    unsigned PIndex = this->getIndexFromInstr(PInstr);
                    auto RVPointToSet = infoIn->pointerMap[VIndex];

                    if (RVPointToSet.size() != 0)
                    {
                        for (auto Y : infoIn->pointerMap[PIndex])
                        {
                            // add RVPointToSet into pointerMap of Y
                            infoIn->pointerMap[Y].insert(RVPointToSet.begin(), RVPointToSet.end());
                        }
                    }
                }
            }

            /*  select
                out = in U {Ri->X | R1 -> X } U {Ri->X | R2 -> X }
                where R1 and R2 are the DFA identifiers of <val1> and <val2>, respectively.*/
            if (opName == "select")
            {
                Instruction *operand1 = (Instruction *)I->getOperand(1);
                Instruction *operand2 = (Instruction *)I->getOperand(2);

                // add both R1PointToSet and R2PointToSet into pointerMap of this instruction
                if (this->countInstructions(operand1) != 0)
                {
                    unsigned operand1_index = this->getIndexFromInstr(operand1);
                    auto R1PointToSet = infoIn->pointerMap[operand1_index];
                    if (R1PointToSet.size() != 0)
                    {
                        infoIn->pointerMap[index].insert(R1PointToSet.begin(), R1PointToSet.end());
                    }
                }
                if (this->countInstructions(operand2) != 0)
                {
                    unsigned operand2_index = this->getIndexFromInstr(operand2);
                    auto R2PointToSet = infoIn->pointerMap[operand2_index];
                    if (!R2PointToSet.size() != 0)
                    {
                        infoIn->pointerMap[index].insert(R2PointToSet.begin(), R2PointToSet.end());
                    }
                }
            }

            /*  phi
                out = in U {Ri->X | R0 -> X } U ... U {Ri->X | Rk -> X }
                where R0 through Rk are the DFA identifiers of <val0> through <valk>, respectively. 
                This is the flow function for one phi instruction. 
            */
            if (opName == "phi")
            {
                //find the ending of phi by finding the first non phi
                Instruction *firstNonPhi = I->getParent()->getFirstNonPHI();
                unsigned FirstNonPhiIndex = this->getIndexFromInstr(firstNonPhi);
                
                //traverse from first phi to the first nonPhi
                for (unsigned phiIndex = index; phiIndex < FirstNonPhiIndex; phiIndex++)
                {
                    Instruction *instr_phi = this->getInstrFromIndex(phiIndex);
                
                    //traverse all the k phi instructions and add all kth phi instruction into pointerMap
                    for (unsigned k = 0; k < instr_phi->getNumOperands(); k++)
                    {
                        Instruction *kthInstruction = (Instruction *)instr_phi->getOperand(k);
                        //check no duplication                        
                        if (this->countInstructions(kthInstruction) != 0)
                        {
                            unsigned kthIndex = this->getIndexFromInstr(kthInstruction);
                            auto kPhiPointToSet = infoIn->pointerMap[kthIndex];
                            if (kPhiPointToSet.size() != 0)
                            {   
                                infoIn->pointerMap[index].insert(kPhiPointToSet.begin(), kPhiPointToSet.end());
                            }
                        }
                    }
                }
            }

            // Step3: Add result to outgoing edges
            for (unsigned i = 0; i < Infos.size(); i++)
            {
                Infos[i]->pointerMap = infoIn->pointerMap;
            }

            delete infoIn;
        }
    };

    struct MayPointToAnalysisPass : public FunctionPass
    {
        static char ID;

        MayPointToAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override
        {
            MayPointToInfo bot;
            MayPointToAnalysis mpta(bot, bot);
            mpta.runWorklistAlgorithm(&F);
            mpta.print();
            return false;
        }
    };
}

char MayPointToAnalysisPass::ID = 0;
static RegisterPass<MayPointToAnalysisPass> X("cse231-maypointto", "MayPointToAnalysis ",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);