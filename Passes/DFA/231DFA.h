//===- CSE231.h - Header for CSE 231 projects ----------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file provides the interface for the passes of CSE 231 projects
//
//===----------------------------------------------------------------------===//
/*	Part 2.1
	Implement a generic intra-procedural dataflow analysis framework. 
	We provide an incomplete base template class class DataFlowAnalysis in 231DFA.h. 
	To create a dataflow analysis based on the base class DataFlowAnalysis, you need to provide:
		class Info: the class that represents the information at each program point;
		bool Direction: the direction of analysis. If it is true, then the analysis is a forward analysis; otherwise it is a backward analysis.
		Info InitialState: the initial state of the analysis.
		Info Bottom: the bottom of the lattice.

	You need to implement class DataFlowAnalysis in 231DFA.h so that it performs a forward analysis. 
	We provide most of the code for forward analysis in class DataFlowAnalysis. 
	You only need to implement the worklist algorithm in function runWorklistAlgorithm.
*/

#ifndef LLVM_TRANSFORMS_231DFA_H
#define LLVM_TRANSFORMS_231DFA_H

#include "llvm/InitializePasses.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include <deque>
#include <map>
#include <utility>
#include <vector>

using namespace std;

namespace llvm {
/*
 * This is the base class to represent information in a dataflow analysis.
 * For a specific analysis, you need to create a sublcass of it.
 */
class Info {
  public:
    Info() {}
    Info(const Info& other) {}
    virtual ~Info() {};

    /*
     * Print out the information
     *
     * Direction:
     *   In your subclass you should implement this function according to the project specifications.
     */
    virtual void print() = 0;

    /*
     * Compare two pieces of information
     *
     * Direction:
     *   In your subclass you need to implement this function.
     */
    static bool equals(Info * info1, Info * info2);
    
	/*
     * Join two pieces of information.
     * The third parameter points to the result.
     *
     * Direction:
     *   In your subclass you need to implement this function.
     */
    static Info* join(Info * info1, Info * info2, Info * result);
};

/*
 * This is the base template class to represent the generic dataflow analysis framework
 * For a specific analysis, you need to create a sublcass of it.
 */
template <class Info, bool Direction>
class DataFlowAnalysis {

    private:
		typedef std::pair<unsigned, unsigned> Edge;
		// Index to instruction map
		std::map<unsigned, Instruction *> IndexToInstr;
		// Instruction to index map
		std::map<Instruction *, unsigned> InstrToIndex;
		// Edge to information map
		std::map<Edge, Info *> EdgeToInfo;
		// The bottom of the lattice
		Info Bottom;
		// The initial state of the analysis
		Info InitialState;
		// EntryInstr points to the first instruction to be processed in the analysis
		Instruction * EntryInstr;

		/*
		 * Assign an index to each instruction.
		 * The results are stored in InstrToIndex and IndexToInstr.
		 * A dummy node (nullptr) is added. It has index 0. This node has only one outgoing edge to EntryInstr.
		 * The information of this edge is InitialState.
		 * Any real instruction has an index > 0.
		 *
		 * Direction:
		 *   Do *NOT* change this function.
		 *   Both forward and backward analyses must use it to assign
		 *   indices to the instructions of a function.
		 */
		void assignIndiceToInstrs(Function * F) {

			// Dummy instruction null has index 0;
			// Any real instruction's index > 0.
			InstrToIndex[nullptr] = 0;
			IndexToInstr[0] = nullptr;

			unsigned counter = 1;
			for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
				Instruction * instr = &*I;
				InstrToIndex[instr] = counter;
				IndexToInstr[counter] = instr;
				counter++;
			}

			return;
		}

		/*
		 * Utility function:
		 *   Get incoming edges of the instruction identified by index.
		 *   IncomingEdges stores the indices of the source instructions of the incoming edges.
		 */
		void getIncomingEdges(unsigned index, std::vector<unsigned> * IncomingEdges) {
			assert(IncomingEdges->size() == 0 && "IncomingEdges should be empty.");

			for (auto const &it : EdgeToInfo) {
				if (it.first.second == index)
					IncomingEdges->push_back(it.first.first);
			}

			return;
		}

		/*
		 * Utility function:
		 *   Get incoming edges of the instruction identified by index.
		 *   OutgoingEdges stores the indices of the destination instructions of the outgoing edges.
		 */
		void getOutgoingEdges(unsigned index, std::vector<unsigned> * OutgoingEdges) {
			assert(OutgoingEdges->size() == 0 && "OutgoingEdges should be empty.");

			for (auto const &it : EdgeToInfo) {
				if (it.first.first == index)
					OutgoingEdges->push_back(it.first.second);
			}

			return;
		}

		/*
		 * Utility function:
		 *   Insert an edge to EdgeToInfo.
		 *   The default initial value for each edge is bottom.
		 */
		void addEdge(Instruction * src, Instruction * dst, Info * content) {
			Edge edge = std::make_pair(InstrToIndex[src], InstrToIndex[dst]);
			if (EdgeToInfo.count(edge) == 0)
				EdgeToInfo[edge] = content;
			return;
		}

		/*
		 * Initialize EdgeToInfo and EntryInstr for a forward analysis.
		 */
		void initializeForwardMap(Function * func) {
			assignIndiceToInstrs(func);

			for (Function::iterator bi = func->begin(), e = func->end(); bi != e; ++bi) {
				BasicBlock * block = &*bi;

				Instruction * firstInstr = &(block->front());

				// Initialize incoming edges to the basic block
				for (auto pi = pred_begin(block), pe = pred_end(block); pi != pe; ++pi) {
					BasicBlock * prev = *pi;
					Instruction * src = (Instruction *)prev->getTerminator();
					Instruction * dst = firstInstr;
					addEdge(src, dst, &Bottom);
				}

				// If there is at least one phi node, add an edge from the first phi node
				// to the first non-phi node instruction in the basic block.
				if (isa<PHINode>(firstInstr)) {
					addEdge(firstInstr, block->getFirstNonPHI(), &Bottom);
				}

				// Initialize edges within the basic block
				for (auto ii = block->begin(), ie = block->end(); ii != ie; ++ii) {
					Instruction * instr = &*ii;
					if (isa<PHINode>(instr))
						continue;
					if (instr == (Instruction *)block->getTerminator())
						break;
					Instruction * next = instr->getNextNode();
					addEdge(instr, next, &Bottom);
				}

				// Initialize outgoing edges of the basic block
				Instruction * term = (Instruction *)block->getTerminator();
				for (auto si = succ_begin(block), se = succ_end(block); si != se; ++si) {
					BasicBlock * succ = *si;
					Instruction * next = &(succ->front());
					addEdge(term, next, &Bottom);
				}

			}

			EntryInstr = (Instruction *) &((func->front()).front());
			addEdge(nullptr, EntryInstr, &InitialState);

			return;
		}

		/*
		 * Direction:
		 *   Implement the following function in part 3 for backward analyses
		 *
		 *	Reuse code from initializeForwardMap() but changing direction of src and dst
		 *  implement 
		 */
		void initializeBackwardMap(Function * func) {
			assignIndiceToInstrs(func);

            for (Function::iterator bi = func->begin(), e = func->end(); bi != e; ++bi) {
                BasicBlock * block = &*bi;

                Instruction * firstInstr = &(block->front());

                // Initialize incoming edges to the basic block
                for (auto pi = pred_begin(block), pe = pred_end(block); pi != pe; ++pi) {
                    BasicBlock * prev = *pi;
                    Instruction * src = firstInstr;
                    Instruction * dst = (Instruction *)prev->getTerminator();
                    addEdge(src, dst, &Bottom);
                }

                // If there is at least one phi node, add an edge from the first phi node
                // to the first non-phi node instruction in the basic block.
                if (isa<PHINode>(firstInstr)) {
                    addEdge(block->getFirstNonPHI(), firstInstr,  &Bottom);
                }

                // Initialize edges within the basic block
                for (auto ii = block->begin(), ie = block->end(); ii != ie; ++ii) {
                    Instruction * instr = &*ii;
                    if (isa<PHINode>(instr))
                        continue;
                    if (instr == (Instruction *)block->getTerminator())
                        break;
                    Instruction * next = instr->getNextNode();
                    addEdge(next, instr, &Bottom);
                }

                // Initialize outgoing edges of the basic block
                Instruction * term = (Instruction *)block->getTerminator();
                for (auto si = succ_begin(block), se = succ_end(block); si != se; ++si) {
                    BasicBlock * succ = *si;
                    Instruction * next = &(succ->front());
                    addEdge(next, term, &Bottom);
                }

                // multi ret operator
                Instruction * ProbableEntryInstr = (Instruction *) &(block->back());
                if((std::string) (ProbableEntryInstr->getOpcodeName()) == "ret"){
                    addEdge(nullptr, ProbableEntryInstr, &InitialState);
                }
            }

            EntryInstr = (Instruction *) &((func->back()).back());
            return;
        }

    /*
     * The flow function.
     *   Instruction I: the IR instruction to be processed.
     *   std::vector<unsigned> & IncomingEdges: the vector of the indices of the source instructions of the incoming edges.
     *   std::vector<unsigned> & IncomingEdges: the vector of indices of the source instructions of the outgoing edges.
     *   std::vector<Info *> & Infos: the vector of the newly computed information for each outgoing eages.
     *
     * Direction:
     * 	 Implement this function in subclasses.
     */
    virtual void flowfunction(	Instruction * I, std::vector<unsigned> & IncomingEdges,
								std::vector<unsigned> & OutgoingEdges, std::vector<Info *> & Infos) = 0;

  public:
    DataFlowAnalysis(Info & bottom, Info & initialState) :
    								 Bottom(bottom), InitialState(initialState),EntryInstr(nullptr) {}

    virtual ~DataFlowAnalysis() {}

	//############################################################
	// getter methods
	//############################################################
	unsigned getIndexFromInstr(Instruction* I){
		return this->InstrToIndex[I];
	}

	Info* getInfoFromEdge(Edge edge){
		return this->EdgeToInfo[edge];
	}

	unsigned countInstructions(Instruction* I){
		return this->InstrToIndex.count(I);
	}

	Instruction* getInstrFromIndex(unsigned index){
		return this->IndexToInstr[index];
	}
	
    /*
     * Print out the analysis results.
     *
     * Direction:
     * 	 Do not change this funciton.
     * 	 The autograder will check the output of this function.
     */
    void print() {
		for (auto const &it : EdgeToInfo) {
			errs() << "Edge " << it.first.first << "->" "Edge " << it.first.second << ":";
			(it.second)->print();
		}
    }

    /*
     * This function implements the work list algorithm in the following steps:
     * (1) Initialize info of each edge to bottom
     * (2) Initialize the worklist
     * (3) Compute until the worklist is empty
     *
     * Direction:
     *   Implement the rest of the function.
     *   You may not change anything before "// (2) Initialize the worklist".
     */
	void runWorklistAlgorithm(Function * func) {
        std::deque<unsigned> worklist;
      
	    // (1) Initialize info of each edge to bottom
        if (Direction)
            initializeForwardMap(func);
        else
            initializeBackwardMap(func);

        assert(EntryInstr != nullptr && "Entry instruction is null.");

        // (2) Initialize the work list
        for (auto iter = IndexToInstr.begin(); iter != IndexToInstr.end(); ++iter){
            if(iter->first==0){
                continue;
            }
			worklist.push_back(iter->first);
        }
		
        // (3) Compute until the work list is empty
        while (!worklist.empty()) {

			// remove any from the worklist
            unsigned index = worklist.front();
            worklist.pop_front();
            Instruction *I = IndexToInstr[index];

			// get incomingEdges and outgoingEdges
            std::vector<unsigned> incomingEdges, outgoingEdges;
			getIncomingEdges(index, &incomingEdges);
            getOutgoingEdges(index, &outgoingEdges);

            std::vector<Info *> info_out;
            for(unsigned i=0; i<outgoingEdges.size();i++){
                info_out.push_back(new Info());
            }
           
		    flowfunction(I, incomingEdges, outgoingEdges, info_out);
        
		    for(unsigned i=0;i<info_out.size();i++){
                unsigned start = index, end = outgoingEdges[i];
                Edge edge = std::make_pair(start, end);
                Info * newInfo = new Info();
                
                Info::join(EdgeToInfo[edge], info_out[i], newInfo);	//Debug fixed  join(info1, info2, res)

                if(!Info::equals(newInfo,EdgeToInfo[edge])){
                    if (EdgeToInfo[edge] != &Bottom) { 
                        delete EdgeToInfo[edge];
                    }
					//update EdgeToInfo map and  worklist 
                    EdgeToInfo[edge] = newInfo;
                    worklist.push_back(end);
                } else {
					// no need to replace anything
                    delete newInfo;
                }
            }
			
            for(unsigned i=0; i<outgoingEdges.size();i++){
                delete info_out[i];
            }
        }
    }

};

}
#endif // End LLVM_231DFA_H