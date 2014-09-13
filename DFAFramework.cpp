#include "llvm/Pass.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/PassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/ValueMap.h"
#include "llvm/Support/raw_ostream.h"
#include <map>
#include <set>
#include <ostream>
#include <fstream>
#include <iostream>

using namespace std;
using namespace llvm;

/**
 * Struct used to maintain the Analysis
 * data of a basic block. Bit(s) in the 
 * bitvectors represent(s) the Analysis of a
 * Value* in this basic block.
 */

template<class T>
class BasicBlockAnalysisData {
public:
  T* in;
  T* out;
  T* use;
  T* def;
  BasicBlock* block;

  BasicBlockAnalysisData(BasicBlock *block) {
    this->block = block;
    use = new T();
    def = new T();
    in = new T();
    out = new T();
  }

  BasicBlockAnalysisData(BasicBlock *block, int size) {
    this->block = block;
   use = new T(size);
    def = new T(size);
    in = new T(size);
    out = new T(size);
  }
};


/**
 * Struct used to maintain the Analysis
 * data of a Instruction. Bit(s) in the 
 * bitvectors represent(s) the Analysis of a
 * Value* in this Instruction.
 */

template<class T>
class InstructionAnalysisData {
public:
  T* in;
  T* out;
  T* use;
  T* def;
  Value* block;

  InstructionAnalysisData(Value* block) {
    this->block = block;
    use = new T();
    def = new T();
    in = new T();
    out = new T();
  }

  InstructionAnalysisData(Value* block, int size) {
    this->block = block;
    use = new T(size);
    def = new T(size);
    in = new T(size);
    out = new T(size);
  }
};



template<class T>
class DFAFramework{
public:
  bool direction; //forward analysis if true
  bool verbose;

  /**
   * Maintains the index of every value in the program.
   * This map is used to set/reset the right bits representing
   * the values in the bit vectors used for analysis.
   */
  ValueMap<Value *, int> valueIndexMap;
  /**
   * Map that is used to maintain a map between 
   * the basic block pointers and the flow
   * data corresponding to the basic block.
   */
  ValueMap<BasicBlock*, BasicBlockAnalysisData<T>*> blockFlowDataMap;
  /**
   * Map that is used to maintain a map between 
   * the instruction pointers (might be instrucions
   * or arugments) and the flow
   * data corresponding to the instruction.
   */
  ValueMap<Value*, InstructionAnalysisData<T>*> instructionFlowDataMap;
  /**
   * The mask that stores values to deal PHINodes
   * specially. This mask will be populated initially
   * before the analysis and used while doing DFA to 
   * obtain proper results.
   */
  map<pair<BasicBlock *, BasicBlock *>, T*> phiNodeMask;



  DFAFramework(bool dir){
    direction = dir;
  }
  
  //modifies the appropriate set based on the direction of analysis
  virtual void transferFunction(BasicBlock* block) = 0; 
  //meets the in set or out set based on whats needed
  virtual void meet(BasicBlock* block) = 0;
  //sets the initial flow values
  virtual void setInitialFlowValues() = 0;
  //sets any boundary conditions needed to taken care of
  virtual void setBoundaryConditions() = 0;
  //print values in a specific format
  virtual void printValuesInFormat() = 0;

  void analyze(Function &F){
    valueIndexMap.clear();
    blockFlowDataMap.clear();
    instructionFlowDataMap.clear();
    phiNodeMask.clear();

      initializeValueIndexMap(valueIndexMap,F);
      initializeBlockFlowDataMap(blockFlowDataMap,valueIndexMap.size(),F);      
      initializeInstructionFlowDataMap(instructionFlowDataMap,valueIndexMap.size(),F);      
      initializeBlockDefs(blockFlowDataMap,valueIndexMap,F);
      initializeBlockUses(blockFlowDataMap,valueIndexMap,F);
      initializePHINodeMaskValues(phiNodeMask,blockFlowDataMap,valueIndexMap,F);
      initializeInstructionDefs(instructionFlowDataMap,valueIndexMap,F);
      initializeInstructionUses(instructionFlowDataMap,valueIndexMap,F);

      setInitialFlowValues();
      set<BasicBlock*> workList;
      //value is initialized based on forward or backward analysis
      if(!direction){
	workList.insert(--(F.end()));
      }else{
	workList.insert(F.begin());
      }

      while(workList.size() > 0){
	BasicBlock* block = *(workList.begin());
	workList.erase(workList.begin()); //remove the block being processed
	meet(block);
	// in[Block] = use[Block] U (out[Block] - def[Block])
	T   prevValue = *(blockFlowDataMap[block]->out);
	if(!direction){
	  prevValue = *(blockFlowDataMap[block]->in);
	}

	transferFunction(block);
	if(!direction){
	  if (*(blockFlowDataMap[block]->in) != prevValue) {
	    // block has changed, add all its predecessors to the work list.
	    for (pred_iterator PI = pred_begin(block), E = pred_end(block); PI != E; ++PI) {
	      BasicBlock* pred = *PI;
	      set<BasicBlock*>::iterator workListIterator = workList.find(pred);
	      if (workListIterator == workList.end()) {
		workList.insert(pred);
	      }
	    }
	  }
	}else{
	  if (*(blockFlowDataMap[block]->out) != prevValue) {
	    // block has changed, add all its successors to the work list.
	    for (succ_iterator next = succ_begin(block),nexte = succ_end(block); next != nexte; next++) {	
	      BasicBlock* succ = *next;
	      set<BasicBlock*>::iterator workListIterator = workList.find(succ);
	      if (workListIterator == workList.end()) {
		workList.insert(succ);
	      }
	    }
	  }
	}
	
      }
      //push results to instruction level
      pushResultsFromBlockToInstructions(blockFlowDataMap,instructionFlowDataMap);
  }


    ////////////////////////////////////// API for Debugging ///////////////////////////////


    /**
     * Helper method used to print flow 
     * value for debug purposes.
     * 
     * bv - the pointer to the flow value 
     *      that needs to be printed
     * newLine - the boolean which decides
     *           if a new line has to be printed
     *          after printing the bit vector.
     */
  virtual void printFlowValue(T *bv, bool newLine) = 0;

  virtual  void pushResultsFromBlockToInstructions(ValueMap<BasicBlock*, BasicBlockAnalysisData<T>*> &blockFlowDataMap,ValueMap<Value*, InstructionAnalysisData<T>*> &instructionFlowDataMap) =0;

    /**
     * Iterate through the instruction flow
     * data map and print flow data for
     * every instruction.
     */
  void printInstructionFlowDataMap(ValueMap<Value*, InstructionAnalysisData<T>*> &instructionFlowDataMap){
      errs() << "\n" << "-- Instruction Flow Data map --" << "\n";
      for (typename ValueMap<Value*, InstructionAnalysisData<T>*>::iterator it = instructionFlowDataMap.begin(), ite = instructionFlowDataMap.end(); it != ite; it++) {
	errs() << *(it->first) << "\n";
	errs() << "Use : ";
	printFlowValue(it->second->use,true);
	errs() << "Def : ";
	printFlowValue(it->second->def,true);
	errs() << "In : ";
	printFlowValue(it->second->in,true);
	errs() << "Out : ";
	printFlowValue(it->second->out,true);
      }
      errs() << "\n";
  }



    /**
     * Iterate through the block flow
     * data map and print flow data for
     * every block.
     */
    void printBlockFlowDataMap(ValueMap<BasicBlock*, BasicBlockAnalysisData<T>*> &blockFlowDataMap){
      errs() << "\n" << "-- Block Flow Data map --" << "\n";
      for (typename ValueMap<BasicBlock*, BasicBlockAnalysisData<T>*>::iterator it = blockFlowDataMap.begin(), ite = blockFlowDataMap.end(); it != ite; it++) {
	errs() << *(it->first) << "\n";
	errs() << "Use : ";
	printFlowValue(it->second->use,true);
	errs() << "Def : ";
	printFlowValue(it->second->def,true);
	errs() << "In : ";
	printFlowValue(it->second->in,true);
	errs() << "Out : ";
	printFlowValue(it->second->out,true);
      }
      errs() << "\n";
    }
  

    /**
     * Iterate through the index value map
     * and print its contents for debugging
     * purposes.
     */

    void printIndexValueMap(ValueMap<Value *, int> &valueIndexMap){
      errs() << "\n" << "-- Value index map --" << "\n";
      for (ValueMap<Value*, int>::iterator it = valueIndexMap.begin(), ite = valueIndexMap.end(); it != ite; it++) {
	errs() << "Inst : " << *(it->first) <<"   Value : " << it->second << "\n";
      }
      errs() << "\n";
    }


    void printPHINodeMaskValues(map<pair<BasicBlock *, BasicBlock *>, T*> &phiNodeMask){
      errs() << "\n" << "-- Phi Node Mask Values --" << "\n";
      for (typename map<pair<BasicBlock *, BasicBlock *>, T*>::iterator it = phiNodeMask.begin(), ite = phiNodeMask.end(); it != ite; it++) {
	errs() << "Block One : " << *(it->first.first) << "\n";
	errs() << "Block Two : " << *(it->first.second) << "\n";
	errs() << "Mask : ";
	printFlowValue(it->second,true);
      }
    }

  virtual void initializePHINodeMaskValues(map<pair<BasicBlock*, BasicBlock*>, T*> &phiNodeMask,ValueMap<BasicBlock*, BasicBlockAnalysisData<T>*> &blockFlowDataMap,ValueMap<Value *, int> &valueIndexMap,Function &F) = 0;


    //////////////////////////////////// API for doing liveness Analysis ////////////////////

    /**
     * Initialize the value index map
     * by assgning an index to each value
     * in the program. This way we can use
     * these indices to keep track of flow data
     * in bit vectors.
     * 
     */
    void initializeValueIndexMap(ValueMap<Value *, int> &valueIndexMap, Function &F) {
      int count = 0;
      // Arguments count as definitions as well
      for (Function::arg_iterator arg = F.arg_begin(),arge = F.arg_end();arg !=arge; arg++) {
	valueIndexMap.insert(std::make_pair(&*arg, count));
	count++;
      }
      // There might be instructions which dont really use/def anything. We will
      // just don't care about them as we are not really running short on space
      for (inst_iterator inst = inst_begin(F),inste = inst_end(F);inst !=inste; inst++) {
	valueIndexMap.insert(std::make_pair(&*inst, count));
	count++;
      }
    }
    //;;;;;;;;;;;;;;;;;;;;;;; Methods for Instruction flow data ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    /**
     * Iterates through the Instructions of 
     * the given function, creates new 
     * analysis datablocks for the Ins and 
     * puts them in the map.
     *
     * vectorSize - the number of bits for which
     * the bitvectors in the analysis data object 
     * should be created.
     */
  void initializeInstructionFlowDataMap(ValueMap<Value*, InstructionAnalysisData<T>*> &instructionFlowDataMap, int vectorSize, Function &F) {
      //Put the arguments in the instruction flow data map
      for (Function::arg_iterator arg = F.arg_begin(),arge = F.arg_end();arg !=arge; arg++) {
	InstructionAnalysisData<T> *info = new InstructionAnalysisData<T>(&*arg, vectorSize);
	  instructionFlowDataMap.insert(std::make_pair(&*arg, info));
      }

      for (Function::iterator b = F.begin(), be = F.end(); b != be; b++) {
	BasicBlock *block = &*b;
	for (BasicBlock::iterator inst = block->begin(), inste = block->end(); inst != inste; inst++){
	  InstructionAnalysisData<T> *info = new InstructionAnalysisData<T>(&*inst, vectorSize);
	  instructionFlowDataMap.insert(std::make_pair(&*inst, info));
	}
      }
    }


    /**
     * Initialize the defs of the analysis
     * instruction  in the instruction flow datamap.
     */
  void initializeInstructionDefs(ValueMap<Value*, InstructionAnalysisData<T>*> &instructionFlowDataMap,ValueMap<Value *, int> &valueIndexMap, Function &F){
    for (typename ValueMap<Value*, InstructionAnalysisData<T>*>::iterator it = instructionFlowDataMap.begin(), ite = instructionFlowDataMap.end(); it != ite; it++) {
	  it->second->def->set(valueIndexMap[it->first]);
      }
    }


    /**
     * Initialize the uses of the analysis
     * instructions in the instruction flow datamap.
     */
  void initializeInstructionUses(ValueMap<Value*, InstructionAnalysisData<T>*> &instructionFlowDataMap,ValueMap<Value *, int> &valueIndexMap,Function &F) {
    for (typename ValueMap<Value*, InstructionAnalysisData<T>*>::iterator it = instructionFlowDataMap.begin(), ite = instructionFlowDataMap.end(); it != ite; it++) {
	if(Instruction *inst = dyn_cast<Instruction>(it->first)){
	  for (User::op_iterator OI = (inst)->op_begin(), OE = (inst)->op_end(); OI != OE; ++OI){
	    Value *val = *OI;
	    if(isa<Instruction>(val) || isa<Argument>(val)) {
	      instructionFlowDataMap[it->first]->use->set(valueIndexMap[val]);
	    }
	  }
	}
      }
    }



    //;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    //;;;;;;;;;;;;;;;;;;;;;;; Methods for basic block flow data ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    /**
     * Iterates through the basic blocks of 
     * the given function, creates new 
     * analysis datablocks for the BBs and 
     * puts them in the map.
     *
     * vectorSize - the number of bits for which
     * the bitvectors in the analysis data object 
     * should be created.
     */
  void initializeBlockFlowDataMap(ValueMap<BasicBlock*, BasicBlockAnalysisData<T>*> &blockFlowDataMap, int vectorSize, Function &F) {
      for (Function::iterator b = F.begin(), be = F.end(); b != be; b++) {
	BasicBlockAnalysisData<T> *info = new BasicBlockAnalysisData<T>(&*b, vectorSize);
	blockFlowDataMap.insert(std::make_pair(b, info));
      }
    }
    
    /**
     * Initialize the defs of the analysis
     * data blocks in the block flow datamap.
     */
  void initializeBlockDefs(ValueMap<BasicBlock*, BasicBlockAnalysisData<T>*> &blockFlowDataMap,ValueMap<Value *, int> &valueIndexMap, Function &F){
      // initialize the defs for the function arguments
      for (Function::arg_iterator arg = F.arg_begin(),arge = F.arg_end();arg !=arge; arg++) {
	blockFlowDataMap[F.begin()]->def->set(valueIndexMap[&*arg]);
      }

      for (typename ValueMap<BasicBlock*, BasicBlockAnalysisData<T>*>::iterator it = blockFlowDataMap.begin(), ite = blockFlowDataMap.end(); it != ite; it++) {
	BasicBlock *block = it->second->block;
	for (BasicBlock::iterator inst = block->begin(), inste = block->end(); inst != inste; inst++){
	  it->second->def->set(valueIndexMap[inst]);
	}
      }
    }

    /**
     * Initialize the uses of the analysisp
     * data blocks in the block flow datamap.
     */
  void initializeBlockUses(ValueMap<BasicBlock*, BasicBlockAnalysisData<T>*> &blockFlowDataMap,ValueMap<Value *, int> &valueIndexMap,Function &F) {
      for (inst_iterator i = inst_begin(F), e = inst_end(F); i!=e; i++) {
	Instruction* inst = &*i;
	markUsesForGivenInstruction(blockFlowDataMap,inst,valueIndexMap);
      }
      for (Function::arg_iterator a = F.arg_begin(), e = F.arg_end(); a!=e; a++) {
	  Value *val = &*a;
	  if(isa<Instruction>(val) || isa<Argument>(val)) {
	    BasicBlock* parentBlock = F.begin();
	    blockFlowDataMap[parentBlock]->use->set(valueIndexMap[val]);
	  }
      }
    }

    /**
     * Helper method to mark the uses 
     * for a single instruction.
     */
void markUsesForGivenInstruction(ValueMap<BasicBlock*, BasicBlockAnalysisData<T>*> &blockFlowDataMap,Instruction *i,ValueMap<Value *, int> &valueIndexMap) {
      if(Instruction *inst = dyn_cast<Instruction>(&*i)){
	for (User::op_iterator OI = (inst)->op_begin(), OE = (inst)->op_end(); OI != OE; ++OI){
	  Value *val = *OI;
	  if(isa<Instruction>(val) || isa<Argument>(val)) {
	    BasicBlock* parentBlock = inst->getParent();
	    blockFlowDataMap[parentBlock]->use->set(valueIndexMap[val]);
	  }
	}
      }
    }

    //;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



  
};


