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
#include "llvm/Support/FormattedStream.h"
#include "llvm/Assembly/AssemblyAnnotationWriter.h"
#include "llvm/DebugInfo.h"
#include "DFAFramework.cpp"
#include <map>
#include <set>
#include <ostream>
#include <fstream>
#include <iostream>

using namespace llvm;
using namespace std;

namespace {


  class Annotator : public AssemblyAnnotationWriter {
  public:
    ValueMap<BasicBlock*, BasicBlockAnalysisData<BitVector>*> &blockFlowDataMap;
    ValueMap<Value*, InstructionAnalysisData<BitVector>*> &instructionFlowDataMap;
    ValueMap<Value*,int> &valueMap;

    Annotator(ValueMap<BasicBlock*, BasicBlockAnalysisData<BitVector>*> &bl,   ValueMap<Value*, InstructionAnalysisData<BitVector>*> &im, ValueMap<Value*,int> &vm) : blockFlowDataMap(bl), instructionFlowDataMap(im), valueMap(vm){
    }

  virtual void emitBasicBlockStartAnnot(const BasicBlock *bb, formatted_raw_ostream &os) {
    os << "; ";
    for (ValueMap<BasicBlock*, BasicBlockAnalysisData<BitVector>*>::iterator it = blockFlowDataMap.begin(), ite = blockFlowDataMap.end(); it != ite; it++) {
      if(bb->getName() == it->first->getName()){
	for (unsigned bit = 0; bit < it->second->in->size(); bit++){
	  if(it->second->in->test(bit) == true){
	    for (ValueMap<Value*,int>::iterator it1 = valueMap.begin(), it1e = valueMap.end(); it1 != it1e; it1++) {
	      if(it1->second == bit)
		os << it1->first->getName() << ", ";
	    }
	  }
	}
	break;
      }
    }
 os << "\n";
  }

    virtual void emitInstructionAnnot(const Instruction *i, formatted_raw_ostream &os) {
      os << "; ";

      for (ValueMap<Value*, InstructionAnalysisData<BitVector>*>::iterator it = instructionFlowDataMap.begin(), ite = instructionFlowDataMap.end(); it != ite; it++) {
	if(Instruction* ins = dyn_cast<Instruction>(it->first)){
	  if(ins->isIdenticalTo(i)){
	    for (unsigned bit = 0; bit < it->second->in->size(); bit++){
	      if(it->second->in->test(bit) == true){
		for (ValueMap<Value*,int>::iterator it1 = valueMap.begin(), it1e = valueMap.end(); it1 != it1e; it1++) {
		  if(it1->second == bit)
		    os << it1->first->getName() << ", ";
		}
	      }
	    }
	    break;
	  }
	}
      }
      os << "\n";
    }

  };


  class FunctionInfo : public FunctionPass, public DFAFramework<BitVector> {

  public:
    static char ID;
    FunctionInfo() : FunctionPass(ID), DFAFramework(false){}

    //modifies the appropriate set based on the direction of analysis
    virtual void transferFunction(BasicBlock* block){
	BitVector outDefDiff = *(blockFlowDataMap[block]->def);
	outDefDiff.flip();
	outDefDiff &= *(blockFlowDataMap[block]->out);
	BitVector newInBlock = *(blockFlowDataMap[block]->use);
	newInBlock |= outDefDiff;
	*(blockFlowDataMap[block]->in) = newInBlock;
}
    //meets the in set or out set based on whats needed
    virtual void meet(BasicBlock* block){
	(blockFlowDataMap[block]->out)->reset();
	for (succ_iterator next = succ_begin(block),nexte = succ_end(block); next != nexte; next++) {
	  BasicBlock* succ = *next;
	  pair<BasicBlock *, BasicBlock *> phiKey= make_pair(block, succ);
	  if (phiNodeMask.find(phiKey) != phiNodeMask.end()) {
	    BitVector maskedInClone = *(blockFlowDataMap[succ]->in);
	    maskedInClone &= *(phiNodeMask[phiKey]); 
	    *(blockFlowDataMap[block]->out) |= maskedInClone;
	  } else {
	    *(blockFlowDataMap[block]->out) |= *(blockFlowDataMap[succ]->in);
	  }
	}
}


    //sets the initial flow values
    virtual void setInitialFlowValues(){
    }
    //sets any boundary conditions needed to taken care of
    virtual void setBoundaryConditions(){}

    virtual void printFlowValue(BitVector *bv, bool newLine) {
      for (unsigned bit = 0; bit < bv->size(); bit++)
	errs() << (bv->test(bit) ? '1' : '0');
      if(newLine) errs() << "\n";
    }

    virtual void printValuesInFormat(){
      //print here once analysis is done
	printIndexValueMap(valueIndexMap);
	printInstructionFlowDataMap(instructionFlowDataMap);
	//printBlockFlowDataMap(blockFlowDataMap);
	//printPHINodeMaskValues(phiNodeMask);
    }

    virtual bool runOnFunction(Function  &F){
      analyze(F);
      //printValuesInFormat();
      Annotator anno(blockFlowDataMap,instructionFlowDataMap,valueIndexMap);
      F.print(errs(),&anno);
      return false;
    }



    /**
     * Initializes the phi node mask 
     * values by creating pair of 
     * incoming and phi node containing
     * blocks to be used while propagating
     * flow values forward/backward.
     */
void initializePHINodeMaskValues(map<pair<BasicBlock*, BasicBlock*>, BitVector*> &phiNodeMask,ValueMap<BasicBlock*, BasicBlockAnalysisData<BitVector>*> &blockFlowDataMap,ValueMap<Value *, int> &valueIndexMap,Function &F) {
      for (inst_iterator i = inst_begin(F), e = inst_end(F); i!=e; i++) {
	if (!isa<PHINode>(&*i)) continue;
	PHINode *phiNode = dyn_cast<PHINode>(&*i);
	BasicBlock *phiBlock = phiNode->getParent();
	for (int innerIndex = 0; innerIndex < phiNode->getNumIncomingValues(); innerIndex++) {
	  BasicBlock *innerBlock = phiNode->getIncomingBlock(innerIndex);
	  for (int outerIndex = 0; outerIndex < phiNode->getNumIncomingValues(); outerIndex++) {
	    // should continue if the blocks are the same as we shouldn't omit its value
	    if (innerIndex == outerIndex) continue;
	    Value *outerValue = phiNode->getIncomingValue(outerIndex);
	    int outerIndex = valueIndexMap[outerValue];
	    std::pair<BasicBlock*, BasicBlock*> blockPair = std::make_pair(innerBlock, phiBlock);
	    std::map<std::pair<BasicBlock *, BasicBlock *>, BitVector*>::iterator maskIterator = phiNodeMask.find(blockPair);
	    if (maskIterator == phiNodeMask.end()) {
	      phiNodeMask[blockPair] =  new BitVector(valueIndexMap.size(), true);
	    }
	    phiNodeMask[blockPair]->reset(outerIndex);
	  }
	}
      }
    }



    void pushResultsFromBlockToInstructions(ValueMap<BasicBlock*, BasicBlockAnalysisData<BitVector>*> &blockFlowDataMap,ValueMap<Value*, InstructionAnalysisData<BitVector>*> &instructionFlowDataMap) {
      for (ValueMap<BasicBlock*, BasicBlockAnalysisData<BitVector>*>::iterator it = blockFlowDataMap.begin(), ite = blockFlowDataMap.end(); it != ite; it++) {
	BasicBlock* B = dyn_cast<BasicBlock>(it->first);
	Instruction* prev = NULL;
	for (BasicBlock::reverse_iterator I = B->rbegin(), Ie = B->rend(); I != Ie; ++I){
	  Instruction *inst = dyn_cast<Instruction>(&*I);
	  InstructionAnalysisData<BitVector>* insData = instructionFlowDataMap[&*I]; 
	  if(prev == NULL){
	    insData->out = it->second->out;
	  }else{
	    insData->out = instructionFlowDataMap[prev]->in;
	  }
	  // in[Block] = use[Block] U (out[Block] - def[Block])
	  BitVector outDefDiff = *(insData->def);
	  outDefDiff.flip();
	  outDefDiff &= *(insData->out);
	  BitVector newInBlock = *(insData->use);
	  newInBlock |= outDefDiff;
	  *(insData->in) = newInBlock;
	  //make the prev to the current instruction
	  prev = inst;
	}
	prev = NULL;
      }
    }    

  };



//Register the pass and set the ID  
char FunctionInfo::ID = 0;
RegisterPass<FunctionInfo> X("live", "Function Information");

}

