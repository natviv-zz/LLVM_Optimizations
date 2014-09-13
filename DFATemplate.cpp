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

template<class T>
class  InsNode {
public:
  T* in;
  T* out;
  T* use;
  T* def;
  Value* block;

    InsNode(Value* val, int size) {
    this->block = val;
    use = new T(size);
    def = new T(size);
    in = new T(size);
    out = new T(size);
  }
};

template<class T>
class  BBNode {
public:
  T* in;
  T* out;
  T* use;
  T* def;
  BasicBlock* block;

   BBNode(BasicBlock *block, int size) {
    this->block = block;
    use = new T(size);
    def = new T(size);
    in = new T(size);
    out = new T(size);
  }
};

template<class T>
class DFATemplate{
public:
  ValueMap<BasicBlock*,BBNode<T>*> flowForBB;
  ValueMap<Value*,InsNode<T>*> flowForIns;
  ValueMap<Value *,int> mapValueToBit;
  map<pair<BasicBlock *, BasicBlock *>, T*> flowForPhiNode;
  bool direction; 

  DFATemplate(bool dir){
    direction = dir;
  }
    
  virtual void flowFunction(BasicBlock* block) = 0; 
  virtual void merge(BasicBlock* block) = 0;
 
  
  void runAnalysis(Function &F){

      allclear();

      //Map value to bit
      int count = 0;
      
      //Iterate over arguments and instruction
      for (Function::arg_iterator arg = F.arg_begin(),arge = F.arg_end();arg !=arge; arg++) 
      {
	mapValueToBit.insert(std::make_pair(&*arg, count));
	count++;
      }
      
      for (inst_iterator inst = inst_begin(F),inste = inst_end(F);inst !=inste; inst++) 
      {
	mapValueToBit.insert(std::make_pair(&*inst, count));
	count++;
      }

      int vectorSize = mapValueToBit.size();

      
      //initialize ins flow values
      for (Function::arg_iterator arg = F.arg_begin(),arge = F.arg_end();arg !=arge; arg++) 
      {
	  InsNode<T> *flowval = new InsNode<T>(&*arg, vectorSize);
	  flowForIns.insert(std::make_pair(&*arg, flowval));
      }

      //initialize BB flow values
      for (Function::iterator b = F.begin(), be = F.end(); b != be; b++) 
      {
	 BBNode<T> *flowval = new  BBNode<T>(&*b, vectorSize);
	 flowForBB.insert(std::make_pair(b, flowval));
      }


      for (Function::iterator b = F.begin(), be = F.end(); b != be; b++) 
      {
	BasicBlock *block = &*b;
	for (BasicBlock::iterator inst = block->begin(), inste = block->end(); inst != inste; inst++)
        {
	   InsNode<T> *flowval = new InsNode<T>(&*inst, vectorSize);
	  flowForIns.insert(std::make_pair(&*inst, flowval));
	}
      }


      //initialize BB defs
      
      for (Function::arg_iterator arg = F.arg_begin(),arge = F.arg_end();arg !=arge; arg++) 
      {
	flowForBB[F.begin()]->def->set(mapValueToBit[&*arg]);
      }
      
      //initialize BB uses
      for (inst_iterator i = inst_begin(F), e = inst_end(F); i!=e; i++) 
      {
	
        if(Instruction *inst = dyn_cast<Instruction>(&*i))
      {
	for (User::op_iterator OI = (inst)->op_begin(), OE = (inst)->op_end(); OI != OE; ++OI)
        {
	  Value *val = *OI;
          //errs()<<*val<<"\n";
	  if(isa<Instruction>(val) || isa<Argument>(val)) 
          {
	    BasicBlock* parentBlock = inst->getParent();
	    flowForBB[parentBlock]->use->set(mapValueToBit[val]);
	  }
	}
      }

      }


       for (typename ValueMap<BasicBlock*,  BBNode<T>*>::iterator it = flowForBB.begin(), ite = flowForBB.end(); it != ite; it++) 
      {
	BasicBlock *block = it->second->block;
	for (BasicBlock::iterator inst = block->begin(), inste = block->end(); inst != inste; inst++)
        {
	  it->second->def->set(mapValueToBit[inst]);
	}
      }
      

      for (Function::arg_iterator a = F.arg_begin(), e = F.arg_end(); a!=e; a++) 
      {
	  Value *val = &*a;
	  if(isa<Instruction>(val) || isa<Argument>(val)) 
         {
	    BasicBlock* parentBlock = F.begin();
	    flowForBB[parentBlock]->use->set(mapValueToBit[val]);
	 }
      }
    
       //Phi Node flow init here
       for (inst_iterator i = inst_begin(F), e = inst_end(F); i!=e; i++) 
       {
	//Sanity check - Remember last time error from TA
        if (!isa<PHINode>(&*i)) 
        continue;
	
        PHINode *phiNode = dyn_cast<PHINode>(&*i);
	
        BasicBlock *phiParent = phiNode->getParent();
       
	
        for (int x = 0; x < phiNode->getNumIncomingValues(); x++) 
         {
	   BasicBlock *inBlock = phiNode->getIncomingBlock(x);
	
           for (int y = 0; y < phiNode->getNumIncomingValues(); y++) 
           {
	    
	    if (x == y) 
            continue;
	    
	    std::pair<BasicBlock*, BasicBlock*> blockPair = std::make_pair(inBlock, phiParent);
	    Value *val = phiNode->getIncomingValue(y);
            int y = mapValueToBit[val];
            typename std::map<std::pair<BasicBlock *, BasicBlock *>, T*>::iterator phiFlowIterator = flowForPhiNode.find(blockPair);
	    
            if (phiFlowIterator == flowForPhiNode.end()) 
            flowForPhiNode[blockPair] =  new T(vectorSize, true);
	   
	    flowForPhiNode[blockPair]->reset(y);
	  }
	}
      }



      // initialize ins defs
      for (typename ValueMap<Value*,  InsNode<T>*>::iterator it = flowForIns.begin(), ite = flowForIns.end(); it != ite; it++) 
      {
	  it->second->def->set(mapValueToBit[it->first]);
      }

       set<BasicBlock*> bbList; 
      // Insert into worklist based on flow dir    
      if(!direction)
      {
        //errs()<<--(F.end()).getName()<<"\n";
	bbList.insert(--(F.end()));
      }
      else
      {
	bbList.insert(F.begin());
      }
      
      for (typename ValueMap<Value*,  InsNode<T>*>::iterator it = flowForIns.begin(), ite = flowForIns.end(); it != ite; it++) 
      {
	if(Instruction *inst = dyn_cast<Instruction>(it->first))
        {
	  for (User::op_iterator OI = (inst)->op_begin(), OE = (inst)->op_end(); OI != OE; ++OI)
          {
	    Value *val = *OI;
            //errs()<<*val<<"\n";
	    if(isa<Instruction>(val) || isa<Argument>(val)) 
	      flowForIns[it->first]->use->set(mapValueToBit[val]);
	    
	  }
	}
      }
     
     
      //Until worklist not empty
      while(bbList.size() > 0)
      {
	BasicBlock* block = *(bbList.begin());
	// Pop from worklist
        bbList.erase(bbList.begin()); 
	merge(block);
	
        T prevInsValue = *(flowForBB[block]->in);
	
	flowFunction(block);
	
        
	  if (*(flowForBB[block]->in) != prevInsValue) 
          {	    
	    for (pred_iterator PI = pred_begin(block), E = pred_end(block); PI != E; ++PI) 
            {
	      BasicBlock* pred = *PI;
	      set<BasicBlock*>::iterator bbListIterator = bbList.find(pred);
	      if (bbListIterator == bbList.end()) 
              {
		bbList.insert(pred);
	      }
	    }
	  
	}
        
       
	
      }

      //push results to instruction level
      //propagateFlow from BB toIns; Needs to be modified


       for (typename ValueMap<BasicBlock*,  BBNode<T>*>::iterator it = flowForBB.begin(), ite = flowForBB.end(); it != ite; it++) 
       {
	
        BasicBlock* B = dyn_cast<BasicBlock>(it->first);
        Instruction* prevIns = NULL;
        
	
	
        for (BasicBlock::reverse_iterator I = B->rbegin(), Ie = B->rend(); I != Ie; ++I){

	InsNode<T>* insData = flowForIns[&*I]; 
        Instruction *inst = dyn_cast<Instruction>(&*I);
	
	
        if(prevIns == NULL)
        {
	    *(insData->out) |= *(it->second->out);
	}
        else
        {
	    *(insData->out) |= *(flowForIns[prevIns]->in);
	}	 
	
          T bin = *(insData->use);
          T bdef = *(insData->def);
	  bdef.flip();
	  bdef &= *(insData->out);
	  
	  bin |= bdef;
	  *(insData->in) = bin;	  
	  prevIns = inst;
	}
	prevIns = NULL;
      }

  }

  void allclear()
  {
    mapValueToBit.clear();
    flowForBB.clear();
    flowForIns.clear();
    flowForPhiNode.clear();
 

  }

  
};


