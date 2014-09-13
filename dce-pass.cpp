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
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/Dominators.h"
#include "DFATemplate.cpp"
#include <map>
#include <set>
#include <ostream>
#include <fstream>
#include <iostream>
#include <vector>

using namespace llvm;
using namespace std;

namespace {

  class FunctionInfo : public FunctionPass, public DFATemplate<BitVector> {

  public:
    static char ID;
    FunctionInfo() : FunctionPass(ID), DFATemplate(false){}
    LoopInfo* LI;
    DominatorTree* DT; 
    Loop* CurrentLoop;
   
    virtual void flowFunction(BasicBlock* block)
    {
	BitVector bdef = *(flowForBB[block]->def);
	BitVector bin = *(flowForBB[block]->use);
        //Nice function for negation
        bdef.flip();
	bdef &= *(flowForBB[block]->out);
	
	bin |= bdef;
	*(flowForBB[block]->in) = bin;
    }

    virtual void merge(BasicBlock* block)
    {
	(flowForBB[block]->out)->reset();
	
	for (succ_iterator next = succ_begin(block),nexte = succ_end(block); next != nexte; next++) {
	  
          BasicBlock* succ = *next;
	  pair<BasicBlock *, BasicBlock *> phiNodePair= make_pair(block, succ);
	  
          if (flowForPhiNode.find(phiNodePair) != flowForPhiNode.end()) 
          {
	    BitVector phiFlow = *(flowForBB[succ]->in);
            phiFlow &= *(flowForPhiNode[phiNodePair]); 
	    *(flowForBB[block]->out) |= phiFlow;
	  } 
          else 
	    *(flowForBB[block]->out) |= *(flowForBB[succ]->in);
	        
	}
     }

    virtual bool runOnFunction(Function  &F){
      runAnalysis(F);
     
       LI = &getAnalysis<LoopInfo>();
       DT = &getAnalysis<DominatorTree>();
      vector<Instruction*> editlist;
      int change = 0;
      do
      {
        //errs()<<"Entered again\n";
        change = 0;
        for (inst_iterator inst = inst_begin(F), e = inst_end(F); inst != e;)
        {
          
            Instruction *i = &*inst++;

	  //   errs() << "; ";
      int count =0;
      for (ValueMap<Value*,InsNode<BitVector>*>::iterator it = flowForIns.begin(), ite = flowForIns.end(); it != ite; it++) {
	if(Instruction* ins = dyn_cast<Instruction>(it->first)){
	  if(ins==i){
	    for (unsigned bit = 0; bit < it->second->out->size(); bit++){
	      if(it->second->out->test(bit) == true){
		for (ValueMap<Value*,int>::iterator it1 = mapValueToBit.begin(), it1e = mapValueToBit.end(); it1 != it1e; it1++) {
		  
                    if(it1->second == bit)
		    {//errs() << it1->first->getName() << ", ";
		     if(isa<Instruction>(it1->first) && ins == dyn_cast<Instruction>(it1->first))
		    {
                    //errs() << it1->first->getName()<<"matches"<<ins->getName()<<"\n";
		      count =1;
		    }
		    				
	          }		
		}
	      }
	    }
	    break;
	  }
	}
      }
         

	if (count==0 && !i->isTerminator() && !isa<PHINode>(&*i))
	{
        //errs()<<"\n"<<i->getName()<<" is marked for removal\n";
        //errs()<<LI->getLoopFor(i->getParent())<<"\n";
        // errs()<<"entered here\n"; 
         Loop* CurrentLoop = LI->getLoopFor(i->getParent());
         SmallVector<BasicBlock*, 8> ExitBlocks;
         if(CurrentLoop!=NULL) 
         CurrentLoop->getExitBlocks(ExitBlocks);
         int k =1;
         
         for (Value::use_iterator ins = i->use_begin(), e = i->use_end(); ins != e; ++ins)
         if(*ins!=NULL)
         if (Instruction *Inst = dyn_cast<Instruction>(*ins)) 
         {
              
            if (!DT->dominates(i->getParent(), Inst->getParent()))
         {
          // errs()<<*i<<"does not dom use inst "<<Inst->getName()<<"\n";
           k =0;
         }

         }

         
//         for (unsigned j = 0, e = ExitBlocks.size(); j != e; ++j)
//         if (!DT->dominates(i->getParent(), ExitBlocks[j]))
//         {
//           errs()<<"does not dom all exit block "<<ExitBlocks[j]->getName()<<"\n";
//           k =0;
//         }

        // if (isSafeToSpeculativelyExecute(&*i))
        // k=1;
 

         if(k==0)
         break;



         //errs()<<*i<<"is removed\n";
         i->dropAllReferences();
         i->removeFromParent();
         //editlist.push_back(i);
         change = 1;
         runAnalysis(F);
        

        }
      
        }
  

      }while(change==1);		      	 

      return false;
    }

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
       AU.setPreservesAll();
       AU.addRequired<LoopInfo>();
       AU.addRequired<DominatorTree>();
     }






  };


char FunctionInfo::ID = 0;
RegisterPass<FunctionInfo> X("dce-pass", "DCE Pass");

}

