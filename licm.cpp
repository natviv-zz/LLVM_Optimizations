#include "llvm/Pass.h"
#include "llvm/Support/CFG.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/PassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FormattedStream.h"
#include "llvm/Assembly/AssemblyAnnotationWriter.h"
#include "llvm/DebugInfo.h"
#include "llvm/IR/Module.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/ValueMap.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopIterator.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/Debug.h"
#include "DFAFramework.cpp"
#include "llvm/Transforms/Scalar.h"
#include "llvm/ADT/Statistic.h"
#include <map>
#include <set>
#include <vector>
#include <ostream>
#include <fstream>
#include <iostream>

 using namespace llvm;
 using namespace std;
 STATISTIC(LoopInstNum, "Counts number of instructions in a loop");

 namespace 
 {
   struct LICM : public LoopPass {
     static char ID; // Pass identification, replacement for typeid
     LICM() : LoopPass(ID) {}

     private:
     bool mayThrow;
     bool changed;
     LoopInfo* LI;
     DominatorTree* DT; 
     Loop* CurrentLoop;
     BasicBlock *Preheader;
     Instruction *InsertPt;

     virtual bool runOnLoop(Loop *L, LPPassManager &LPM) 
     {
          LI = &getAnalysis<LoopInfo>();
          DT = &getAnalysis<DominatorTree>();
          CurrentLoop = L;

          Preheader = L->getLoopPreheader();
          InsertPt = Preheader->getTerminator();
          errs()<<"Insert point "<<*InsertPt<<"\n";
          BasicBlock* bb = L->getUniqueExitBlock();  
          errs()<<bb->getName()<<" Exit block name \n";
          errs()<<L->getLoopDepth()<<" sub loops \n";

          mayThrow = false;
          //Check for instructions which can throw. Need to consider their effects
          checkforThrowIns(mayThrow);
          if(!mayThrow)
          errs()<<" May throw "<<mayThrow<<" \n";      

	  
          if (Preheader)
             HoistRegion(DT->getNode(L->getHeader()));

          

         for (Loop::block_iterator b = L->block_begin(), be = L->block_end();b !=be; ++b)
         {
         for (BasicBlock::iterator i = (*b)->begin(), ie = (*b)->end(); i != ie; ++i)
         {
                 Instruction* ins = i; 	
                 errs()<<*i<<" "<<isUsedinLoop(*ins)<<"\n";

         }
         }

       return false;
     }

     // We don't modify the program, so we preserve all analyses
     virtual void getAnalysisUsage(AnalysisUsage &AU) const {
       AU.setPreservesAll();
       AU.addRequired<LoopInfo>();
       AU.addRequired<DominatorTree>();
     }

     bool inSubLoop(BasicBlock *bb)
     {
     
      assert(CurrentLoop->contains(bb) && "Valid if BB is IN the loop");
      return LI->getLoopFor(bb) != CurrentLoop;
    
     }

   // Check if trapping ins is executed, then safe to hoist .
   bool isSafeToHoist(Instruction &Inst) 
   {
   
      if (llvm::isSafeToSpeculativelyExecute(&Inst))
        return true;
 
      return isExecuted(Inst);
   } 

   // Check if ins is executed
   //a> No throwing ins
   //b> Dominates all exit blocks of loop  
   //c> Check if loop is not infinie
   bool isExecuted(Instruction &I){

       if(mayThrow)
         return false;

       if (I.getParent() == CurrentLoop->getHeader())
         return true;

       SmallVector<BasicBlock*, 8> ExitBlocks;
       CurrentLoop->getExitBlocks(ExitBlocks);
 
       for (unsigned i = 0, e = ExitBlocks.size(); i != e; ++i)
       if (!DT->dominates(I.getParent(), ExitBlocks[i]))
         return false;
 
       if (ExitBlocks.empty())
         return false;
 
       return true; 
    
   } 


   void checkforThrowIns(bool& mayThrow){
      
      for (Loop::block_iterator BB = CurrentLoop->block_begin(), BBE = CurrentLoop->block_end();(BB != BBE) && !mayThrow ; ++BB)
         for (BasicBlock::iterator I = (*BB)->begin(), E = (*BB)->end();(I != E) && !mayThrow; ++I)
                   mayThrow |= I->mayThrow();        

   }

  

   // DFS based search of Dominator tree to do LICM in one iteration
   void HoistRegion(DomTreeNode *N) {
        assert(N != 0 && "Null dominator tree node?");
        BasicBlock *BB = N->getBlock();
        //errs()<<"Came to hoist region\n"; 
        if (!CurrentLoop->contains(BB)) return;
 
        if (!inSubLoop(BB))
          for (BasicBlock::iterator II = BB->begin(), E = BB->end(); II != E; ) {
            Instruction &I = *II++;
 
       // Check for constant folding
          if (Constant *C = ConstantFoldInstruction(&I)) 
          {
             I.replaceAllUsesWith(C);
             I.eraseFromParent();
             continue;
          }
 
          //  errs()<<"Ins "<<I<<"\n";
          // errs()<<"Invariance "<<checkforInvariance(&I)<<"\n";
          //  errs()<<"validate Hoist "<<validateHoist(I)<<"\n";
          //  errs()<<"safe to hoist "<<isSafeToHoist(I)<<"\n";
            

       // Check for Instruction invaraince. If yes hoist to preheader
          if (checkforInvariance(&I) && validateHoist(I) &&
             isSafeToHoist(I))
          {
            errs()<<"Hoisting\n";
            hoist(I);
          }
       } 
       const std::vector<DomTreeNode*> &Children = N->getChildren();
       for (unsigned i = 0, e = Children.size(); i != e; ++i)
         HoistRegion(Children[i]);
   }

   //Certain load and call instructions are not to be hoisted
   bool validateHoist(Instruction &I){

   if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
     if (!LI->isUnordered()) //Check for load invariance
       return false;
     if (LI->getMetadata("invariant.load"))
       return true;
     }
     //From LLVM API only these instructions to be hoisted
     if (!isa<BinaryOperator>(I) && !isa<CastInst>(I) && !isa<SelectInst>(I) && !isa<GetElementPtrInst>(I) && !isa<CmpInst>(I)                    &&!isa<InsertElementInst>(I) && !isa<ExtractElementInst>(I) && !isa<ShuffleVectorInst>(I) && !isa<ExtractValueInst>(I) && !isa<InsertValueInst>(I))
     return false;

     return isSafeToHoist(I);
 
   }

   void hoist(Instruction &I) {
      I.moveBefore(Preheader->getTerminator());
      changed = true;

   }



//Check if instruction is used in loop handling special case for phi nodes
   bool isUsedinLoop(Instruction& I)
   {

         for (Value::use_iterator i = I.use_begin(), e = I.use_end(); i != e; ++i)
         { 
          Instruction *UsedIns = dyn_cast<Instruction>(*i);
          if (PHINode *PN = dyn_cast<PHINode>(UsedIns)) 
           {
       
               if (isRedundantPHI(*PN, I)) 
               {
                 if (CurrentLoop->contains(PN))
                   return true;
                 else
                   continue;
               }
  
             // Check is another use is inside the current loop.
               for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i)
                  if (PN->getIncomingValue(i) == &I)
                     if (CurrentLoop->contains(PN->getIncomingBlock(i)))
                        return true;
                     continue;
           } 
  
          if (CurrentLoop->contains(UsedIns))
            return true;
         }
    
      return false;


   }

  //Check for redundant phi nodes possible in LCSSA form         
   static bool isRedundantPHI(PHINode &PN, Instruction &I) {
   for (unsigned i = 0, e = PN.getNumIncomingValues(); i != e; ++i)
     if (PN.getIncomingValue(i) != &I)
       return false;
    return true;
 }

  //Check for instruction invariance in loop
  bool checkforInvariance(Instruction* I)
  {
   for (unsigned i = 0, e = I->getNumOperands(); i != e; ++i)
     if (!isInvariant(I->getOperand(i)))
       return false;
 
   return true;    


  }

  bool isInvariant(Value *V) const 
  {
   if (Instruction *I = dyn_cast<Instruction>(V))
     return !CurrentLoop->contains(I);
   return true;  
  }

   };
 

 char LICM::ID = 0;
 RegisterPass<LICM> X("LICM", "LICM");

}

