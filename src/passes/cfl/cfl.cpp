
#include <pass.h>
#include <map>
#include <optional>

#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/CFG.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/IRBuilder.h"

using namespace llvm;

#define DEBUG_TYPE "cfl"
#define cflPassLog(M) LLVM_DEBUG(dbgs() << "CFLPass: " << M << "\n")
#define oprint(s) outs() << s << "\n"

static cl::list<std::string>
Functions("cfl-funcs",
    cl::desc("Specify all the comma-separated function regexes to cfl"),
    cl::ZeroOrMore, cl::CommaSeparated, cl::NotHidden);

static cl::opt<bool>
SimpleBranches("cfl-simple-branches",
    cl::desc("Linearize only simple branches"),
    cl::init(false), cl::NotHidden);

static cl::opt<bool>
MemProtect("cfl-protect-mem",
    cl::desc("CFL: protect memory accesses (disable if run after DFL)"),
    cl::init(true), cl::NotHidden);

static cl::opt<bool>
BranchProtect("cfl-protect-branches",
    cl::desc("CFL: protect branches"),
    cl::init(true), cl::NotHidden);

static cl::opt<bool>
CFLRelaxed("cfl-relaxed",
    cl::desc("Avoid linearizing non tainted branches for which we may prove they are safe"),
    cl::init(false), cl::NotHidden);

typedef long imd_t;

namespace {

  class IfCondition {
  public:
      BranchInst *Branch;
      BasicBlock *MergePoint;
      BasicBlock *IfTrue;
      BasicBlock *IfFalse;
      BasicBlock *IfTruePred;
  };

  class CFLPass : public ModulePass {

    unsigned long CFLedFuncs         = 0;
    unsigned long totalFuncs         = 0;
    unsigned long linearizedBranches = 0;
    unsigned long totalBranches      = 0;
    unsigned long totalIFCs          = 0;
    std::map<const BasicBlock *, int> syntheticBGIDs;
    std::map<const Instruction *, int> syntheticIBIDs;
    int nextSyntheticBGID = -1;
    int nextSyntheticIBID = -1;
    
  public:
    static char ID;
    CFLPass() : ModulePass(ID) {}

    void setInstructionTaint(Instruction *I, bool taint) {
        LLVMContext& C = I->getContext();
        MDNode* N = MDNode::get(C, ConstantAsMetadata::get(ConstantInt::get(C, APInt(sizeof(imd_t)*8, taint, true))));
        I->setMetadata("t", N);
    }

    bool getInstructionTaint(Instruction &I) {
        MDNode* N;
        Constant *val;
        N = I.getMetadata("t");
        if (N == NULL) return false;
        val = dyn_cast<ConstantAsMetadata>(N->getOperand(0))->getValue();
        if (!val) return false;
        int taint = cast<ConstantInt>(val)->getSExtValue();
        return taint;
    }

    // check if the instruction has been marked as uninteresting by the 
    // loadtainted pass
    bool isInstructionUninteresting(Instruction &I) {
        MDNode* N;
        N = I.getMetadata("uninteresting_direction");
        if (N == NULL) return false;
        return true;
    }

    bool getUninterestingDirection(Instruction &I) {
        MDNode* N;
        Constant *val;
        N = I.getMetadata("uninteresting_direction");
        if (N == NULL) return false;
        val = dyn_cast<ConstantAsMetadata>(N->getOperand(0))->getValue();
        if (!val) return false;
        int direction = cast<ConstantInt>(val)->getSExtValue();
        return direction;
    }

    std::optional<int> getMetadataInt(MDNode *N) {
        if (!N || N->getNumOperands() == 0)
            return std::nullopt;

        auto *Meta = dyn_cast<ConstantAsMetadata>(N->getOperand(0));
        if (!Meta)
            return std::nullopt;

        auto *Val = dyn_cast<ConstantInt>(Meta->getValue());
        if (!Val)
            return std::nullopt;

        return static_cast<int>(Val->getSExtValue());
    }

    int getOrCreateSyntheticBGID(const BasicBlock *BB) {
        auto It = syntheticBGIDs.find(BB);
        if (It != syntheticBGIDs.end())
            return It->second;
        int Assigned = nextSyntheticBGID--;
        syntheticBGIDs.emplace(BB, Assigned);
        return Assigned;
    }

    int getOrCreateSyntheticIBID(const Instruction *I) {
        auto It = syntheticIBIDs.find(I);
        if (It != syntheticIBIDs.end())
            return It->second;
        int Assigned = nextSyntheticIBID--;
        syntheticIBIDs.emplace(I, Assigned);
        return Assigned;
    }

    int getBGID(Instruction &I) {
        BasicBlock *BB = I.getParent();
        if (BB && BB->getTerminator()) {
            if (auto ID = getMetadataInt(BB->getTerminator()->getMetadata("b-gid")))
                return *ID;
        }
        return getOrCreateSyntheticBGID(BB);
    }

    int getIBID(Instruction &I) {
        if (auto ID = getMetadataInt(I.getMetadata("i-bid")))
            return *ID;
        return getOrCreateSyntheticIBID(&I);
    }

    ConstantInt* makeConstI32(LLVMContext &C, int value) {
        return ConstantInt::get(C, APInt(sizeof(int)*8, value, true));
    }

    ConstantInt* makeConstBool(LLVMContext &C, int value) {
        ConstantInt *BoolTrue = ConstantInt::getTrue(C);
        ConstantInt *BoolFalse = ConstantInt::getFalse(C);
        return value? BoolTrue : BoolFalse;
    }

    void wrapIntrinsicCall(CallBase &CB, Function *Callee) {
        const char *wrapper = NULL;
        switch(Callee->getIntrinsicID()) {
        case Intrinsic::memcpy:
            wrapper = "cfl_memcpy";
            break;
        case Intrinsic::memmove:
            wrapper = "cfl_memmove";
            break;
        case Intrinsic::memset:
            wrapper = "cfl_memset";
            break;
        default:
            return;
        }
        Module *M = Callee->getParent();
        Function *NewCallee = M->getFunction(wrapper);
        if (!NewCallee) {
            FunctionType *FTy = Callee->getFunctionType();
            FunctionCallee Decl = M->getOrInsertFunction(wrapper, FTy);
            NewCallee = dyn_cast<Function>(Decl.getCallee());
        }
        if (NewCallee)
            CB.setCalledFunction(NewCallee);
    }

    void wrapExtCall(CallBase &CB, Function *Callee) {
        Module *M = Callee->getParent();
        LLVMContext &Ctx = M->getContext();
        Type *PtrTy = PointerType::getUnqual(Ctx);
        FunctionType *FTy = FunctionType::get(PtrTy, {PtrTy}, false);
        FunctionCallee Wrap = M->getOrInsertFunction("cfl_fptr_wrap", FTy);
        Function *F = dyn_cast<Function>(Wrap.getCallee());
        if (!F) return;
        std::vector<Value*> args;
        Type *Param0 = F->getFunctionType()->getParamType(0);
        args.push_back(
            CastInst::CreatePointerCast(Callee, Param0, "", &CB));
        CallInst *CI = CallInst::Create(F, args, "", &CB);
        Value *NewCallee =
            CastInst::CreatePointerCast(CI, CB.getCalledOperand()->getType(),
                                        "", &CB);
        CB.setCalledOperand(NewCallee);
    }

    void wrapLoad(LoadInst *LI) {
        Module *M = LI->getParent()->getParent()->getParent();
        LLVMContext &Ctx = M->getContext();
        Type *PtrTy = PointerType::getUnqual(Ctx);
        FunctionType *FTy = FunctionType::get(PtrTy, {PtrTy}, false);
        FunctionCallee Wrap = M->getOrInsertFunction("cfl_ptr_wrap", FTy);
        Function *F = dyn_cast<Function>(Wrap.getCallee());
        static InlineFunctionInfo IFI;
        if (!F) return;
        std::vector<Value*> args;
        args.push_back(CastInst::CreatePointerCast(
            LI->getPointerOperand(), F->getFunctionType()->getParamType(0), "",
            LI));
        CallInst *CI = CallInst::Create(F, args, "", LI);
        LI->setOperand(0, CastInst::CreatePointerCast(CI, LI->getPointerOperandType(), "", LI));
        // do not inline now to avoid loops-cfl detecting this as an escaping value
        // due to the call to an unrecognized function
        // assert(InlineFunction(CS, IFI));
    }

    void wrapStore(StoreInst *SI) {
        Module *M = SI->getParent()->getParent()->getParent();
        LLVMContext &Ctx = M->getContext();
        Type *PtrTy = PointerType::getUnqual(Ctx);
        FunctionType *FTy = FunctionType::get(PtrTy, {PtrTy}, false);
        FunctionCallee Wrap = M->getOrInsertFunction("cfl_ptr_wrap", FTy);
        Function *F = dyn_cast<Function>(Wrap.getCallee());
        static InlineFunctionInfo IFI;
        if (!F) return;
        std::vector<Value*> args;
        args.push_back(CastInst::CreatePointerCast(
            SI->getPointerOperand(), F->getFunctionType()->getParamType(0), "",
            SI));
        CallInst *CI = CallInst::Create(F, args, "", SI);
        SI->setOperand(1, CastInst::CreatePointerCast(CI, SI->getPointerOperandType(), "", SI));
        // do not inline now to avoid loops-cfl detecting this as an escaping value
        // due to the call to an unrecognized function
        // assert(InlineFunction(CS, IFI));
    }


    void wrapUninterestingCondition(IfCondition &IFC) {
        static Function *CondF;

        // Init
        Function *F = IFC.MergePoint->getParent();
        LLVMContext& C = F->getContext();
        BasicBlock *IfHeader = IFC.Branch->getParent();
        Value *IfCond = IFC.Branch->getCondition();
        if (!CondF) {
            Module *M = F->getParent();
            LLVMContext &Ctx = M->getContext();
            Type *I1 = Type::getInt1Ty(Ctx);
            FunctionType *FTy = FunctionType::get(I1, {I1, I1}, false);
            FunctionCallee Cal = M->getOrInsertFunction("cfl_br_get_fixed", FTy);
            CondF = dyn_cast<Function>(Cal.getCallee());
        }

        int branchBGID = getBGID(*IFC.Branch);
        int branchIBID = getIBID(*IFC.Branch);

        // assert that the branch is not tainted
        if (getInstructionTaint(*IFC.Branch)) return;

        bool fixed_res = getUninterestingDirection(*IFC.Branch);
        // Call the wrapper
        std::vector<Value*> CondFArgs;
        CondFArgs.push_back(IfCond);
        CondFArgs.push_back(makeConstBool(C, fixed_res));
        // add the required IDs if CFL_DEBUG==2
        if (CondF->arg_size() > CondFArgs.size()) {
            CondFArgs.push_back(makeConstI32(C, branchBGID));
            CondFArgs.push_back(makeConstI32(C, branchIBID));
        }
        Value *FixedCond = CallInst::Create(CondF, CondFArgs, "", IfHeader->getTerminator());
        IFC.Branch->setCondition(FixedCond);
    }

    void wrapCondition(IfCondition &IFC) {
        static Function *CondF, *IfTrueF, *IfFalseF, *MergePointF;

        // Init
        Function *F = IFC.MergePoint->getParent();
        BasicBlock *IfHeader = IFC.Branch->getParent();
        Value *IfCond = IFC.Branch->getCondition();
        if (!CondF) {
            Module *M = F->getParent();
            LLVMContext &Ctx = M->getContext();
            Type *VoidTy = Type::getVoidTy(Ctx);
            Type *PtrTy = PointerType::getUnqual(Ctx);
            Type *I1 = Type::getInt1Ty(Ctx);
            FunctionCallee CondCal =
                M->getOrInsertFunction("cfl_br_cond",
                                       FunctionType::get(VoidTy, {PtrTy}, false));
            FunctionCallee IfTrueCal = M->getOrInsertFunction(
                "cfl_br_iftrue", FunctionType::get(VoidTy, {PtrTy, I1}, false));
            FunctionCallee IfFalseCal =
                M->getOrInsertFunction("cfl_br_iffalse",
                                       FunctionType::get(VoidTy, {PtrTy, I1}, false));
            FunctionCallee MergeCal =
                M->getOrInsertFunction("cfl_br_merge",
                                       FunctionType::get(VoidTy, {PtrTy}, false));
            CondF = dyn_cast<Function>(CondCal.getCallee());
            IfTrueF = dyn_cast<Function>(IfTrueCal.getCallee());
            IfFalseF = dyn_cast<Function>(IfFalseCal.getCallee());
            MergePointF = dyn_cast<Function>(MergeCal.getCallee());
        }
        if (!CondF || !IfTrueF || !IfFalseF || !MergePointF)
            return;

        // Create local to pass to wrappers
        LLVMContext &C = F->getContext();
        AllocaInst *AITmp = new AllocaInst(Type::getInt1Ty(C), 0, "cfl_tmp",
                                           &*(F->getEntryBlock().getFirstInsertionPt()));
        const DataLayout &DL = AITmp->getParent()->getParent()->getParent()->getDataLayout();
        // Set lifetime start information
        llvm::IRBuilder<> BuilderStart(AITmp->getNextNode());
        BuilderStart.CreateLifetimeStart(AITmp, ConstantInt::get(Type::getInt64Ty(C), DL.getTypeAllocSize(AITmp->getAllocatedType())));

        // The branch condition may not dominate the serialized IfFalse path when
        // the original true/false regions contain loops. Store it once in the
        // header and reload it where needed to keep SSA dominance valid.
        AllocaInst *AICond = new AllocaInst(
            Type::getInt1Ty(C), 0, "cfl_cond",
            &*(F->getEntryBlock().getFirstInsertionPt()));
#if 0
        errs() << IFC.MergePoint->getName() << "\n";
        IfCond->print(errs()); errs() << "\n";
        if (IFC.IfTrue) errs() << IFC.IfTrue->getName() << "\n";
        if (IFC.IfFalse) errs() << IFC.IfFalse->getName() << "\n";
#endif

        int branchBGID = getBGID(*IFC.Branch);
        int branchIBID = getIBID(*IFC.Branch);

        // Store the original condition in the header. This is required because
        // after CFL serializes execution, the IfFalse region may be reached via
        // paths (e.g., loops) that do not preserve SSA dominance of IfCond.
        new StoreInst(IfCond, AICond, IfHeader->getTerminator());

        // Call wrappers
        std::vector<Value*> CondFArgs;
        CondFArgs.push_back(AITmp);
        // add the required IDs if CFL_DEBUG==2
        if (CondF->arg_size() > CondFArgs.size()) {
            CondFArgs.push_back(makeConstI32(C, branchBGID));
            CondFArgs.push_back(makeConstI32(C, branchIBID));
        }
        CallInst::Create(CondF, CondFArgs, "", IfHeader->getTerminator());

        if (IFC.IfTrue != IFC.MergePoint) {
            std::vector<Value*> IfTrueFArgs;
            IfTrueFArgs.push_back(AITmp);
            Instruction *IfTrueIP = &*(IFC.IfTrue->getFirstInsertionPt());
            LoadInst *CondTrue =
                new LoadInst(Type::getInt1Ty(C), AICond, "", IfTrueIP);
            IfTrueFArgs.push_back(CondTrue);
            CallInst::Create(IfTrueF, IfTrueFArgs, "", IfTrueIP);
        }

        if (IFC.IfFalse != IFC.MergePoint) {
            std::vector<Value*> IfFalseFArgs;
            IfFalseFArgs.push_back(AITmp);
            Instruction *IfFalseIP = &*(IFC.IfFalse->getFirstInsertionPt());
            LoadInst *CondFalse =
                new LoadInst(Type::getInt1Ty(C), AICond, "", IfFalseIP);
            IfFalseFArgs.push_back(CondFalse);
            CallInst::Create(IfFalseF, IfFalseFArgs, "", IfFalseIP);
        }

        std::vector<Value*> MergePointFArgs;
        MergePointFArgs.push_back(AITmp);
        CallInst* MergeCall = CallInst::Create(MergePointF, MergePointFArgs, "", &*(IFC.MergePoint->getFirstInsertionPt()));

        // Create lifetime end at the merge point
        llvm::IRBuilder<> BuilderEnd(MergeCall->getNextNode());
        BuilderEnd.CreateLifetimeEnd(AITmp, ConstantInt::get(Type::getInt64Ty(C), DL.getTypeAllocSize(AITmp->getAllocatedType())));

        // Turn any PHIs into Selects in MergePoint block
        Instruction *MergeIP = &*(IFC.MergePoint->getFirstInsertionPt());
        LoadInst *CondMerge =
            new LoadInst(Type::getInt1Ty(C), AICond, "", MergeIP);
        while (PHINode *PN = dyn_cast<PHINode>(IFC.MergePoint->begin())) {
            if (PN->getNumIncomingValues() != 2)
                break;
            Value *TrueVal = PN->getIncomingValue(PN->getIncomingBlock(0) == IFC.IfTruePred ? 0 : 1);
            Value *FalseVal = PN->getIncomingValue(PN->getIncomingBlock(0) == IFC.IfTruePred ? 1 : 0);
            Value *Sel = SelectInst::Create(CondMerge, TrueVal, FalseVal, "",
                                            MergeIP);
            PN->replaceAllUsesWith(Sel);
            Sel->takeName(PN);
            PN->eraseFromParent();
        }

        // Move IfFalse block (might be MergePoint) under IfTrue block
        BranchInst *BI = dyn_cast<BranchInst>(IFC.IfTruePred->getTerminator());
        if (!BI)
            return;
        bool Rewired = false;
        for (unsigned i=0;i<BI->getNumSuccessors();i++) {
            if (BI->getSuccessor(i) == IFC.MergePoint) {
                // In the case where IfTruePred == IfHeader, the IFC.Branch
                // will now point twice to IFFalse, but it's ok
                BI->setSuccessor(i, IFC.IfFalse);
                Rewired = true;
                break;
            }
        }
        if (!Rewired)
            return;

        // Remove conditional branch if IfTruePred != IfHeader
        // Otherwise we already fixed the jumps while connecting IfTrue to IFFalse
        if (IFC.IfTruePred != IfHeader) {
            // We removed the direct edge IfHeader -> IfFalse and replaced it
            // with IfTruePred -> IfFalse to serialize execution. Update PHI
            // nodes in the IfFalse block accordingly, otherwise the CFG change
            // leaves stale incoming blocks and breaks SSA form.
            IFC.IfFalse->replacePhiUsesWith(IfHeader, IFC.IfTruePred);
            BranchInst::Create(IFC.IfTrue, IFC.Branch);
            IFC.Branch->eraseFromParent();
        }
    }

    BasicBlock *getImmediatePostdominator(PostDominatorTree *PDT, BasicBlock* BB) {
        auto SuccIt = ++df_begin(BB);
        auto SuccEnd = df_end(BB);
        while (SuccIt != SuccEnd) {
            BasicBlock *SuccBB = *SuccIt;
            if (PDT->dominates(SuccBB, BB)) {
                return SuccBB;
            }
            SuccIt++;
        }
        return NULL;
    }

    IfCondition *getIfCondition(DominatorTree *DT, PostDominatorTree *PDT, BranchInst *BI) {
        static IfCondition IFC;

        // Only conditional branches
        if (!BI->isConditional() || BI->getNumSuccessors()!=2)
            return NULL;

        // Look for i-postdominator with 2 predecessors, dominated by branch
        BasicBlock *BB = BI->getParent();
        BasicBlock *IPD = getImmediatePostdominator(PDT, BB);
        if (!IPD || !IPD->hasNPredecessors(2) || !DT->dominates(BB, IPD))
            return NULL;

        // Found candidate merge point, ensure it isn't someone else's point
        auto SuccIt = ++df_begin(BB);
        auto SuccEnd = df_end(BB);
        while (SuccIt != SuccEnd) {
            BasicBlock *SuccBB = *SuccIt;
            if (SuccBB == IPD)
                break;
            BranchInst *BI = dyn_cast<BranchInst>(SuccBB->getTerminator());
            if (BI && BI->isConditional() && DT->dominates(SuccBB, IPD))
                return NULL;
            SuccIt++;
        }

        // Found the merge point block, fill info and return
        IFC.Branch = BI;
        IFC.MergePoint = IPD;
        IFC.IfTrue = BI->getSuccessor(0);
        IFC.IfFalse = BI->getSuccessor(1);
        IFC.IfTruePred = NULL;
        for (BasicBlock *Pred : predecessors(IFC.MergePoint)) {
            if (!DT->dominates(IFC.IfTrue, Pred))
                continue;
            if (IFC.IfTruePred)
                return NULL;
            IFC.IfTruePred = Pred;
        }
        // if no predecessor of the MergePoint is dominated by the IFTrue Block
        // it means IFTrue == MergePoint, so we set IFTruePred = BranchBB
        if(!IFC.IfTruePred) {
            IFC.IfTruePred = IFC.Branch->getParent();
        }
        return &IFC;
    }

    void cfl(Function *F) {
        cflPassLog("CFLing " << F->getName());
        DominatorTree *DT = &getAnalysis<DominatorTreeWrapperPass>(*F).getDomTree();
        PostDominatorTree PDT;
        PDT.recalculate(*F);
        F->addFnAttr("null-pointer-is-valid", "true");

        // Wrap loads, stores, memory intrinsics, and external calls
        for (auto &BB : *F)
        for (auto &I : BB) {
            // If we run after DFL we must not wrap memory accesses since the only
            // mem accesses that have been left unprotected are the one DFL needs
            if (MemProtect == true) {
                if (LoadInst *LI = dyn_cast<LoadInst>(&I)) {
                    wrapLoad(LI);
                    continue;
                }
                if (StoreInst *SI = dyn_cast<StoreInst>(&I)) {
                    wrapStore(SI);
                    continue;
                }
            }
            CallBase *CB = dyn_cast<CallBase>(&I);
            if (!CB || CB->isInlineAsm())
                continue; // not a call
            Function *Callee = CB->getCalledFunction();
            if (!Callee)
                continue; // not a direct call
            if (Callee->isIntrinsic())
                wrapIntrinsicCall(*CB, Callee);
            else if (Callee->isDeclaration())
                wrapExtCall(*CB, Callee);
        }

        if( BranchProtect == false) return;

        // Loop over CFG to first find and then wrap conditions
        std::vector<IfCondition> ifConditions;
        for (auto &BB : *F) {
            BranchInst *BI = dyn_cast<BranchInst>(BB.getTerminator());
            if (!BI)
                continue;
            if(BI->isConditional()) ++totalBranches;
            IfCondition *IFC = getIfCondition(DT, &PDT, BI);
            if (!IFC)
                continue;
            ++totalIFCs;
            if (SimpleBranches) {
                // Only simple branches LLVM's GetIfCondition can handle
                BasicBlock *IfTrue, *IfFalse;
                if (!GetIfCondition(IFC->MergePoint, IfTrue, IfFalse))
                    continue;
            }
            ifConditions.push_back(*IFC);
        }
        for (auto &IFC : ifConditions) {
            if (isInstructionUninteresting(*IFC.Branch)) {
                wrapUninterestingCondition(IFC);
                continue;
            }
            if (CFLRelaxed && (getInstructionTaint(*IFC.Branch) == false)) {
                // While it is necessary to set the taken variable in dummy/non-dummy
                // mode to properly wrap the memory accesses,
                // we can avoid linearizing the branch if it is not necessary
                // since this branch may be an inner branch of a tainted one, and it
                // may not leak anything
                continue;
            }
            ++linearizedBranches;
            wrapCondition(IFC);
        }
    }

    virtual bool runOnModule(Module &M) {
        cflPassLog("Running...");

        std::vector<Regex*> FunctionRegexes;
        if (Functions.empty())
            Functions.push_back("main");
        passListRegexInit(FunctionRegexes, Functions);

        /* Iterate all functions in the module to cfl */
        std::set<Function*> cflFunctionSet;
        for (auto &F : M.getFunctionList()) {
            if (F.isDeclaration())
                continue;
            ++totalFuncs;
            const std::string FName = F.getName().str();
            if (!passListRegexMatch(FunctionRegexes, FName))
                continue;
            if (F.getSection() == "dfl_code" || F.getSection() == "cfl_code" ||
                F.getSection() == "cgc_code" || F.getSection() == "icp_code")
                continue;
            cflFunctionSet.insert(&F);
        }
        while (!cflFunctionSet.empty()) {
            ++CFLedFuncs;
            Function *F = *cflFunctionSet.begin();
            cflFunctionSet.erase(cflFunctionSet.begin());
            // Linearize the control flow of the whole function
            cfl(F);
        }
        oprint("--------[ CFL STATS ]--------");
        oprint("[+] Total Functions    : " << totalFuncs);
        oprint("[+] CFLed Functions    : " << CFLedFuncs);
        oprint("[+] Total Branches     : " << totalBranches);
        oprint("[+] Total IFCs         : " << totalIFCs);
        oprint("[+] Linearized Branches: " << linearizedBranches);
        return true;
    }

    void getAnalysisUsage(AnalysisUsage &AU) const {
        AU.addRequired<DominatorTreeWrapperPass>();
    }

  };

}

char CFLPass::ID = 0;
RegisterPass<CFLPass> MP("cfl", "CFL Pass");
