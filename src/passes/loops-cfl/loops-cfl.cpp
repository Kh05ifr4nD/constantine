
#include <pass.h>
#include <iostream>
#include <fstream>
#include <iomanip>
#include <map>
#include <random>
#include <set>
#include <utility>
#include <cmath>

#include "llvm/IR/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Support/Alignment.h"
#include "llvm/Support/ErrorHandling.h"

using namespace llvm;

#define DEBUG_TYPE "loops-cfl"
#define loopsCFLPassLog(M) LLVM_DEBUG(dbgs() << "LoopsCFLPass: " << M << "\n")
#define qprint(s) std::cout << s << std::endl
#define oprint(s) outs() << s << "\n"

typedef long imd_t;

static cl::list<std::string>
Functions("loops-cfl-funcs",
    cl::desc("Specify all the comma-separated function regexes to cfl"),
    cl::ZeroOrMore, cl::CommaSeparated, cl::NotHidden);

static cl::opt<bool>
ProtectStores("loops-cfl-protect-stores",
    cl::desc("Protect stores in loops (KEEP ENABLED if mem-protect disabled in CFL)"),
    cl::init(true), cl::NotHidden);

static cl::opt<std::string>
ConfigFilename("loops-cfl-conf",
    cl::desc("The file to load config from, for the initial values of `max_count`"),
    cl::init(""), cl::NotHidden);

static cl::opt<unsigned long>
DefaultMaxCount("loops-cfl-default-max",
    cl::desc("Fallback initializer for `max_count` when no config entry is present (0 disables fallback)"),
    cl::init(0), cl::NotHidden);

static cl::opt<bool>
DumpConf("loops-cfl-dump-conf",
    cl::desc("Dump the runtime `max_count` value to `stderr` when executing"),
    cl::init(false), cl::NotHidden);

unsigned long totalLoops = 0;
unsigned long protectedLoops = 0;

namespace {
  // Linearize Loops by fixing the number of iterations to the maximum value seen.
  // BEWARE: This pass will work correctly only if applied to code which has been
  // protected by the CFL or DFL pass: It will modify how loops are executed and
  // will introduce inconsistencies with the program if the memory accesses are 
  // not properly shielded by either CFL or DFL.
  // The pass tries to prevent invalid values to escape the dummy interations of
  // the loop, but this is impossible when a loop is always executed in dummy mode
  // since we do not have any valid value to rely on.
  // (e.g. a loop in a dummy branch, or an inner loop during the dummy iterations
  // of the outer one)
  class LoopsCFLPass : public LoopPass {

    // Hold the max_count initialization value for each branch, if present in the configuration
    // <b_gid, i_bid> -> initial_value
    std::map<std::pair<int,int>,unsigned long> maxCountInit;
    unsigned long unique_id;
  public:
    static char ID;
    LoopsCFLPass() : LoopPass(ID) {
        unique_id = 0;

        // check if the configuration file is present, and load it if it is the case
        if (ConfigFilename != "") {
            // open the config file to read the conf
            std::ifstream configFile(ConfigFilename);
            if (!configFile.is_open()) {
                oprint("Failed to open configuration file");
                exit(1);
            }
            int b_gid,i_bid;
            unsigned long value;
            // Read all the values
            while (configFile >> value >> b_gid >> i_bid)
            {
                // std::cout << b_gid << " " << i_bid << " " << value << std::endl;
                
                // Update the initial value if we found an higher one
                if (maxCountInit[std::make_pair(b_gid, i_bid)] < value)
                    maxCountInit[std::make_pair(b_gid, i_bid)] = value;
            }
        }
    }

    ~LoopsCFLPass() {
        // We should not be allowed to keep info between runOnLoop invocations,
        // but we like living dangerously
        oprint("--------[ LOOP-CFL STATS ]--------");
        oprint("[+] Total Loops    : " << totalLoops);
        oprint("[+] Protected Loops: " << protectedLoops);
    }

    unsigned long getUniqueID() {
        return unique_id++;
    }

    ConstantInt* makeConstI8(LLVMContext &C, unsigned char value) {
        return ConstantInt::get(C, APInt(sizeof(unsigned char)*8, value));
    }

	    bool hasTaintMetadata(Instruction *I) {
	        MDNode* N;
	        N = I->getMetadata("t");
	        return N != NULL;
	    }

	    bool getInstructionTaint(Instruction &I) {
	        MDNode* N;
	        Constant *val;
	        N = I.getMetadata("t");
	        if (N == NULL) return false;
	        val = dyn_cast<ConstantAsMetadata>(N->getOperand(0))->getValue();
	        if (!val) return false;
	        int taint = cast<ConstantInt>(val)->getSExtValue();
	        return taint != 0;
	    }

    void dumpIDs(llvm::Instruction& I, llvm::BasicBlock &BB, int taint){
        MDNode* N;
        Constant *val;
        N = BB.getTerminator()->getMetadata("b-gid");
        val = dyn_cast<ConstantAsMetadata>(N->getOperand(0))->getValue();
        assert(val);
        int b_gid = cast<ConstantInt>(val)->getSExtValue();
        N = I.getMetadata("i-bid");
        val = dyn_cast<ConstantAsMetadata>(N->getOperand(0))->getValue();
        assert(val);
        int i_bid = cast<ConstantInt>(val)->getSExtValue();
        std::cout << (taint == 1? "  loop:T00000:" : "  loop:0t0000:") << std::setfill('0') 
                 << std::setw(8) << b_gid << ":" << std::setfill('0') << std::setw(4) 
                 << i_bid << std::endl;
    }

    int getBGID(Instruction &I) {
        MDNode* N;
        Constant *val;
        BasicBlock *BB = I.getParent();
        N = BB->getTerminator()->getMetadata("b-gid");
        val = dyn_cast<ConstantAsMetadata>(N->getOperand(0))->getValue();
        assert(val);
        int b_gid = cast<ConstantInt>(val)->getSExtValue();
        return b_gid;
    }

    int getIBID(Instruction &I) {
        MDNode* N;
        Constant *val;
        N = I.getMetadata("i-bid");
        val = dyn_cast<ConstantAsMetadata>(N->getOperand(0))->getValue();
        assert(val);
        int i_bid = cast<ConstantInt>(val)->getSExtValue();
        return i_bid;
    }

    ConstantInt* makeConstU64(LLVMContext &C, unsigned long value) {
        return ConstantInt::get(C, APInt(sizeof(unsigned long)*8, value));
    }

    ConstantInt* makeConstI32(LLVMContext &C, int value) {
        return ConstantInt::get(C, APInt(sizeof(int)*8, value, true));
    }

    void setLoopNoUnroll(Loop *L) {
        LLVMContext &Context = L->getHeader()->getContext();

        MDNode *DisableUnrollMD =
            MDNode::get(Context, MDString::get(Context, "llvm.loop.unroll.disable"));
        MDNode *LoopID = L->getLoopID();
        MDNode *NewLoopID = makePostTransformationMetadata(
            Context, LoopID, {"llvm.loop.unroll."}, {DisableUnrollMD});
        L->setLoopID(NewLoopID);
    }

    // Obtain a random value to use in place of an undef value, which appears safer
    Value *getPoison(Type* T, Function *F) {
        // Seed with a real random value, if available
        static std::random_device rd;
        std::mt19937_64 e2(rd());
        std::uniform_int_distribution<long long unsigned int> dist(std::llround(std::pow(2,61)), std::llround(std::pow(2,62)));
        unsigned long long randValue = 0;//dist(e2);
        // unsigned long long randValue = 0x1111111100001100uL | (protectedLoops << 16uL) | (dist(e2) & 0xff);

        LLVMContext &C = F->getContext();
        const DataLayout &DL = F->getParent()->getDataLayout();
        uint64_t valSize = DL.getTypeSizeInBits(T); 

        if (T->isPointerTy()) return CastInst::Create(CastInst::IntToPtr, ConstantInt::get(C, APInt(valSize, randValue)), T, "", &*F->getEntryBlock().getFirstInsertionPt());
        
        if (!T->isIntegerTy()) return UndefValue::get(T);

        return ConstantInt::get(C, APInt(valSize, randValue));
    }

    // Memory accesses and external calls are already managed in the cfl pass,
    // here we just need to manage the loop iterations (i.e. avoid iteration timing leaks)
    void loops_cfl(Loop* L) {
        static Function *PreheaderFunc, *ExitingFunc, *ExitFunc, *DumpFunc;
        // CFL already wrapped loads, stores, memory intrinsics, and external calls

        Function* F = L->getHeader()->getParent();
        Module* M = F->getParent();

        BasicBlock* PreheaderBlock = L->getLoopPreheader();
        BasicBlock* HeaderBlock = L->getHeader();

        // StrictCT: loops may have multiple exiting blocks (e.g. one exit to an
        // outer loop and one exit to the function epilogue). For loops-cfl we
        // specifically linearize tainted exit checks; pick the unique tainted
        // conditional branch that exits the current loop.
        BasicBlock* ExitingBlock = nullptr;
        BasicBlock* ExitBlock = nullptr;
        BranchInst* ExitingBranch = nullptr;
        llvm::SmallVector<llvm::BasicBlock*, 16> ExitingBlocks;
        L->getExitingBlocks(ExitingBlocks);
        for (llvm::BasicBlock* BB : ExitingBlocks) {
            if (!BB)
                continue;
            llvm::BranchInst *BI = dyn_cast<llvm::BranchInst>(BB->getTerminator());
            if (!BI || !BI->isConditional())
                continue;
            if (!getInstructionTaint(*BI))
                continue;
            llvm::BasicBlock *S0 = BI->getSuccessor(0);
            llvm::BasicBlock *S1 = BI->getSuccessor(1);
            const bool s0_in = L->contains(S0);
            const bool s1_in = L->contains(S1);
            if (s0_in == s1_in) {
                // both in-loop or both out-of-loop: not a simple exit/continue branch.
                continue;
            }
            llvm::BasicBlock *Outside = s0_in ? S1 : S0;
            if (ExitingBranch && ExitingBranch != BI) {
                errs() << "[loops-cfl] multiple tainted loop exits in function '"
                       << F->getName()
                       << "'; cannot linearize safely\n";
                report_fatal_error("loops-cfl: multiple tainted exits unsupported");
            }
            ExitingBranch = BI;
            ExitingBlock = BB;
            ExitBlock = Outside;
        }

        if (!PreheaderBlock || !HeaderBlock || !ExitingBlock || !ExitBlock ||
            !ExitingBranch) {
            errs() << "[loops-cfl] unsupported tainted loop in function '"
                   << F->getName()
                   << "' (needs preheader + tainted conditional exit branch)\n";
            report_fatal_error("loops-cfl: unsupported tainted loop form");
        }

        int branchBGID = getBGID(*ExitingBranch);
        int branchIBID = getIBID(*ExitingBranch);

        Value *LoopCond = ExitingBranch->getCondition();
        // Constantine expects the exiting branch to be of the form:
        //   br would_exit, exit, continue
        // Some frontends generate the opposite ordering (continue condition).
        // Normalize by swapping successors and inverting the condition when
        // needed.
        BasicBlock *Succ0 = ExitingBranch->getSuccessor(0);
        BasicBlock *Succ1 = ExitingBranch->getSuccessor(1);
        if (Succ0 != ExitBlock && Succ1 == ExitBlock && L->contains(Succ0)) {
            // Condition is "continue" → make it "exit".
            if (auto *C = dyn_cast<Constant>(LoopCond)) {
                LoopCond = ConstantExpr::getNot(C);
            } else {
                Instruction *InsertPt = ExitingBranch;
                LoopCond =
                    BinaryOperator::CreateNot(LoopCond, "loop_exit.inv", InsertPt);
            }
            ExitingBranch->setCondition(LoopCond);
            ExitingBranch->swapSuccessors();
        }

        if (ExitBlock != ExitingBranch->getSuccessor(0) ||
            !L->contains(ExitingBranch->getSuccessor(1)) ||
            PreheaderBlock->getUniqueSuccessor() != HeaderBlock) {
            errs() << "[loops-cfl] tainted loop has unexpected successor layout in function '"
                   << F->getName() << "'\n";
            report_fatal_error("loops-cfl: unsupported tainted loop successor layout");
        }

        if (!PreheaderFunc) {
            LLVMContext &Ctx = M->getContext();
            Type *VoidTy = Type::getVoidTy(Ctx);
            Type *PtrTy = PointerType::getUnqual(Ctx);
            Type *I1 = Type::getInt1Ty(Ctx);
            Type *I32 = Type::getInt32Ty(Ctx);

            PreheaderFunc = dyn_cast<Function>(
                M->getOrInsertFunction(
                     "cfl_loop_preheader",
                     FunctionType::get(VoidTy, {PtrTy, PtrTy, I32, I32}, false))
                    .getCallee());
            ExitingFunc = dyn_cast<Function>(
                M->getOrInsertFunction(
                     "cfl_loop_exiting",
                     FunctionType::get(I1, {PtrTy, PtrTy, I1}, false))
                    .getCallee());
            ExitFunc = dyn_cast<Function>(
                M->getOrInsertFunction(
                     "cfl_loop_exit",
                     FunctionType::get(VoidTy, {PtrTy, PtrTy}, false))
                    .getCallee());
            DumpFunc = dyn_cast<Function>(
                M->getOrInsertFunction(
                     "cfl_loop_dump_count",
                     FunctionType::get(VoidTy, {PtrTy, I1, I32, I32}, false))
                    .getCallee());
        }
        assert(PreheaderFunc && ExitingFunc && ExitFunc && DumpFunc);

        // Create locals to pass to wrappers
        AllocaInst *AITmp = new AllocaInst(Type::getInt1Ty(M->getContext()), 0,
                                           "loop_cfl_tmp",
                                           &*(F->getEntryBlock().getFirstInsertionPt()));
        AllocaInst *AICount =
            new AllocaInst(Type::getInt64Ty(M->getContext()), 0, "loop_cfl_count",
                           &*(F->getEntryBlock().getFirstInsertionPt()));
        const DataLayout &DL = AITmp->getParent()->getParent()->getParent()->getDataLayout();
        LLVMContext& C = AITmp->getContext();
        // Set lifetime start information
        llvm::IRBuilder<> BuilderStart(AITmp->getNextNode());
        BuilderStart.CreateLifetimeStart(AITmp, ConstantInt::get(Type::getInt64Ty(C), DL.getTypeAllocSize(AITmp->getAllocatedType())));
        BuilderStart.CreateLifetimeStart(AICount, ConstantInt::get(Type::getInt64Ty(C), DL.getTypeAllocSize(AICount->getAllocatedType())));

	        // Create per-loop exiting block global variable
	        Type* uLongType = IntegerType::getInt64Ty(M->getContext());
	        auto key = std::make_pair(branchBGID, branchIBID);
	        unsigned long init_value = 0;
	        auto It = maxCountInit.find(key);
	        if (It != maxCountInit.end())
	            init_value = It->second;
	        if (init_value == 0 && DefaultMaxCount > 0)
	            init_value = DefaultMaxCount;
	        ConstantInt* const_long_val = ConstantInt::get(M->getContext(), APInt(64,init_value));
	        std::string globalName = "loop_cfl_glob_" + ExitingBlock->getName().str() + F->getName().str() + std::to_string(getUniqueID());

        M->getOrInsertGlobal(globalName,uLongType);
        GlobalVariable *ExitingMaxCount = M->getNamedGlobal(globalName);
        ExitingMaxCount->setLinkage(GlobalValue::InternalLinkage);
        ExitingMaxCount->setAlignment(Align(8));
        ExitingMaxCount->setInitializer(const_long_val);
        if (init_value) {
            // oprint(protectedLoops << " " << globalName << " - BGID: " << branchBGID << " - IBID: " << branchIBID << " - init: " << init_value);
        }

        // Call preheader wrapper
        std::vector<Value*> PreheaderFuncArgs;
        PreheaderFuncArgs.push_back(AITmp);
        PreheaderFuncArgs.push_back(AICount);
        PreheaderFuncArgs.push_back(makeConstI32(C, branchBGID));
        PreheaderFuncArgs.push_back(makeConstI32(C, branchIBID));
        CallInst::Create(PreheaderFunc, PreheaderFuncArgs, "", PreheaderBlock->getTerminator());

        // If required, call the `count` dumping function
        if (DumpConf) {
            std::vector<Value*> DumpFuncArgs;
            DumpFuncArgs.push_back(AICount);
            DumpFuncArgs.push_back(LoopCond);
            DumpFuncArgs.push_back(makeConstI32(C, branchBGID));
            DumpFuncArgs.push_back(makeConstI32(C, branchIBID));
            CallInst::Create(DumpFunc, DumpFuncArgs, "", ExitingBlock->getTerminator());
        } else {
            // Call exiting wrapper
            std::vector<Value*> ExitingFuncArgs;
            ExitingFuncArgs.push_back(AICount);
            ExitingFuncArgs.push_back(ExitingMaxCount);
            ExitingFuncArgs.push_back(LoopCond);
            Instruction *ShouldExit = CallInst::Create(ExitingFunc, ExitingFuncArgs, "", ExitingBlock->getTerminator());
            ExitingBranch->setCondition(ShouldExit);
        }

        // Insert exit wrappers on *all* exit edges from the loop.
        // In LCSSA/loop-simplify form, a tainted loop can still have multiple
        // exit blocks (e.g., exit to epilogue vs. exit to an outer region).
        // We must restore `taken`/reset counters on every possible exit path,
        // otherwise we may leave dummy mode enabled after an early exit.
        llvm::SmallVector<llvm::BasicBlock*, 16> AllExitBlocks;
        L->getExitBlocks(AllExitBlocks);
        for (llvm::BasicBlock* EB : AllExitBlocks) {
            if (!EB)
                continue;
            for (llvm::BasicBlock* Pred : predecessors(EB)) {
                if (!Pred || !L->contains(Pred))
                    continue;

                BasicBlock *Tramp = BasicBlock::Create(
                    M->getContext(),
                    "loop_cfl_exit_" + EB->getName().str() + "_" +
                        Pred->getName().str(),
                    F, EB);

                std::vector<Value*> ExitFuncArgs;
                ExitFuncArgs.push_back(AITmp);
                ExitFuncArgs.push_back(AICount);
                CallInst *ExitCall = CallInst::Create(ExitFunc, ExitFuncArgs, "", Tramp);

                BranchInst::Create(EB, Tramp);

                // Lifetime end at the exit edge.
                llvm::IRBuilder<> BuilderEnd(Tramp->getTerminator());
                BuilderEnd.CreateLifetimeEnd(
                    AITmp, ConstantInt::get(Type::getInt64Ty(C),
                                            DL.getTypeAllocSize(AITmp->getAllocatedType())));
                BuilderEnd.CreateLifetimeEnd(
                    AICount, ConstantInt::get(Type::getInt64Ty(C),
                                              DL.getTypeAllocSize(AICount->getAllocatedType())));

                // Redirect the exiting edge Pred -> EB to Pred -> Tramp -> EB.
                Instruction *TI = Pred->getTerminator();
                assert(TI && TI->isTerminator());
                for (unsigned si = 0; si < TI->getNumSuccessors(); ++si) {
                    if (TI->getSuccessor(si) == EB)
                        TI->setSuccessor(si, Tramp);
                }
                EB->replacePhiUsesWith(Pred, Tramp);
            }
        }

        // blacklist of values we must be sure to not wrap
        std::set<Value*> blacklist;
        blacklist.insert(AITmp);
        blacklist.insert(AICount);
        blacklist.insert(ExitingMaxCount);
        // blacklist.insert(ShouldExit);
        blacklist.insert(LoopCond);

        // if we have only to dump count values we are done
        if (DumpConf) {
            // Add llvm.loop.unroll.disable metadata to the loop
            setLoopNoUnroll(L);
            return;
        }

        // We have to protect the values that are generated in the loop, and used
        // outside, since they may be dependent from the iteration count (we are
        // changing it), or they may be loaded from memory (we are shielding that
        // when in dummy mode)
        std::set<BasicBlock*> allBB(L->getBlocks().begin(), L->getBlocks().end());
        // assert that the preheader/exit-block is not included in the loop blocks,
        // since I do not trust myself reading docs
        // otherwise we may let some values escape, or wrap wrong ones
        assert(allBB.find(ExitBlock) == allBB.end());
        assert(allBB.find(PreheaderBlock) == allBB.end());

        // an escaping value and its uses
        std::map<Instruction*, std::set<Instruction*>> escapingValuesAndUses;
        GlobalVariable* CFL_taken_ref = nullptr;
        if (auto *GV = M->getNamedGlobal("taken")) {
            CFL_taken_ref = GV;
        } else {
            M->getOrInsertGlobal("taken", Type::getInt1Ty(M->getContext()));
            CFL_taken_ref = M->getNamedGlobal("taken");
        }
        assert(CFL_taken_ref);
        for(BasicBlock *BB: L->getBlocks()) {
            for (Instruction &I: *BB) {
                // If the instruction is the result of a call to `cfl_ptr_wrap`
                // we will have a pointer which is either `dummy` or valid, based
                // on `taken`. Using it in a load operation is safe, and we should
                // wrap only the load result, as well as using it in a store, since
                // it will not write to useful memory in dummy mode (in the
                // CFL), or will just touch memory (in the DFL model).
                if (CallInst *CI = dyn_cast<CallInst>(I.stripPointerCasts())) {
                    if (!CI->getCalledFunction() || CI->getCalledFunction()->getName() == "cfl_ptr_wrap" || CI->getCalledFunction()->getName() == "dfl_ptr_wrap") {
                        continue;
                    }
                }

                for(User* user: I.users()) {
                    Instruction *use = dyn_cast<Instruction>(user);
                    assert(use);

                    // collect all the values that are used outside, like any 
                    // value that may be defined of modified inside the loop, 
                    // and used in any way outside.
                    // This includes values defined in the loop body and:
                    //   1) Used outside
                    //   2) Stored into memory
                    //   3) Passed to nested calls
                    if (allBB.find(use->getParent()) == allBB.end()) {
                        // assert lcssa form to be sure we are in the right form
                        assert(isa<PHINode>(use));
                        static std::string lcssa_str = ".lcssa";
                        assert((use->getName().str().length() - lcssa_str.length()) >= 0);
                        // too strict! (e.g. val.lcssa1)
                        // assert(!use->getName().str().compare(use->getName().str().length() - lcssa_str.length(), lcssa_str.length(), lcssa_str));
                        assert(use->getName().contains(lcssa_str));
                        escapingValuesAndUses[&I].insert(use);
                    // NOTICE: a store should have been managed by CFL or DFL, but
                    // 1) DFL may leave stores unprotected if they do not leak
                    //    -> this is safe in an IF condition, but in a loop will
                    //       cause values getting updated in dummy iterations
                    // 2) CFL should protect all the stores, but we actually do 
                    //    not know if the user provided the `-cfl-no-mem-protect`
                    //    flag or not. Let's define a flag ourself that will make
                    //    the right thing by default
                    } else if ( ProtectStores && isa<StoreInst>(use)) {
                        // If the loop is executed always in dummy mode, we are 
                        // going to write to memory an invalid value, so make sure
                        // this is an output variable generated by the extract 
                        // functions pass: these variables are only used to propagate
                        // values across extracted basic blocks. If we are in dummy mode
                        // an invalid value will not matter, as it is not part of
                        // the original program
                        StoreInst* SI = dyn_cast<StoreInst>(use);
                        Value* ptr = SI->getPointerOperand();

                        // Make sure we are not invalidating a pointer!!
                        assert(&I != ptr);
                        // Checking that the value has no taint metadata means
                        // checking that it has been added after the tainting pass
                        // and that it is not part of the original program (e.g.
                        // added by branch extract). This may fail if we run this
                        // pass after CFL, but not after DFL, since CFL does not
                        // remove raw stores as DFL does, but just protects the ptr
                        assert(!hasTaintMetadata(use));
                        static std::string end_str = ".out";
                        assert((ptr->getName().str().length() - end_str.length()) >= 0);
                        // too strict (e.g. val.out1)
                        // assert(!ptr->getName().str().compare(ptr->getName().str().length() - end_str.length(), end_str.length(), end_str));
                        assert(ptr->getName().contains(end_str));
                        escapingValuesAndUses[&I].insert(use);
                    // We should protect also all the values that could escape 
                    // in inner calls
                    } else if (isa<CallInst>(use)) {
                        // This is the last way a value may escape: a store in a
                        // nested function, so better wrap also arguments to inner
                        // calls.
                        // Check that we are not dealing with an helper of ours
                        Function *F = dyn_cast<CallInst>(use)->getCalledFunction();
                        if (F == nullptr ||
                            (      F->getSection() == "dfl_code" 
                                || F->getSection() == "cfl_code" 
                                || F->getSection() == "cgc_code" 
                                || F->getSection() == "icp_code")) {
                            continue;
                        }
                        escapingValuesAndUses[&I].insert(use);
                    }
                }
            }
        }

        // Some synthetic loop bookkeeping values (tmp/count/cond) may end up
        // looking like "escaping" values after prior transforms. Never attempt
        // to wrap these; just ignore them.
        for (auto It = escapingValuesAndUses.begin();
             It != escapingValuesAndUses.end();) {
            if (blacklist.find(It->first->stripPointerCasts()) != blacklist.end()) {
                It = escapingValuesAndUses.erase(It);
                continue;
            }
            ++It;
        }

        // Transform each escaping value such that:
        // 1) a phi node keeps track of the last valid value in the loop
        // 2) a select on the escaping value, chooses if to update the value with
        //    the new one (when not in dummy mode) or if to preserve the old valid
        //    one (when in dummy mode)
        //
        // base:
        //   [...]
        // for:
        //   i = phi(0 from `base`, next from `for`)
        //   [...]
        //   next = i+1
        //   [...]
        //   cc = cmp next, cond
        //   brcc for, exit
        // exit:
        //   next.lcssa = phi(next from `for`)
        //
        // --> becomes
        //
        // base:
        //   [...]
        // for:
        //   i = phi(0 from `base`, next from `for`)
        //   last_valid_next = phi(undef from `base`, next from `for`)
        //   [...]
        //   _next = i+1
        //   next = select( taken? _next : last_valid_next )
        //   [...]
        //   cc = cmp next, cond
        //   brcc for, exit
        // exit:
        //   next.lcssa = phi(next from `for`)
        //
        // so that the escaping value stops updating when in dummy mode

        for (auto escapingValueAndUses : escapingValuesAndUses) {
            Instruction *escapingValue = escapingValueAndUses.first;
            auto Uses                  = escapingValueAndUses.second;
            Instruction* insertionPoint = escapingValue->getNextNode();

            // insert the phi node to track the last valid value in a circular 
            // dependency
            PHINode* lastValid = PHINode::Create(escapingValue->getType(), 2, 
                "last_valid", &*(HeaderBlock->getFirstInsertionPt()));
            // lastValid->addIncoming(UndefValue::get(escapingValue->getType()), 
            //     PreheaderBlock);
            lastValid->addIncoming(getPoison(escapingValue->getType(), PreheaderBlock->getParent()), 
                PreheaderBlock);

            // the escaping value might be a phi node, so make sure we will insert
            // the select after the escaping value, but also after all phis
            while(isa<PHINode>(insertionPoint))
                insertionPoint = insertionPoint->getNextNode();

            // Insert the select to choose if update the value or not
            // ...load the `taken` value first (it's a global)
            Type *TakenTy = CFL_taken_ref->getValueType();
            LoadInst* takenVal = new LoadInst(TakenTy, CFL_taken_ref, "", /*isVolatile=*/true,
                                              Align(1), insertionPoint);
            Value *boolTaken = takenVal;
            if (!boolTaken->getType()->isIntegerTy(1)) {
                boolTaken = new ICmpInst(insertionPoint, ICmpInst::ICMP_NE, takenVal,
                                         ConstantInt::get(takenVal->getType(), 0), "");
            }

            SelectInst *Sel = SelectInst::Create(boolTaken, escapingValue, lastValid, "escaping_val", insertionPoint);
            lastValid->addIncoming(Sel, ExitingBlock); 

            for (Instruction *use: Uses) {
                use->replaceUsesOfWith(escapingValue, Sel);
            }
        }

        // check that the exit check is still the last thing
        // if (!DumpConf) {
        //     assert(ShouldExit->getNextNode() == ExitingBranch);
        // }
        // Exit wrappers are inserted via per-edge trampolines; no single ExitCall.

        // Add llvm.loop.unroll.disable metadata to the loop
        setLoopNoUnroll(L);
    }

    bool runOnLoop(Loop *L, LPPassManager &LPM) override {
        assert(L->isLoopSimplifyForm());

        std::vector<Regex*> FunctionRegexes;
        if (Functions.empty())
            Functions.push_back("main");
        passListRegexInit(FunctionRegexes, Functions);

        Function *F = L->getHeader()->getParent();
        if (F->getSection() == "dfl_code" || F->getSection() == "cfl_code" 
                || F->getSection() == "cgc_code" || F->getSection() == "icp_code")
            return false;

        ++totalLoops;

        std::string FName = L->getHeader()->getParent()->getName().str();
        if (!passListRegexMatch(FunctionRegexes, FName))
            return false;

	        if (skipLoop(L)) {
	            return false;
	        }

	        // StrictCT: only linearize loops whose exit condition depends on secrets.
	        // The upstream pass can be applied to all loops, but that can be
	        // prohibitively expensive for fixed-count loops inside hot paths.
	        bool shouldProtect = false;
	        llvm::SmallVector<llvm::BasicBlock*, 16> ExitingBlocks;
	        L->getExitingBlocks(ExitingBlocks);
	        for(llvm::BasicBlock* BB: ExitingBlocks) {
	            llvm::BranchInst *EndBranch = dyn_cast<BranchInst>(BB->getTerminator());
	            if (!EndBranch || !EndBranch->isConditional())
	                continue;
	            if (getInstructionTaint(*EndBranch)) {
	                shouldProtect = true;
	                break;
	            }
	        }
	        if (!shouldProtect) {
	            return false;
	        }

	        ++protectedLoops;
	        loops_cfl(L);
	        return true;
	    }
  };

}

char LoopsCFLPass::ID = 0;
RegisterPass<LoopsCFLPass> MP("loops-cfl", "CFL Pass");
