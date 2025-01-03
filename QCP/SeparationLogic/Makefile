CURRENT_DIR=.
COQBIN=

-include CONFIGURE

COQC=$(COQBIN)coqc$(SUF)
COQDEP=$(COQBIN)coqdep$(SUF)

DIRS = \
	Common CoreLang Frontend Asrtdef AuxiFun auxlibs Cdef compcert_lib SeparationLogic sets test unifysl StrategyLib fixedpoints
 
COQ_FLAG = -R Common SimpleC.Common -R CoreLang SimpleC.CoreLang -R Frontend SimpleC.Frontend -R SeparationLogic SimpleC.SL -R unifysl Logic -R Asrtdef SimpleC.ASRT -R AuxiFun SimpleC.ASRTFUN -R Cdef SimpleC.CSE -R sets SetsClass -R compcert_lib compcert.lib -R auxlibs AUXLib -R test SimpleC.PT -R examples SimpleC.EE -R StrategyLib SimpleC.StrategyLib -R fixedpoints FP -R MonadLib/monadnrm StateMonad.monadnrm -R MonadLib/monaderror StateMonad.monaderror

DEP_FLAG = -R Common SimpleC.Common -R CoreLang SimpleC.CoreLang -R Frontend SimpleC.Frontend -R SeparationLogic SimpleC.SL -R unifysl Logic -R Asrtdef SimpleC.ASRT -R AuxiFun SimpleC.ASRTFUN -R Cdef SimpleC.CSE -R sets SetsClass -R compcert_lib compcert.lib -R auxlibs AUXLib -R test SimpleC.PT -R examples SimpleC.EE -R StrategyLib SimpleC.StrategyLib -R fixedpoints FP -R MonadLib/monadnrm StateMonad.monadnrm -R MonadLib/monaderror StateMonad.monaderror


Common_FILES = \
  CTypes.v COps.v Notations.v

CoreLang_FILES = \
  CTypes.v CTypesDefDeclSem.v

Frontend_FILES = \
  CTypes.v CExprs.v CVarInit.v

Compcertlib_FILES = \
  Coqlib.v Integers.v Zbits.v

FIXPOINT_FILES = \
  Coqlib.v LiftConstructors.v  PartialOrder_Setoid.v  KnasterTarski.v  BourbakiWitt.v AllFramework.v SetsFixedpoints.v

Auxlibs_FILES = \
  int_auto.v Idents.v Feq.v Axioms.v VMap.v List_lemma.v relations.v \
  OrdersDecFact.v BinaryTree.v 

Sets_FILES = \
  SetsClass.v SetsClass_AxiomFree.v SetsDomain.v SetElement.v SetElementProperties.v RelsDomain.v SetProd.v SetsDomain_Classic.v

# The following files are commented out because they currently cannot be compiled
# Asrtdef_FILES = \
#     PolyType.v DepList.v ExprDef.v LocalDef.v PropDef.v SepDef.v Error.v AsrtDef.v DefFiles.v

# Cdef_FILES = \
#    Cexpr_def.v Cexpr_eval.v Cexpr_SymExec.v StateMachine.v Cstate_def.v Cexpr_semantics.v Cstatement_semantics.v Cexpr_val_helper.v Ceval_sound.v Assertion_denote.v

# Cdef_FILES = \
#    Cexpr_def.v Cexpr_eval.v Cstate_def.v Cexpr_val_helper.v Assertion_denote.v

Asrtdef_FILES = \
  PolyType.v

AuxiFun_FILES = \
  list_lemma.v

Unify_FILES = \
   Interface.v 

MonadNrm_Files = \
	monadbasic.v safeexec_lib.v mergeExample.v

MonadError_Files = \
	monadEbasic.v monadEwhile.v monadesafe_lib.v monadEhoare.v

SL_FILES = \
  CommonAssertion.v Assertion.v Mem.v ListLib.v ConAssertion.v \
  NestedCriticalSTS.v CriticalSTS.v \
  IntLib.v ArrayLib.v StoreAux.v pocv02.v SeparationLogic.v CNotation.v

StrategyLib_FILES = \
  DepList.v Mapping.v

Examples_FILES = \
  sll_split_while_goal.v sll_split_while_goal_check.v sll_split_while_proof_auto.v sll_split_while_proof_manual.v \
  poly_sll_lib.v poly_sll_goal.v poly_sll_goal_check.v poly_sll_proof_auto.v poly_sll_proof_manual.v \
  sll_lib.v sll_goal.v sll_goal_check.v sll_proof_auto.v sll_proof_manual.v \
  sll_merge_lib.v sll_merge_goal.v sll_merge_goal_check.v sll_merge_proof_auto.v sll_merge_proof_manual.v \
  sll_merge_rel_lib.v sll_merge_rel_goal.v sll_merge_rel_goal_check.v sll_merge_rel_proof_auto.v sll_merge_rel_proof_manual.v \
	int_array_merge_rel_lib.v int_array_merge_rel_goal.v int_array_merge_rel_goal_check.v int_array_merge_rel_proof_auto.v int_array_merge_rel_proof_manual.v \
	sll_insert_sort_lib.v sll_insert_sort_goal.v sll_insert_sort_goal_check.v sll_insert_sort_proof_auto.v sll_insert_sort_proof_manual.v \
	functional_queue_lib.v functional_queue_goal.v functional_queue_goal_check.v functional_queue_proof_auto.v functional_queue_proof_manual.v \
	dll_queue_lib.v dll_queue_goal.v dll_queue_goal_check.v dll_queue_proof_auto.v dll_queue_proof_manual.v \
	sll_queue_lib.v sll_queue_goal.v sll_queue_goal_check.v sll_queue_proof_auto.v sll_queue_proof_manual.v \
	simple_arith/abs_goal.v simple_arith/abs_goal_check.v simple_arith/abs_proof_auto.v simple_arith/abs_proof_manual.v \
	simple_arith/add_goal.v simple_arith/add_goal_check.v simple_arith/add_proof_auto.v simple_arith/add_proof_manual.v \
	simple_arith/max3_goal.v simple_arith/max3_goal_check.v simple_arith/max3_proof_auto.v simple_arith/max3_proof_manual.v \
	simple_arith/gcd_goal.v simple_arith/gcd_goal_check.v simple_arith/gcd_proof_auto.v simple_arith/gcd_proof_manual.v \
	simple_arith/Apos_lib.v simple_arith/Always_pos_goal.v simple_arith/Always_pos_goal_check.v simple_arith/Always_pos_proof_auto.v simple_arith/Always_pos_proof_manual.v \
	simple_arith/PDiv_lib.v simple_arith/div_test_goal.v simple_arith/div_test_goal_check.v simple_arith/div_test_proof_auto.v simple_arith/div_test_proof_manual.v \
	simple_arith/exgcd_goal.v simple_arith/exgcd_goal_check.v simple_arith/exgcd_proof_auto.v simple_arith/exgcd_proof_manual.v \
	simple_arith/Signed_unsigned_test_goal.v simple_arith/Signed_unsigned_test_goal_check.v simple_arith/Signed_unsigned_test_proof_auto.v simple_arith/Signed_unsigned_test_proof_manual.v \
	int_array_lib.v sum_goal.v sum_goal_check.v sum_proof_auto.v sum_proof_manual.v \
	bst_lib.v bst_insert_goal.v bst_insert_goal_check.v bst_insert_proof_auto.v bst_insert_proof_manual.v \
	bst_insert_rec_goal.v bst_insert_rec_goal_check.v bst_insert_rec_proof_auto.v bst_insert_rec_proof_manual.v \
	bst_fp_lib.v bst_fp_insert_goal.v bst_fp_insert_goal_check.v bst_fp_insert_proof_auto.v bst_fp_insert_proof_manual.v \
	bst_fp_delete_goal.v bst_fp_delete_goal_check.v bst_fp_delete_proof_auto.v bst_fp_delete_proof_manual.v \
	swap_lib.v swap_goal.v swap_goal_check.v swap_proof_auto.v swap_proof_manual.v \
	eval_lib.v eval_goal.v eval_goal_check.v eval_proof_auto.v eval_proof_manual.v \
	bst_delete_rec_goal.v bst_delete_rec_goal_check.v bst_delete_rec_proof_auto.v bst_delete_rec_proof_manual.v \
	bst_delete_rec2_goal.v bst_delete_rec2_goal_check.v bst_delete_rec2_proof_auto.v bst_delete_rec2_proof_manual.v \
	char_array_lib.v kmpExample.v kmp_rel_lib.v kmp_rel_goal.v kmp_rel_goal_check.v kmp_rel_proof_auto.v kmp_rel_proof_manual.v \
  critical_sll_lib.v concur_critical/concur_sll_goal.v concur_critical/concur_sll_proof_auto.v concur_critical/concur_sll_proof_manual.v concur_critical/concur_sll_goal_check.v \
  nested_critical_sll_lib.v concur_nested_critical/nconcur_sll_goal.v concur_nested_critical/nconcur_sll_proof_auto.v concur_nested_critical/nconcur_sll_proof_manual.v concur_nested_critical/nconcur_sll_goal_check.v \
  guarded_critical_sll_lib.v concur_guarded_critical/gconcur_sll_goal.v concur_guarded_critical/gconcur_sll_proof_auto.v concur_guarded_critical/gconcur_sll_proof_manual.v concur_guarded_critical/gconcur_sll_goal_check.v \
  fine_grained_sll_lib.v concur_fine_grained/fine_grained_sll_goal.v concur_fine_grained/fine_grained_sll_proof_auto.v concur_fine_grained/fine_grained_sll_proof_manual.v concur_fine_grained/fine_grained_sll_goal_check.v \
	fieldtest_lib.v fieldtest_goal.v fieldtest_goal_check.v fieldtest_proof_auto.v fieldtest_proof_manual.v \
	global_vars_goal.v global_vars_goal_check.v global_vars_proof_auto.v global_vars_proof_manual.v \
	triple_critical_sll_lib.v concur_triple_critical/triple_grained_sll_goal.v concur_triple_critical/triple_grained_sll_proof_auto.v concur_triple_critical/triple_grained_sll_proof_manual.v concur_triple_critical/triple_grained_sll_goal_check.v \

StrategyProof_FILES = \
	common_strategy_goal.v common_strategy_proof.v common_strategy_goal_check.v \
	fieldtest_strategy_goal.v fieldtest_strategy_proof.v fieldtest_strategy_goal_check.v \
	poly_sll_strategy_goal.v poly_sll_strategy_proof.v poly_sll_strategy_goal_check.v \
	sll_shape_strategy_goal.v sll_shape_strategy_proof.v sll_shape_strategy_goal_check.v \
	sll_strategy_goal.v sll_strategy_proof.v sll_strategy_goal_check.v \
	dll_queue_strategy_goal.v dll_queue_strategy_proof.v dll_queue_strategy_goal_check.v \
	functional_queue_strategy_goal.v functional_queue_strategy_proof.v functional_queue_strategy_goal_check.v \
	sll_queue_strategy_goal.v sll_queue_strategy_proof.v sll_queue_strategy_goal_check.v \
	int_array_strategy_goal.v int_array_strategy_proof.v int_array_strategy_goal_check.v \
	bst_strategy_goal.v bst_strategy_proof.v bst_strategy_goal_check.v \
	bst_fp_strategy_goal.v bst_fp_strategy_proof.v bst_fp_strategy_goal_check.v \
	safeexec_strategy_goal.v safeexec_strategy_proof.v safeexec_strategy_goal_check.v \
	eval_strategy_goal.v eval_strategy_proof.v eval_strategy_goal_check.v \
	char_array_strategy_goal.v char_array_strategy_proof.v char_array_strategy_goal_check.v \
	safeexecE_strategy_goal.v safeexecE_strategy_proof.v safeexecE_strategy_goal_check.v \
	concur_critical/common_strategy_goal.v concur_critical/common_strategy_proof.v concur_critical/common_strategy_goal_check.v \
	concur_critical/sll_strategy_goal.v concur_critical/sll_strategy_proof.v concur_critical/sll_strategy_goal_check.v \
	concur_critical/safeexec_strategy_goal.v concur_critical/safeexec_strategy_proof.v concur_critical/safeexec_strategy_goal_check.v \
	concur_critical/critical_strategy_goal.v concur_critical/critical_strategy_proof.v concur_critical/critical_strategy_goal_check.v \
	concur_nested_critical/common_strategy_goal.v concur_nested_critical/common_strategy_proof.v concur_nested_critical/common_strategy_goal_check.v \
	concur_nested_critical/sll_strategy_goal.v concur_nested_critical/sll_strategy_proof.v concur_nested_critical/sll_strategy_goal_check.v \
	concur_nested_critical/safeexec_strategy_goal.v concur_nested_critical/safeexec_strategy_proof.v concur_nested_critical/safeexec_strategy_goal_check.v \
	concur_nested_critical/nested_critical_strategy_goal.v concur_nested_critical/nested_critical_strategy_proof.v concur_nested_critical/nested_critical_strategy_goal_check.v \
	concur_guarded_critical/common_strategy_goal.v concur_guarded_critical/common_strategy_proof.v concur_guarded_critical/common_strategy_goal_check.v \
	concur_guarded_critical/sll_strategy_goal.v concur_guarded_critical/sll_strategy_proof.v concur_guarded_critical/sll_strategy_goal_check.v \
	concur_guarded_critical/safeexec_strategy_goal.v concur_guarded_critical/safeexec_strategy_proof.v concur_guarded_critical/safeexec_strategy_goal_check.v \
	concur_guarded_critical/guarded_critical_strategy_goal.v concur_guarded_critical/guarded_critical_strategy_proof.v concur_guarded_critical/guarded_critical_strategy_goal_check.v \
	concur_fine_grained/common_strategy_goal.v concur_fine_grained/common_strategy_proof.v concur_fine_grained/common_strategy_goal_check.v \
	concur_fine_grained/sll_strategy_goal.v concur_fine_grained/sll_strategy_proof.v concur_fine_grained/sll_strategy_goal_check.v \
	concur_fine_grained/safeexec_strategy_goal.v concur_fine_grained/safeexec_strategy_proof.v concur_fine_grained/safeexec_strategy_goal_check.v \
	concur_fine_grained/critical_strategy_goal.v concur_fine_grained/critical_strategy_proof.v concur_fine_grained/critical_strategy_goal_check.v \
	concur_triple_critical/common_strategy_goal.v concur_triple_critical/common_strategy_proof.v concur_triple_critical/common_strategy_goal_check.v \
	concur_triple_critical/sll_strategy_goal.v concur_triple_critical/sll_strategy_proof.v concur_triple_critical/sll_strategy_goal_check.v \
	concur_triple_critical/safeexec_strategy_goal.v concur_triple_critical/safeexec_strategy_proof.v concur_triple_critical/safeexec_strategy_goal_check.v \
	concur_triple_critical/triple_critical_strategy_goal.v concur_triple_critical/triple_critical_strategy_proof.v concur_triple_critical/triple_critical_strategy_goal_check.v \
	
Auto_Examples_FILES = \
	sll_shape_lib.v sll_auto_goal.v sll_auto_goal_check.v sll_auto_proof_auto.v sll_auto_proof_manual.v \

EXAMPLE = \
	$(SL_FILES:%.v=SeparationLogic/%.v) \
	$(Sets_FILES:%.v=sets/%.v) \
	$(Unify_FILES:%.v=unifysl/LogicGenerator/demo932/%.v) \
	$(MonadNrm_Files:%.v=MonadLib/monadnrm/%.v) \
	$(MonadError_Files:%.v=MonadLib/monaderror/%.v) \
	$(Examples_FILES:%.v=examples/%.v) \
	$(StrategyProof_FILES:%.v=examples/%.v) \
	$(Auto_Examples_FILES:%.v=examples/%.v) \

SYMEXEC = \
	$(Common_FILES:%.v=Common/%.v) \
	$(CoreLang_FILES:%.v=CoreLang/%.v) \
	$(Frontend_FILES:%.v=Frontend/%.v) \
	$(Compcertlib_FILES:%.v=compcert_lib/%.v) \
	$(FIXPOINT_FILES:%.v=fixedpoints/%.v) \
	$(Asrtdef_FILES:%.v=Asrtdef/%.v) \
	$(Cdef_FILES:%.v=Cdef/%.v) \
	$(AuxiFun_FILES:%.v=AuxiFun/%.v) \
	$(Auxlibs_FILES:%.v=auxlibs/%.v) \

AUXFILES = \
	$(SL_FILES:%.v=SeparationLogic/.%.aux) \
	$(Sets_FILES:%.v=sets/.%.aux) \
	$(Unify_FILES:%.v=unifysl/LogicGenerator/demo932/.%.aux) \
	$(MonadNrm_Files:%.v=MonadLib/monadnrm/.%.aux) \
	$(MonadError_Files:%.v=MonadLib/monaderror/.%.aux) \
	$(Examples_FILES:%.v=examples/.%.aux) \
	$(StrategyProof_FILES:%.v=examples/.%.aux) \
	$(Auto_Examples_FILES:%.v=examples/.%.aux) \
	$(Common_FILES:%.v=Common/.%.aux) \
	$(CoreLang_FILES:%.v=CoreLang/.%.aux) \
	$(Frontend_FILES:%.v=Frontend/.%.aux) \
	$(Compcertlib_FILES:%.v=compcert_lib/.%.aux) \
	$(Asrtdef_FILES:%.v=Asrtdef/.%.aux) \
	$(Cdef_FILES:%.v=Cdef/.%.aux) \
	$(AuxiFun_FILES:%.v=AuxiFun/.%.aux) \
	$(Auxlibs_FILES:%.v=auxlibs/.%.aux) \

$(EXAMPLE:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

$(SYMEXEC:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

all: \
	$(EXAMPLE:%.v=%.vo) \
	$(SYMEXEC:%.v=%.vo)  

examples : \
	$(EXAMPLE:%.v=%.vo) 

symexec : \
	$(SYMEXEC:%.v=%.vo) 

_CoqProject:
	@echo $(COQ_FLAG) > _CoqProject

depend:
	$(COQDEP) $(DEP_FLAG) $(EXAMPLE) $(SYMEXEC)  > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(EXAMPLE) $(SYMEXEC) > .depend

clean:
	@rm -f $(EXAMPLE:%.v=%.glob) $(SYMEXEC:%.v=%.glob)
	@rm -f $(EXAMPLE:%.v=%.vo) $(SYMEXEC:%.v=%.vo)
	@rm -f $(EXAMPLE:%.v=%.vok) $(SYMEXEC:%.v=%.vok)
	@rm -f $(EXAMPLE:%.v=%.vos) $(SYMEXEC:%.v=%.vos)
	@rm -f $(AUXFILES:.%.aux=.%.aux)
	@rm -f .depend

.PHONY: clean depend
.DEFAULT_GOAL := all

include .depend