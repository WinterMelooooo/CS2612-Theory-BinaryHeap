Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Import ListNotations.

Module Type LanguageSig.
(* primitive_types *)
  Parameter Inline expr : Type .
(* derived types *)
  Definition context := (expr -> Prop) .
(* primitive judgements *)
  Parameter derivable : (context -> expr -> Prop) .
(* primitive connectives *)
  Parameter falsep : expr .
  Parameter truep : expr .
  Parameter negp : (expr -> expr) .
  Parameter andp : (expr -> expr -> expr) .
  Parameter orp : (expr -> expr -> expr) .
  Parameter impp : (expr -> expr -> expr) .
End LanguageSig.

Module DerivedNames (Names: LanguageSig).
Include Names.
(* derived connectives *)
  Definition multi_imp := (fun (xs : list expr) (y : expr) => fold_right impp y xs) .
(* derived judgements *)
End DerivedNames.

Module Type PrimitiveRuleSig (Names: LanguageSig).
Include DerivedNames (Names).
  Axiom deduction_subst1 : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable (Union expr Phi (Singleton expr x)) y -> derivable Phi y) .
  Axiom derivable_by_contradiction : (forall (Phi : Ensemble expr) (x y : expr), derivable (Union expr Phi (Singleton expr (negp x))) y -> derivable (Union expr Phi (Singleton expr (negp x))) (negp y) -> derivable Phi x) .
  Axiom deduction_truep_intros : (forall Phi : context, derivable Phi truep) .
  Axiom deduction_falsep_elim : (forall (Phi : context) (x : expr), derivable Phi falsep -> derivable Phi x) .
  Axiom deduction_orp_intros1 : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi (orp x y)) .
  Axiom deduction_orp_intros2 : (forall (Phi : context) (x y : expr), derivable Phi y -> derivable Phi (orp x y)) .
  Axiom deduction_orp_elim : (forall (Phi : Ensemble expr) (x y z : expr), derivable (Union expr Phi (Singleton expr x)) z -> derivable (Union expr Phi (Singleton expr y)) z -> derivable (Union expr Phi (Singleton expr (orp x y))) z) .
  Axiom deduction_andp_intros : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi y -> derivable Phi (andp x y)) .
  Axiom deduction_andp_elim1 : (forall (Phi : context) (x y : expr), derivable Phi (andp x y) -> derivable Phi x) .
  Axiom deduction_andp_elim2 : (forall (Phi : context) (x y : expr), derivable Phi (andp x y) -> derivable Phi y) .
  Axiom deduction_modus_ponens : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi (impp x y) -> derivable Phi y) .
  Axiom deduction_impp_intros : (forall (Phi : Ensemble expr) (x y : expr), derivable (Union expr Phi (Singleton expr x)) y -> derivable Phi (impp x y)) .
  Axiom derivable_finite_witnessed : (forall (Phi : context) (y : expr), derivable Phi y -> exists xs : list expr, Forall Phi xs /\ derivable (fun x : expr => In x xs) y) .
  Axiom deduction_weaken : (forall (Phi Psi : Ensemble expr) (x : expr), Included expr Phi Psi -> derivable Phi x -> derivable Psi x) .
  Axiom derivable_assum : (forall (Phi : Ensemble expr) (x : expr), Ensembles.In expr Phi x -> derivable Phi x) .
End PrimitiveRuleSig.

Module Type LogicTheoremSig (Names: LanguageSig) (Rules: PrimitiveRuleSig Names).
Include Rules.
Parameter Inline tree_pos : Type .
(* derived rules *)
  Axiom deduction_contrapositivePP : (forall (Phi : Ensemble expr) (x y : expr), derivable (Union expr Phi (Singleton expr y)) x -> derivable (Union expr Phi (Singleton expr (negp x))) (negp y)) .
  Axiom deduction_contradiction_elim : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi (negp x) -> derivable Phi y) .
  Axiom deduction_double_negp_intros : (forall (Phi : context) (x : expr), derivable Phi x -> derivable Phi (negp (negp x))) .
  Axiom deduction_subst : (forall (Phi Psi : context) (y : expr), (forall x : expr, Psi x -> derivable Phi x) -> derivable (Union expr Phi Psi) y -> derivable Phi y) .
  Axiom deduction_impp_elim : (forall (Phi : context) (x y : expr), derivable Phi (impp x y) -> derivable (Union expr Phi (Singleton expr x)) y) .
  Axiom deduction_theorem : (forall (Phi : context) (x y : expr), derivable (Union expr Phi (Singleton expr x)) y <-> derivable Phi (impp x y)) .
  Axiom deduction_theorem_multi_imp : (forall (Phi : context) (xs : list expr) (y : expr), derivable (Union expr Phi (fun x : expr => In x xs)) y <-> derivable Phi (multi_imp xs y)) .
  Axiom derivable_impp_refl : (forall (Phi : context) (x : expr), derivable Phi (impp x x)) .
  Axiom deduction_left_impp_intros : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi (impp y x)) .
  Axiom derivable_modus_ponens : (forall (Phi : context) (x y : expr), derivable Phi (impp x (impp (impp x y) y))) .
  Axiom deduction_impp_trans : (forall (Phi : context) (x y z : expr), derivable Phi (impp x y) -> derivable Phi (impp y z) -> derivable Phi (impp x z)) .
  Axiom deduction_impp_arg_switch : (forall (Phi : context) (x y z : expr), derivable Phi (impp x (impp y z)) -> derivable Phi (impp y (impp x z))) .
  Axiom deduction_negp_fold : (forall (Phi : Ensemble expr) (x : expr), derivable (Union expr Phi (Singleton expr x)) falsep -> derivable Phi (negp x)) .
  Axiom deduction_negp_unfold : (forall (Phi : context) (x : expr), derivable Phi (negp x) -> derivable (Union expr Phi (Singleton expr x)) falsep) .
  Axiom expr_deep : Set .
  Axiom impp_deep : (expr_deep -> expr_deep -> expr_deep) .
  Axiom sepcon_deep : (expr_deep -> expr_deep -> expr_deep) .
  Axiom emp_deep : expr_deep .
  Axiom varp_deep : (nat -> expr_deep) .
  Axiom var_pos : (expr -> option positive -> tree_pos) .
  Axiom sepcon_pos : (tree_pos -> tree_pos -> tree_pos) .
  Axiom cancel_mark : (expr_deep -> expr_deep -> tree_pos -> tree_pos -> tree_pos * tree_pos) .
  Axiom deduction_and_neg1 : (forall (Phi : context) (P Q : expr), derivable Phi (negp P) -> derivable Phi (negp (andp P Q))) .
  Axiom deduction_and_neg2 : (forall (Phi : context) (P Q : expr), derivable Phi (negp Q) -> derivable Phi (negp (andp P Q))) .
  Axiom deduction_or_neg : (forall (Phi : context) (P Q : expr), derivable Phi (negp P) -> derivable Phi (negp Q) -> derivable Phi (negp (orp P Q))) .
  Axiom deduction_imp_neg1 : (forall (Phi : context) (P Q : expr), derivable Phi (negp P) -> derivable Phi (impp P Q)) .
  Axiom deduction_imp_neg2 : (forall (Phi : context) (P Q : expr), derivable Phi P -> derivable Phi (negp Q) -> derivable Phi (negp (impp P Q))) .
  Axiom deduction_false_neg : (forall Phi : context, derivable Phi (negp falsep)) .
(* derived rules as instance *)
End LogicTheoremSig.

Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.GeneralLogic.ProofTheory.TheoryOfSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.TheoryOfJudgement.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.ProofTheoryPatterns.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfIteratedConnectives.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfClassicalAxioms.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.ProofTheory.DerivedRules.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfCancel.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
Require Import Logic.SeparationLogic.ProofTheory.Corable.
Require Import Logic.SeparationLogic.ProofTheory.Deduction.
Require Import Logic.GeneralLogic.ProofTheory.BasicLogicEquiv.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.ShallowEmbedded.Join2Sepcon.
Require Import Logic.SeparationLogic.ShallowEmbedded.Model2CoqPropEmp.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.SeparationLogic.ShallowEmbedded.PredicateSeparationLogic.
Require Import Logic.ShallowQuantifierLogic.Syntax.
Require Import Logic.ShallowQuantifierLogic.ProofTheory.
Require Import Logic.ShallowQuantifierLogic.ModelConstrEX.
Require Import Logic.ShallowQuantifierLogic.ModelConstrALL.

Module LogicTheorem (Names: LanguageSig) (Rules: PrimitiveRuleSig Names) <: LogicTheoremSig Names Rules.
Include Rules.
(* aux primitive instances *)
  Instance L : Language := (Build_Language expr) .
  Instance falsepL : (FalseLanguage L) := (Build_FalseLanguage L falsep) .
  Instance truepL : (TrueLanguage L) := (Build_TrueLanguage L truep) .
  Instance negpL : (NegLanguage L) := (Build_NegLanguage L negp) .
  Instance andpL : (AndLanguage L) := (Build_AndLanguage L andp) .
  Instance orpL : (OrLanguage L) := (Build_OrLanguage L orp) .
  Instance minL : (MinimumLanguage L) := (Build_MinimumLanguage L impp) .
  Instance GammaD : (Derivable L) := (Build_Derivable L derivable) .
  Instance falsepSC : (FalseSequentCalculus L GammaD) := (Build_FalseSequentCalculus L falsepL GammaD deduction_falsep_elim) .
  Instance truepSC : (TrueSequentCalculus L GammaD) := (Build_TrueSequentCalculus L truepL GammaD deduction_truep_intros) .
  Instance bSC_weak : (BasicSequentCalculus_weak L GammaD) := (Build_BasicSequentCalculus_weak L GammaD deduction_weaken derivable_assum) .
  Instance bSC_subst1 : (BasicSequentCalculus_subst1 L GammaD) := (Build_BasicSequentCalculus_subst1 L GammaD deduction_subst1) .
  Instance bSC_fw : (BasicSequentCalculus_fw L GammaD) := (Build_BasicSequentCalculus_fw L GammaD derivable_finite_witnessed) .
  Instance cpSC : (ClassicalSequentCalculus L GammaD) := (Build_ClassicalSequentCalculus L negpL GammaD derivable_by_contradiction) .
  Instance andpSC : (AndSequentCalculus L GammaD) := (Build_AndSequentCalculus L andpL GammaD deduction_andp_intros deduction_andp_elim1 deduction_andp_elim2) .
  Instance orpSC : (OrSequentCalculus L GammaD) := (Build_OrSequentCalculus L orpL GammaD deduction_orp_intros1 deduction_orp_intros2 deduction_orp_elim) .
  Instance minSC : (MinimumSequentCalculus L GammaD) := (Build_MinimumSequentCalculus L minL GammaD deduction_modus_ponens deduction_impp_intros) .
(* aux refl instances for derivation *)
(* aux derived instances *)
  Instance bSC_subst : (BasicSequentCalculus_subst L GammaD) := Subst1FiniteWitness2Subst .
  Instance bSC : (BasicSequentCalculus L GammaD) := WeakSubst12BasicSequentCalculus .
  Instance inegpSC : (IntuitionisticNegSequentCalculus L GammaD) := Classical2Intuitionistic_cSC .
  Instance negpSCDerived : (deduction_derived_neg L GammaD) := SequentCalculus2DeductionDerivedNeg .
Definition tree_pos : Type := tree_pos.
(* derived rules *)
  Definition deduction_contrapositivePP : (forall (Phi : Ensemble expr) (x y : expr), derivable (Union expr Phi (Singleton expr y)) x -> derivable (Union expr Phi (Singleton expr (negp x))) (negp y)) := deduction_contrapositivePP .
  Definition deduction_contradiction_elim : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi (negp x) -> derivable Phi y) := deduction_contradiction_elim .
  Definition deduction_double_negp_intros : (forall (Phi : context) (x : expr), derivable Phi x -> derivable Phi (negp (negp x))) := deduction_double_negp_intros .
  Definition deduction_subst : (forall (Phi Psi : context) (y : expr), (forall x : expr, Psi x -> derivable Phi x) -> derivable (Union expr Phi Psi) y -> derivable Phi y) := deduction_subst .
  Definition deduction_impp_elim : (forall (Phi : context) (x y : expr), derivable Phi (impp x y) -> derivable (Union expr Phi (Singleton expr x)) y) := deduction_impp_elim .
  Definition deduction_theorem : (forall (Phi : context) (x y : expr), derivable (Union expr Phi (Singleton expr x)) y <-> derivable Phi (impp x y)) := deduction_theorem .
  Definition deduction_theorem_multi_imp : (forall (Phi : context) (xs : list expr) (y : expr), derivable (Union expr Phi (fun x : expr => In x xs)) y <-> derivable Phi (multi_imp xs y)) := deduction_theorem_multi_imp .
  Definition derivable_impp_refl : (forall (Phi : context) (x : expr), derivable Phi (impp x x)) := derivable_impp_refl .
  Definition deduction_left_impp_intros : (forall (Phi : context) (x y : expr), derivable Phi x -> derivable Phi (impp y x)) := deduction_left_impp_intros .
  Definition derivable_modus_ponens : (forall (Phi : context) (x y : expr), derivable Phi (impp x (impp (impp x y) y))) := derivable_modus_ponens .
  Definition deduction_impp_trans : (forall (Phi : context) (x y z : expr), derivable Phi (impp x y) -> derivable Phi (impp y z) -> derivable Phi (impp x z)) := deduction_impp_trans .
  Definition deduction_impp_arg_switch : (forall (Phi : context) (x y z : expr), derivable Phi (impp x (impp y z)) -> derivable Phi (impp y (impp x z))) := deduction_impp_arg_switch .
  Definition deduction_negp_fold : (forall (Phi : Ensemble expr) (x : expr), derivable (Union expr Phi (Singleton expr x)) falsep -> derivable Phi (negp x)) := deduction_negp_fold .
  Definition deduction_negp_unfold : (forall (Phi : context) (x : expr), derivable Phi (negp x) -> derivable (Union expr Phi (Singleton expr x)) falsep) := deduction_negp_unfold .
  Definition expr_deep : Set := expr_deep .
  Definition impp_deep : (expr_deep -> expr_deep -> expr_deep) := impp_deep .
  Definition sepcon_deep : (expr_deep -> expr_deep -> expr_deep) := sepcon_deep .
  Definition emp_deep : expr_deep := emp_deep .
  Definition varp_deep : (nat -> expr_deep) := varp_deep .
  Definition var_pos : (expr -> option positive -> tree_pos) := var_pos .
  Definition sepcon_pos : (tree_pos -> tree_pos -> tree_pos) := sepcon_pos .
  Definition cancel_mark : (expr_deep -> expr_deep -> tree_pos -> tree_pos -> tree_pos * tree_pos) := cancel_mark .
  Definition deduction_and_neg1 : (forall (Phi : context) (P Q : expr), derivable Phi (negp P) -> derivable Phi (negp (andp P Q))) := deduction_and_neg1 .
  Definition deduction_and_neg2 : (forall (Phi : context) (P Q : expr), derivable Phi (negp Q) -> derivable Phi (negp (andp P Q))) := deduction_and_neg2 .
  Definition deduction_or_neg : (forall (Phi : context) (P Q : expr), derivable Phi (negp P) -> derivable Phi (negp Q) -> derivable Phi (negp (orp P Q))) := deduction_or_neg .
  Definition deduction_imp_neg1 : (forall (Phi : context) (P Q : expr), derivable Phi (negp P) -> derivable Phi (impp P Q)) := deduction_imp_neg1 .
  Definition deduction_imp_neg2 : (forall (Phi : context) (P Q : expr), derivable Phi P -> derivable Phi (negp Q) -> derivable Phi (negp (impp P Q))) := deduction_imp_neg2 .
  Definition deduction_false_neg : (forall Phi : context, derivable Phi (negp falsep)) := deduction_false_neg .
(* derived rules as instance *)
End LogicTheorem.

(*Require Logic.PropositionalLogic.DeepEmbedded.Solver.
Module IPSolver (Names: LanguageSig).
  Import Names.
  Ltac ip_solve :=
    change expr with Base.expr;
    change provable with Base.provable;
    change impp with Syntax.impp;
    change andp with Syntax.andp;
    intros; Solver.SolverSound.ipSolver.
End IPSolver.*)
