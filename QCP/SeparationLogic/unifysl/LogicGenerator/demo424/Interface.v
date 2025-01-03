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
(* primitive judgements *)
  Parameter derivable1 : (expr -> expr -> Prop) .
(* primitive connectives *)
  Parameter impp : (expr -> expr -> expr) .
  Parameter andp : (expr -> expr -> expr) .
  Parameter orp : (expr -> expr -> expr) .
  Parameter exp : (forall A : Type, (A -> expr) -> expr) .
  Parameter coq_prop : (Prop -> expr) .
  Parameter truep : expr .
End LanguageSig.

Module DerivedNames (Names: LanguageSig).
Include Names.
(* derived connectives *)
  Definition multi_imp := (fun (xs : list expr) (y : expr) => fold_right impp y xs) .
(* derived judgements *)
End DerivedNames.

Module Type PrimitiveRuleSig (Names: LanguageSig).
Include DerivedNames (Names).
  Axiom coq_prop_right : (forall (P : Prop) (x : expr), P -> derivable1 x (coq_prop P)) .
  Axiom coq_prop_left : (forall (P : Prop) (x : expr), (P -> derivable1 truep x) -> derivable1 (coq_prop P) x) .
  Axiom shallow_exp_right : (forall (A : Type) (P : expr) (Q : A -> expr) (x : A), derivable1 P (Q x) -> derivable1 P (exp A Q)) .
  Axiom shallow_exp_left : (forall (A : Type) (P : A -> expr) (Q : expr), (forall x : A, derivable1 (P x) Q) -> derivable1 (exp A P) Q) .
  Axiom derivable1_orp_intros1 : (forall x y : expr, derivable1 x (orp x y)) .
  Axiom derivable1_orp_intros2 : (forall x y : expr, derivable1 y (orp x y)) .
  Axiom derivable1_orp_elim : (forall x y z : expr, derivable1 x z -> derivable1 y z -> derivable1 (orp x y) z) .
  Axiom derivable1_andp_intros : (forall x y z : expr, derivable1 x y -> derivable1 x z -> derivable1 x (andp y z)) .
  Axiom derivable1_andp_elim1 : (forall x y : expr, derivable1 (andp x y) x) .
  Axiom derivable1_andp_elim2 : (forall x y : expr, derivable1 (andp x y) y) .
  Axiom derivable1_impp_andp_adjoint : (forall x y z : expr, derivable1 x (impp y z) <-> derivable1 (andp x y) z) .
  Axiom derivable1_refl : (forall x : expr, derivable1 x x) .
  Axiom derivable1_trans : (forall x y z : expr, derivable1 x y -> derivable1 y z -> derivable1 x z) .
End PrimitiveRuleSig.

Module Type LogicTheoremSig (Names: LanguageSig) (Rules: PrimitiveRuleSig Names).
Include Rules.
Parameter Inline tree_pos : Type .
(* derived rules *)
  Axiom expr_deep : Set .
  Axiom impp_deep : (expr_deep -> expr_deep -> expr_deep) .
  Axiom sepcon_deep : (expr_deep -> expr_deep -> expr_deep) .
  Axiom emp_deep : expr_deep .
  Axiom varp_deep : (nat -> expr_deep) .
  Axiom var_pos : (expr -> option positive -> tree_pos) .
  Axiom sepcon_pos : (tree_pos -> tree_pos -> tree_pos) .
  Axiom cancel_mark : (expr_deep -> expr_deep -> tree_pos -> tree_pos -> tree_pos * tree_pos) .
  Axiom ex_and1 : (forall (A : Type) (P : A -> expr) (Q : expr), derivable1 (andp (exp A P) Q) (exp A (fun x : A => andp (P x) Q))) .
  Axiom ex_and2 : (forall (A : Type) (P : expr) (Q : A -> expr), derivable1 (andp P (exp A Q)) (exp A (fun x : A => andp P (Q x)))) .
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
  Instance minL : (MinimumLanguage L) := (Build_MinimumLanguage L impp) .
  Instance andpL : (AndLanguage L) := (Build_AndLanguage L andp) .
  Instance orpL : (OrLanguage L) := (Build_OrLanguage L orp) .
  Instance expL : (ShallowExistsLanguage L) := (Build_ShallowExistsLanguage L exp) .
  Instance coq_prop_L : (CoqPropLanguage L) := (Build_CoqPropLanguage L coq_prop) .
  Instance truepL : (TrueLanguage L) := (Build_TrueLanguage L truep) .
  Instance GammaD1 : (Derivable1 L) := (Build_Derivable1 L derivable1) .
  Instance andpD : (AndDeduction L GammaD1) := (Build_AndDeduction L andpL GammaD1 derivable1_andp_intros derivable1_andp_elim1 derivable1_andp_elim2) .
  Instance adjD : (ImpAndAdjointDeduction L GammaD1) := (Build_ImpAndAdjointDeduction L minL andpL GammaD1 derivable1_impp_andp_adjoint) .
  Instance orpD : (OrDeduction L GammaD1) := (Build_OrDeduction L orpL GammaD1 derivable1_orp_intros1 derivable1_orp_intros2 derivable1_orp_elim) .
  Instance expD : (ShallowExistsDeduction L GammaD1) := (Build_ShallowExistsDeduction L expL GammaD1 shallow_exp_right shallow_exp_left) .
  Instance bD : (BasicDeduction L GammaD1) := (Build_BasicDeduction L GammaD1 derivable1_refl derivable1_trans) .
  Instance coq_prop_D : (CoqPropDeduction L GammaD1) := (Build_CoqPropDeduction L truepL coq_prop_L GammaD1 coq_prop_right coq_prop_left) .
(* aux refl instances for derivation *)
(* aux derived instances *)
  Instance exp_andpD : deduction_exp_and := ExpDeduction2ExsitsAnd .
Definition tree_pos : Type := tree_pos.
(* derived rules *)
  Definition expr_deep : Set := expr_deep .
  Definition impp_deep : (expr_deep -> expr_deep -> expr_deep) := impp_deep .
  Definition sepcon_deep : (expr_deep -> expr_deep -> expr_deep) := sepcon_deep .
  Definition emp_deep : expr_deep := emp_deep .
  Definition varp_deep : (nat -> expr_deep) := varp_deep .
  Definition var_pos : (expr -> option positive -> tree_pos) := var_pos .
  Definition sepcon_pos : (tree_pos -> tree_pos -> tree_pos) := sepcon_pos .
  Definition cancel_mark : (expr_deep -> expr_deep -> tree_pos -> tree_pos -> tree_pos * tree_pos) := cancel_mark .
  Definition ex_and1 : (forall (A : Type) (P : A -> expr) (Q : expr), derivable1 (andp (exp A P) Q) (exp A (fun x : A => andp (P x) Q))) := ex_and1 .
  Definition ex_and2 : (forall (A : Type) (P : expr) (Q : A -> expr), derivable1 (andp P (exp A Q)) (exp A (fun x : A => andp P (Q x)))) := ex_and2 .
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