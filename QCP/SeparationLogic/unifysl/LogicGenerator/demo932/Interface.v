Require Import Coq.Numbers.BinNums.
Require Import Coq.PArith.BinPosDef.
Require Import Logic.lib.PTree.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Import ListNotations.

Module Type LanguageSig.
(* primitive_types *)
  Parameter model : Type .
(* derived types *)
  Definition expr := (model -> Prop) .
(* primitive judgements *)
(* primitive connectives *)
  Parameter join : (model -> model -> model -> Prop) .
  Parameter is_unit : (model -> Prop) .
End LanguageSig.

Module Type DerivedNamesSig (Names: LanguageSig).
Import Names.
(* derived connectives *)
  Definition sepcon := (fun (x y : model -> Prop) (m : model) => exists m1 m2 : model, join m1 m2 m /\ x m1 /\ y m2) .
  Definition wand := (fun (x y : model -> Prop) (m : model) => forall m1 m2 : model, join m m1 m2 -> x m1 -> y m2) .
  Definition orp := (fun (x y : model -> Prop) (m : model) => x m \/ y m) .
  Definition andp := (fun (x y : model -> Prop) (m : model) => x m /\ y m) .
  Definition impp := (fun (x y : model -> Prop) (m : model) => x m -> y m) .
  Definition exp := (fun (A : Type) (x : A -> model -> Prop) (m : model) => exists a : A, x a m) .
  Definition allp := (fun (A : Type) (x : A -> model -> Prop) (m : model) => forall a : A, x a m) .
  Definition emp := (fun m : model => is_unit m) .
  Definition coq_prop := (fun (P : Prop) (_ : model) => P) .
  Definition truep := (fun _ : model => True) .
  Definition multi_imp := (fun (xs : list expr) (y : expr) => fold_right impp y xs) .
  Definition iter_sepcon := (fun xs : list expr => fold_left sepcon xs emp) .
(* derived judgements *)
  Definition derivable1 := (fun x y : model -> Prop => forall m : model, x m -> y m) .
  Definition logic_equiv := (fun x y : expr => derivable1 x y /\ derivable1 y x) .
End DerivedNamesSig.

Module Type PrimitiveRuleSig (Names: LanguageSig) (DerivedNames: DerivedNamesSig Names).
  Import Names DerivedNames.
  Axiom unit_join : (forall n : model, exists u : model, is_unit u /\ join n u n) .
  Axiom unit_spec : (forall n m u : model, is_unit u -> join n u m -> n = m) .
  Axiom join_comm : (forall m1 m2 m : model, join m1 m2 m -> join m2 m1 m) .
  Axiom join_assoc : (forall mx my mz mxy mxyz : model, join mx my mxy -> join mxy mz mxyz -> exists myz : model, join my mz myz /\ join mx myz mxyz) .
End PrimitiveRuleSig.

Module Type LogicTheoremSig (Names: LanguageSig) (DerivedNames: DerivedNamesSig Names) (Rules: PrimitiveRuleSig Names DerivedNames).
Import Names DerivedNames Rules.
Parameter Inline tree_pos : Type .
(* derived rules *)
  Axiom coq_prop_right : (forall (P : Prop) (x : expr), P -> derivable1 x (coq_prop P)) .
  Axiom coq_prop_left : (forall (P : Prop) (x : expr), (P -> derivable1 truep x) -> derivable1 (coq_prop P) x) .
  Axiom iter_sepcon_d1_left1 : (forall xs : list expr, derivable1 (iter_sepcon xs) (fold_left sepcon xs emp)) .
  Axiom iter_sepcon_d1_left2 : (forall xs : list expr, derivable1 (fold_left sepcon xs emp) (iter_sepcon xs)) .
  Axiom shallow_exp_right : (forall (A : Type) (P : expr) (Q : A -> expr) (x : A), derivable1 P (Q x) -> derivable1 P (exp A Q)) .
  Axiom shallow_exp_left : (forall (A : Type) (P : A -> expr) (Q : expr), (forall x : A, derivable1 (P x) Q) -> derivable1 (exp A P) Q) .
  Axiom shallow_allp_right : (forall (A : Type) (P : expr) (Q : A -> expr), (forall x : A, derivable1 P (Q x)) -> derivable1 P (allp A Q)) .
  Axiom shallow_allp_left : (forall (A : Type) (P : A -> expr) (Q : expr) (x : A), derivable1 (P x) Q -> derivable1 (allp A P) Q) . 
  Axiom sepcon_emp_left : (forall x : expr, derivable1 (sepcon x emp) x) .
  Axiom sepcon_emp_right : (forall x : expr, derivable1 x (sepcon x emp)) .
  Axiom derivable1_wand_sepcon_adjoint : (forall x y z : expr, derivable1 (sepcon x y) z <-> derivable1 x (wand y z)) .
  Axiom derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) .
  Axiom derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) .
  Axiom derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) .
  Axiom derivable1_truep_intros : (forall x : expr, derivable1 x truep) .
  Axiom derivable1_andp_intros : (forall x y z : expr, derivable1 x y -> derivable1 x z -> derivable1 x (andp y z)) .
  Axiom derivable1_andp_elim1 : (forall x y : expr, derivable1 (andp x y) x) .
  Axiom derivable1_andp_elim2 : (forall x y : expr, derivable1 (andp x y) y) .
  Axiom derivable1_orp_intros1 : (forall x y : expr, derivable1 x (orp x y)) .
  Axiom derivable1_orp_intros2 : (forall x y : expr, derivable1 y (orp x y)) .
  Axiom derivable1_orp_elim : (forall x y z : expr, derivable1 x z -> derivable1 y z -> derivable1 (orp x y) z) .
  Axiom derivable1_impp_andp_adjoint : (forall x y z : expr, derivable1 x (impp y z) <-> derivable1 (andp x y) z) .
  Axiom derivable1_refl : (forall x : expr, derivable1 x x) .
  Axiom derivable1_trans : (forall x y z : expr, derivable1 x y -> derivable1 y z -> derivable1 x z) .
  Axiom expr_deep : Set .
  Axiom impp_deep : (expr_deep -> expr_deep -> expr_deep) .
  Axiom sepcon_deep : (expr_deep -> expr_deep -> expr_deep) .
  Axiom emp_deep : expr_deep .
  Axiom varp_deep : (nat -> expr_deep) .
  Axiom var_pos : (expr -> option positive -> tree_pos) .
  Axiom sepcon_pos : (tree_pos -> tree_pos -> tree_pos) .
  Axiom cancel_mark : (expr_deep -> expr_deep -> tree_pos -> tree_pos -> tree_pos * tree_pos) .
  Axiom cancel_different : (tree_pos -> tree_pos -> expr) .
  Axiom cancel_same : (tree_pos -> tree_pos -> Prop) .
  Axiom restore : (tree_pos -> tree_pos -> expr) .
  Axiom sepcon_proper_logic_equiv : (Proper (logic_equiv ==> logic_equiv ==> logic_equiv) sepcon) .
  Axiom sepcon_comm_logic_equiv : (forall x y : expr, logic_equiv (sepcon x y) (sepcon y x)) .
  Axiom sepcon_assoc_logic_equiv : (forall x y z : expr, logic_equiv (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) .
  Axiom sepcon_emp_logic_equiv : (forall x : expr, logic_equiv (sepcon x emp) x) .
  Axiom ex_and1 : (forall (A : Type) (P : A -> expr) (Q : expr), derivable1 (andp (exp A P) Q) (exp A (fun x : A => andp (P x) Q))) .
  Axiom ex_and2 : (forall (A : Type) (P : expr) (Q : A -> expr), derivable1 (andp P (exp A Q)) (exp A (fun x : A => andp P (Q x)))) .
  Axiom ex_sepcon1 : (forall (A : Type) (P : A -> expr) (Q : expr), derivable1 (sepcon (exp A P) Q) (exp A (fun x : A => sepcon (P x) Q))) .
  Axiom ex_sepcon2 : (forall (A : Type) (P : expr) (Q : A -> expr), derivable1 (sepcon P (exp A Q)) (exp A (fun x : A => sepcon P (Q x)))) .
  Axiom iter_sepcon_flatten : (forall xs1 xs2 xs3 : list expr, derivable1 (iter_sepcon (xs1 ++ iter_sepcon xs2 :: xs3)) (iter_sepcon (xs1 ++ xs2 ++ xs3))) .
  Axiom sepcon_andp_prop1 : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (sepcon P (andp (coq_prop Q) R)) (andp (coq_prop Q) (sepcon P R))) .
  Axiom sepcon_andp_prop2 : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (andp (coq_prop Q) (sepcon P R)) (sepcon P (andp (coq_prop Q) R))) .
  Axiom sepcon_andp_prop3 : (forall (P Q : expr) (R : Prop), derivable1 (sepcon P (andp Q (coq_prop R))) (andp (coq_prop R) (sepcon P Q))) .
  Axiom sepcon_andp_prop4 : (forall (P Q : expr) (R : Prop), derivable1 (andp (coq_prop R) (sepcon P Q)) (sepcon P (andp Q (coq_prop R)))) .
  Axiom sepcon_andp_prop5 : (forall (P : Prop) (Q R : expr), derivable1 (sepcon (andp (coq_prop P) Q) R) (andp (coq_prop P) (sepcon Q R))) .
  Axiom sepcon_andp_prop6 : (forall (P : Prop) (Q R : expr), derivable1 (andp (coq_prop P) (sepcon Q R)) (sepcon (andp (coq_prop P) Q) R)) .
  Axiom sepcon_andp_prop7 : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (sepcon (andp P (coq_prop Q)) R) (andp (coq_prop Q) (sepcon P R))) .
  Axiom sepcon_andp_prop8 : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (andp (coq_prop Q) (sepcon P R)) (sepcon (andp P (coq_prop Q)) R)) .
  Axiom iter_sepcon_andp_prop : (forall (xs1 : list expr) (P : Prop) (x2 : expr) (xs3 : list expr), derivable1 (iter_sepcon (xs1 ++ andp (coq_prop P) x2 :: xs3)) (andp (coq_prop P) (iter_sepcon (xs1 ++ x2 :: xs3)))) .
  Axiom derivable1_sepcon_iter_sepcon1: (forall xs ys: list expr,
    derivable1 (sepcon (iter_sepcon xs) (iter_sepcon ys)) (iter_sepcon (xs ++ ys))).
  Axiom derivable1_sepcon_iter_sepcon2: (forall xs ys: list expr,
    derivable1 (iter_sepcon (xs ++ ys)) (sepcon (iter_sepcon xs) (iter_sepcon ys))).
  (* derived rules as Instance *)
  #[export] Existing Instance sepcon_proper_logic_equiv .
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

(* Module LogicTheorem (Names: LanguageSig) (DerivedNames: DerivedNamesSig Names) (Rules: PrimitiveRuleSig Names DerivedNames) <: LogicTheoremSig Names DerivedNames Rules. *)
Module Type LogicTheoremSig' (Names: LanguageSig) (DerivedNames: DerivedNamesSig Names) (Rules: PrimitiveRuleSig Names DerivedNames) <: LogicTheoremSig Names DerivedNames Rules.
  Import Names DerivedNames Rules.
(* aux primitive instances *)
  #[export] Instance M : Model := (Build_Model model) .
  #[export] Instance L : Language := (Build_Language expr) .
  #[export] Instance J : (Join model) := join .
  #[export] Instance U : (Unit model) := is_unit .
  #[export] Instance sepconL : (SepconLanguage L) := (Build_SepconLanguage L sepcon) .
  #[export] Instance wandL : (WandLanguage L) := (Build_WandLanguage L wand) .
  #[export] Instance orpL : (OrLanguage L) := (Build_OrLanguage L orp) .
  #[export] Instance andpL : (AndLanguage L) := (Build_AndLanguage L andp) .
  #[export] Instance minL : (MinimumLanguage L) := (Build_MinimumLanguage L impp) .
  #[export] Instance expL : (ShallowExistsLanguage L) := (Build_ShallowExistsLanguage L exp) .
  #[export] Instance allpL : (ShallowForallLanguage L) := (Build_ShallowForallLanguage L allp) .
  #[export] Instance empL : (EmpLanguage L) := (Build_EmpLanguage L emp) .
  #[export] Instance coq_prop_L : (CoqPropLanguage L) := (Build_CoqPropLanguage L coq_prop) .
  #[export] Instance truepL : (TrueLanguage L) := (Build_TrueLanguage L truep) .
  #[export] Instance iter_sepcon_L : (IterSepconLanguage L) := (Build_IterSepconLanguage L iter_sepcon) .
  #[export] Instance GammaD1 : (Derivable1 L) := (Build_Derivable1 L derivable1) .
  #[export] Instance GammaE : (LogicEquiv L) := (Build_LogicEquiv L logic_equiv) .
  #[export] Instance J_SA : (SeparationAlgebra model) := (Build_SeparationAlgebra model J join_comm join_assoc) .
  #[export] Instance UJR : (UnitJoinRelation model) := (Build_UnitJoinRelation model U J unit_join unit_spec) .
(* aux refl instances for derivation *)
  #[export] Instance sepconDef_join : (SepconDefinition_Join Join2Sepcon) := Join2Sepcon_Normal .
  #[export] Instance wandDef_join : (WandDefinition_Join Join2Wand) := Join2Wand_Normal .
  #[export] Instance orpDef_model : (OrpDefinition_Model orpL) := Model2Orp_Normal .
  #[export] Instance andpDef_model : (AndpDefinition_Model andpL) := Model2Andp_Normal .
  #[export] Instance imppDef_model : (ImppDefinition_Model minL) := Model2Impp_Normal .
  #[export] Instance expDef_model : (ExpDefinition_Model expL) := Model2Exp_Normal .
  #[export] Instance allpDef_model : 
  (AllpDefinition_Model allpL) := Model2Allp_Normal.
  #[export] Instance empDef_unit : (EmpDefinition_Unit Unit2Emp) := Unit2Emp_Normal .
  #[export] Instance coqpropDef_model : (CoqPropDefinition_Model coq_prop_L) := Model2CoqProp_Normal .
  #[export] Instance truepDef_model : (TrueDefinition_Model truepL) := Model2Truep_Normal .
  #[export] Instance iter_sepcon_DL : (IterSepconDefinition_left L) := FoldLeftSepcon2IterSepcon_Normal .
  #[export] Instance derivable1Def_model : (Derivable1Definition_Model GammaD1) := Model2Derivable1_Normal .
  #[export] Instance GammaED1 : (EquivDerivable1 L GammaD1 GammaE) := Derivable12Equiv_Normal .
(* aux derived instances *)
  #[export] Instance sepconD : (SepconDeduction L GammaD1) := SeparationAlgebra2SepconDeduction .
  #[export] Instance wandD : (WandDeduction L GammaD1) := SeparationAlgebra2WandDeduction .
  #[export] Instance adjD : (ImpAndAdjointDeduction L GammaD1) := Model2ImpAdjoint .
  #[export] Instance andpD : (AndDeduction L GammaD1) := Model2AndDeduction .
  #[export] Instance orpD : (OrDeduction L GammaD1) := Model2OrDeduction .
  #[export] Instance expD : (ShallowExistsDeduction L GammaD1) := Model2ExpDeduction .
  #[export] Instance allpD : (ShallowForallDeduction L GammaD1) := Model2AllDeduction.
  #[export] Instance bD : (BasicDeduction L GammaD1) := Model2BasicDeduction .
  #[export] Instance exp_andpD : deduction_exp_and := ExpDeduction2ExsitsAnd .
  #[export] Instance iter_sepcon_D1L : (IterSepconDeduction_left L GammaD1) := IterSepconFromDefToD1_L2L .
  #[export] Instance exp_sepconD : deduction_exp_sepcon := ExpDeduction2ExsitsSepcon .
  #[export] Instance empD : (EmpDeduction L GammaD1) := Model2EmpDeduction .
  #[export] Instance iter_sepcon_f : IterSepconFlatten := DeductionSepconFlatten .
  #[export] Instance coq_prop_D : (CoqPropDeduction L GammaD1) := Model2CoqPropDeduction .
  #[export] Instance truepD : (TrueDeduction L GammaD1) := Model2TrueDeduction .
  #[export] Instance sap : sepcon_andp_prop := Derived_sepcon_andp_prop .
  #[export] Instance sap_ext : sepcon_andp_prop_ext := Derived_sepcon_andp_prop_ext .
  #[export] Instance isap : Iter_sepcon_andp_prop := Derived_iter_sepcon_andp_prop .
Definition tree_pos : Type := tree_pos.
(* derived rules *)
  Definition coq_prop_right : (forall (P : Prop) (x : expr), P -> derivable1 x (coq_prop P)) := coq_prop_right .
  Definition coq_prop_left : (forall (P : Prop) (x : expr), (P -> derivable1 truep x) -> derivable1 (coq_prop P) x) := coq_prop_left .
  Definition iter_sepcon_d1_left1 : (forall xs : list expr, derivable1 (iter_sepcon xs) (fold_left sepcon xs emp)) := iter_sepcon_d1_left1 .
  Definition iter_sepcon_d1_left2 : (forall xs : list expr, derivable1 (fold_left sepcon xs emp) (iter_sepcon xs)) := iter_sepcon_d1_left2 .
  Definition shallow_exp_right : (forall (A : Type) (P : expr) (Q : A -> expr) (x : A), derivable1 P (Q x) -> derivable1 P (exp A Q)) := shallow_exp_right .
  Definition shallow_exp_left : (forall (A : Type) (P : A -> expr) (Q : expr), (forall x : A, derivable1 (P x) Q) -> derivable1 (exp A P) Q) := shallow_exp_left .
  Definition shallow_allp_right : (forall (A : Type) (P : expr) (Q : A -> expr), (forall x : A, derivable1 P (Q x)) -> derivable1 P (allp A Q)) := shallow_all_right.
  Definition shallow_allp_left : (forall (A : Type) (P : A -> expr) (Q : expr) (x : A), derivable1 (P x) Q -> derivable1 (allp A P) Q) :=
   shallow_all_left . 
  Definition sepcon_emp_left : (forall x : expr, derivable1 (sepcon x emp) x) := sepcon_emp_left .
  Definition sepcon_emp_right : (forall x : expr, derivable1 x (sepcon x emp)) := sepcon_emp_right .
  Definition derivable1_wand_sepcon_adjoint : (forall x y z : expr, derivable1 (sepcon x y) z <-> derivable1 x (wand y z)) := derivable1_wand_sepcon_adjoint .
  Definition derivable1_sepcon_comm : (forall x y : expr, derivable1 (sepcon x y) (sepcon y x)) := derivable1_sepcon_comm .
  Definition derivable1_sepcon_assoc1 : (forall x y z : expr, derivable1 (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) := derivable1_sepcon_assoc1 .
  Definition derivable1_sepcon_mono : (forall x1 x2 y1 y2 : expr, derivable1 x1 x2 -> derivable1 y1 y2 -> derivable1 (sepcon x1 y1) (sepcon x2 y2)) := derivable1_sepcon_mono .
  Definition derivable1_truep_intros : (forall x : expr, derivable1 x truep) := derivable1_truep_intros .
  Definition derivable1_andp_intros : (forall x y z : expr, derivable1 x y -> derivable1 x z -> derivable1 x (andp y z)) := derivable1_andp_intros .
  Definition derivable1_andp_elim1 : (forall x y : expr, derivable1 (andp x y) x) := derivable1_andp_elim1 .
  Definition derivable1_andp_elim2 : (forall x y : expr, derivable1 (andp x y) y) := derivable1_andp_elim2 .
  Definition derivable1_orp_intros1 : (forall x y : expr, derivable1 x (orp x y)) := derivable1_orp_intros1 .
  Definition derivable1_orp_intros2 : (forall x y : expr, derivable1 y (orp x y)) := derivable1_orp_intros2 .
  Definition derivable1_orp_elim : (forall x y z : expr, derivable1 x z -> derivable1 y z -> derivable1 (orp x y) z) := derivable1_orp_elim .
  Definition derivable1_impp_andp_adjoint : (forall x y z : expr, derivable1 x (impp y z) <-> derivable1 (andp x y) z) := derivable1_impp_andp_adjoint .
  Definition derivable1_refl : (forall x : expr, derivable1 x x) := derivable1_refl .
  Definition derivable1_trans : (forall x y z : expr, derivable1 x y -> derivable1 y z -> derivable1 x z) := derivable1_trans .
  Definition expr_deep : Set := expr_deep .
  Definition impp_deep : (expr_deep -> expr_deep -> expr_deep) := impp_deep .
  Definition sepcon_deep : (expr_deep -> expr_deep -> expr_deep) := sepcon_deep .
  Definition emp_deep : expr_deep := emp_deep .
  Definition varp_deep : (nat -> expr_deep) := varp_deep .
  Definition var_pos : (expr -> option positive -> tree_pos) := var_pos .
  Definition sepcon_pos : (tree_pos -> tree_pos -> tree_pos) := sepcon_pos .
  Definition cancel_mark : (expr_deep -> expr_deep -> tree_pos -> tree_pos -> tree_pos * tree_pos) := cancel_mark .
  Definition cancel_different : (tree_pos -> tree_pos -> expr) := cancel_different .
  Definition cancel_same : (tree_pos -> tree_pos -> Prop) := cancel_same .
  Definition restore : (tree_pos -> tree_pos -> expr) := restore .
  Definition sepcon_proper_logic_equiv : (Proper (logic_equiv ==> logic_equiv ==> logic_equiv) sepcon) := sepcon_proper_logic_equiv .
  Definition sepcon_comm_logic_equiv : (forall x y : expr, logic_equiv (sepcon x y) (sepcon y x)) := sepcon_comm_logic_equiv .
  Definition sepcon_assoc_logic_equiv : (forall x y z : expr, logic_equiv (sepcon x (sepcon y z)) (sepcon (sepcon x y) z)) := sepcon_assoc_logic_equiv .
  Definition sepcon_emp_logic_equiv : (forall x : expr, logic_equiv (sepcon x emp) x) := sepcon_emp_logic_equiv .
  Definition ex_and1 : (forall (A : Type) (P : A -> expr) (Q : expr), derivable1 (andp (exp A P) Q) (exp A (fun x : A => andp (P x) Q))) := ex_and1 .
  Definition ex_and2 : (forall (A : Type) (P : expr) (Q : A -> expr), derivable1 (andp P (exp A Q)) (exp A (fun x : A => andp P (Q x)))) := ex_and2 .
  Definition ex_sepcon1 : (forall (A : Type) (P : A -> expr) (Q : expr), derivable1 (sepcon (exp A P) Q) (exp A (fun x : A => sepcon (P x) Q))) := ex_sepcon1 .
  Definition ex_sepcon2 : (forall (A : Type) (P : expr) (Q : A -> expr), derivable1 (sepcon P (exp A Q)) (exp A (fun x : A => sepcon P (Q x)))) := ex_sepcon2 .
  Definition iter_sepcon_flatten : (forall xs1 xs2 xs3 : list expr, derivable1 (iter_sepcon (xs1 ++ iter_sepcon xs2 :: xs3)) (iter_sepcon (xs1 ++ xs2 ++ xs3))) := iter_sepcon_flatten .
  Definition sepcon_andp_prop1 : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (sepcon P (andp (coq_prop Q) R)) (andp (coq_prop Q) (sepcon P R))) := sepcon_andp_prop1 .
  Definition sepcon_andp_prop2 : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (andp (coq_prop Q) (sepcon P R)) (sepcon P (andp (coq_prop Q) R))) := sepcon_andp_prop2 .
  Definition sepcon_andp_prop3 : (forall (P Q : expr) (R : Prop), derivable1 (sepcon P (andp Q (coq_prop R))) (andp (coq_prop R) (sepcon P Q))) := sepcon_andp_prop3 .
  Definition sepcon_andp_prop4 : (forall (P Q : expr) (R : Prop), derivable1 (andp (coq_prop R) (sepcon P Q)) (sepcon P (andp Q (coq_prop R)))) := sepcon_andp_prop4 .
  Definition sepcon_andp_prop5 : (forall (P : Prop) (Q R : expr), derivable1 (sepcon (andp (coq_prop P) Q) R) (andp (coq_prop P) (sepcon Q R))) := sepcon_andp_prop5 .
  Definition sepcon_andp_prop6 : (forall (P : Prop) (Q R : expr), derivable1 (andp (coq_prop P) (sepcon Q R)) (sepcon (andp (coq_prop P) Q) R)) := sepcon_andp_prop6 .
  Definition sepcon_andp_prop7 : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (sepcon (andp P (coq_prop Q)) R) (andp (coq_prop Q) (sepcon P R))) := sepcon_andp_prop7 .
  Definition sepcon_andp_prop8 : (forall (P : expr) (Q : Prop) (R : expr), derivable1 (andp (coq_prop Q) (sepcon P R)) (sepcon (andp P (coq_prop Q)) R)) := sepcon_andp_prop8 .
  Definition iter_sepcon_andp_prop : (forall (xs1 : list expr) (P : Prop) (x2 : expr) (xs3 : list expr), derivable1 (iter_sepcon (xs1 ++ andp (coq_prop P) x2 :: xs3)) (andp (coq_prop P) (iter_sepcon (xs1 ++ x2 :: xs3)))) := iter_sepcon_andp_prop .
  Definition derivable1_sepcon_iter_sepcon1: (forall xs ys: list expr,
    derivable1 (sepcon (iter_sepcon xs) (iter_sepcon ys)) (iter_sepcon (xs ++ ys))) := derivable1_sepcon_iter_sepcon1.
  Definition derivable1_sepcon_iter_sepcon2: (forall xs ys: list expr,
    derivable1 (iter_sepcon (xs ++ ys)) (sepcon (iter_sepcon xs) (iter_sepcon ys))) := derivable1_sepcon_iter_sepcon2.
  Definition derivable1_wand_sepcon_modus_ponens1: forall (x y: expr), derivable1 (sepcon (wand x y) x) y := derivable1_wand_sepcon_modus_ponens1.
  Definition derivable1_wand_sepcon_modus_ponens2: forall (x y: expr), derivable1 (sepcon x (wand x y)) y := derivable1_wand_sepcon_modus_ponens2.
  Definition derivable1_wand_mono: forall (x1 x2 y1 y2: expr), derivable1 x2 x1 -> derivable1 y1 y2 -> derivable1 (wand x1 y1) (wand x2 y2) := derivable1_wand_mono.
  Definition wand_andp_logic_equiv: forall (x y z: expr), logic_equiv (wand x (andp y z)) (andp (wand x y) (wand x z)) := wand_andp_logic_equiv.

(* derived rules as Instance *)

Lemma logic_equiv_refl : (forall x : expr, logic_equiv x x) .
Proof. unfold logic_equiv;split;intros; apply derivable1_refl. Qed.

Lemma logic_equiv_symm : forall x y : expr, logic_equiv x y -> logic_equiv y x.
Proof. unfold logic_equiv;split;intros;apply H; auto. Qed.

Lemma logic_equiv_trans : forall x y z : expr, logic_equiv x y -> logic_equiv y z -> logic_equiv x z.
Proof. 
  unfold logic_equiv;intros;split;intros ; destruct H , H0 ; eapply derivable1_trans ; eauto. 
Qed.

#[export] Instance basicE : (BasicLogicEquiv L GammaE) := (Build_BasicLogicEquiv L GammaE logic_equiv_refl logic_equiv_symm logic_equiv_trans).

Lemma logic_equiv_derivable1 : (forall x y : expr, logic_equiv x y <-> derivable1 x y /\ derivable1 y x) .
Proof.
  unfold logic_equiv ; intros. tauto.
Qed. 

#[export] Instance equivD : (EquivDerivable1 L GammaD1 GammaE) := (Build_EquivDerivable1 L GammaD1 GammaE logic_equiv_derivable1).


#[export] Instance trueD : (TrueDeduction L GammaD1) := (Build_TrueDeduction L truepL GammaD1 derivable1_truep_intros).

#[export] Instance _Derivable_impp_rewrite :  RewriteRelation derivable1 := Derivable_impp_rewrite. 
  #[export] Instance _derivable1_refl_instance: Reflexive derivable1 := derivable1_refl_instance.
  #[export] Instance _derivable1_trans_instance : Transitive derivable1 := derivable1_trans_instance.
  #[export] Instance _logic_equiv_impp_rewrite : RewriteRelation logic_equiv := logic_equiv_impp_rewrite.
  #[export] Instance _logic_equiv_refl_instance: Reflexive logic_equiv := logic_equiv_refl_instance.
  #[export] Instance _logic_equiv_symm_instance: Symmetric logic_equiv := logic_equiv_symm_instance.
  #[export] Instance _logic_equiv_trans_instance: Transitive logic_equiv := logic_equiv_trans_instance.
  #[export] Instance _logic_equiv_trans_equiv: Equivalence logic_equiv := logic_equiv_trans_equiv.
  #[export] Instance _derivable1_proper_derivable1 : Proper ( derivable1 --> derivable1 ==> Basics.impl) derivable1 := derivable1_proper_derivable1. 
  #[export] Instance _logic_equiv_proper_logic_equiv : Proper (logic_equiv ==> logic_equiv ==> Basics.impl) logic_equiv := logic_equiv_proper_logic_equiv.
  #[export] Instance _logic_equiv_proper_derivable1 : Proper (logic_equiv ==> logic_equiv ==> Basics.impl) derivable1 := logic_equiv_proper_derivable1.
  #[export] Instance _andp_proper_derivable1 : Proper (derivable1 ==> derivable1 ==> derivable1) andp := andp_proper_derivable1 . 
  #[export] Instance _andp_proper_equiv : Proper (logic_equiv ==> logic_equiv ==> logic_equiv) andp .
  Proof.
    hnf ; unfold logic_equiv ; unfold derivable1 ; unfold andp; split ; destruct H , H0 ; intros ; split; destruct H3 ; auto.
  Qed.
  #[export] Instance _orp_proper_equiv: Proper (logic_equiv ==> logic_equiv ==> logic_equiv) orp.
  Proof.
  hnf ; unfold logic_equiv ; unfold derivable1 ; unfold orp; split ; destruct H , H0 ; intros ; destruct H3 ; auto.
  Qed. 
  #[export] Instance _orp_proper_derivable1: Proper (derivable1 ==> derivable1 ==> derivable1) orp.
  Proof.
  hnf ; unfold derivable1 ; unfold orp; intros ; hnf ; intros ;  destruct H1;auto.
  Qed. 
  #[export] Instance _sepcon_proper_logic_equiv : Proper (logic_equiv ==> logic_equiv ==> logic_equiv) sepcon := sepcon_proper_logic_equiv.
  #[export] Instance _sepcon_proper_derivable1 : (Proper (derivable1 ==> derivable1 ==> derivable1) sepcon) := sepcon_proper_derivable1.

  #[export] Instance _wand_proper_logic_equiv: Proper (logic_equiv ==> logic_equiv ==> logic_equiv) wand := wand_proper_logic_equiv.

  #[export] Instance _wand_proper_derivable1: Proper (derivable1 --> derivable1 ==> derivable1) wand := wand_proper_derivable1.

End LogicTheoremSig'.

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
