Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ShallowEmbedded.PredicateAsLang.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.SeparationLogic.ShallowEmbedded.PredicateSeparationLogic.
Require Import Logic.SeparationLogic.Semantics.WeakSemantics.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.Sound.Sound_Flat. 
Require Import Logic.SeparationLogic.Model.SeparationAlgebra.
Require Import Logic.MinimumLogic.Semantics.Kripke.
Require Import Logic.SeparationLogic.Semantics.FlatSemantics.
Require Import Logic.lib.Ensembles_ext.
Require Import Logic.PropositionalLogic.ShallowEmbedded.PredicatePropositionalLogic.
Require Import Logic.MinimumLogic.Semantics.SemanticEquiv.
Require Import Logic.MinimumLogic.Semantics.Trivial.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.

Section M2COQPROP.
Context {M : Model}.

#[export] Instance Model_L : Language := Build_Language (model -> Prop).

Definition Model2CoqProp : CoqPropLanguage Model_L :=
  Build_CoqPropLanguage Model_L (fun (P : Prop) (m : model) => P).

Class CoqPropDefinition_Model (coq_prop_L : CoqPropLanguage Model_L) : Prop := {
  model2coqprop : forall (P : Prop) (m : model), coq_prop P m = P
}.

Lemma Model2CoqProp_Normal : CoqPropDefinition_Model Model2CoqProp.
Proof. constructor. reflexivity. Qed.

End M2COQPROP.

Section M2TRUE.
Context {M : Model}.

#[export] Instance model_L : Language := Build_Language (model -> Prop).

Definition Model2Truep : TrueLanguage model_L :=
  Build_TrueLanguage model_L (fun (m : model) => True).

Class TrueDefinition_Model (truepL : TrueLanguage model_L) : Prop := {
  model2truep : forall (m : model), truep m = True
}.

Lemma Model2Truep_Normal : TrueDefinition_Model Model2Truep.
Proof. constructor. reflexivity. Qed.

End M2TRUE.

Section U2EMP.

Context {M : Model} {U : Unit model}.

#[export] Instance L : Language := Build_Language (model -> Prop).

Definition Unit2Emp : EmpLanguage L :=
  Build_EmpLanguage Model_L (fun (m : model) => is_unit m).

Class EmpDefinition_Unit (empL : EmpLanguage L) : Prop := {
  unit2emp : forall (m : model), emp m = is_unit m
}.

Lemma Unit2Emp_Normal : EmpDefinition_Unit Unit2Emp.
Proof. constructor. reflexivity. Qed.

End U2EMP.

Section EmpD1FromModel.

Context {M : Model} {U : Unit model} {J : Join model} {UJR : UnitJoinRelation model}.

#[export] Instance L_emp : Language := Build_Language (model -> Prop).
#[export] Instance sepconL_emp : SepconLanguage L := Build_SepconLanguage L_emp 
  (fun x y => fun m => exists m1 m2, J m1 m2 m /\ x m1 /\ y m2).
#[export] Instance empL_emp : EmpLanguage L := Build_EmpLanguage L_emp 
  (fun (m : model) => is_unit m).
#[export] Instance GammaD1_emp : Derivable1 L_emp := Build_Derivable1 L_emp 
  (fun (x y : model -> Prop) => forall m, x m -> y m).

Lemma Model2EmpDeduction :
  EmpDeduction L_emp GammaD1_emp.
Proof.
  constructor;
  unfold sepcon, sepconL_emp;
  unfold emp, empL_emp;
  unfold derivable1, GammaD1_emp; intros.
  + destruct H as [m1 [m2 [? [? ?]]]].
    pose proof (unit_spec _ _ _ H1 H). subst m1; apply H0.
  + pose proof (unit_join m).
    destruct H0 as [u [? ?]].
    exists m, u. tauto.
Qed.

End EmpD1FromModel.

Section CoqPropD1FromModel.

Context {M : Model}.

#[export] Instance L_inj : Language := Build_Language (model -> Prop).
#[export] Instance CoqPropL_inj : CoqPropLanguage L_inj := Build_CoqPropLanguage L_inj 
  (fun (P : Prop) (m : model) => P).
#[export] Instance truepL_inj : TrueLanguage L_inj := Build_TrueLanguage L_inj 
  (fun (m : model) => True).
#[export] Instance GammaD1_inj : Derivable1 L_inj := Build_Derivable1 L_inj 
  (fun (x y : model -> Prop) => forall m, x m -> y m).

Lemma Model2CoqPropDeduction :
  CoqPropDeduction L_inj GammaD1_inj.
Proof.
  constructor; 
  unfold coq_prop, CoqPropL_inj, truep, truepL_inj, derivable1, GammaD1_inj; intros.
  + apply H. 
  + apply (H H0 m I).
Qed. 
  
End CoqPropD1FromModel.

Section TrueD1FromModel.

Context {M : Model}.

#[export] Instance L_tt : Language := Build_Language (model -> Prop).
#[export] Instance truepL_tt : TrueLanguage L_tt := Build_TrueLanguage L_tt 
  (fun (m : model) => True).
#[export] Instance GammaD1_tt : Derivable1 L_tt := Build_Derivable1 L_inj 
  (fun (x y : model -> Prop) => forall m, x m -> y m).

Lemma Model2TrueDeduction :
  TrueDeduction L_tt GammaD1_tt.
Proof. 
  constructor.
  unfold derivable1, GammaD1_tt, truep, truepL_tt.
  auto.
Qed. 

End TrueD1FromModel.







(* Section M2EMP.
Context {M : Model}.

Definition Model2Emp : EmpLanguage Model_L :=
  Build_EmpLanguage Model_L (fun (m : model) => forall n, ) *)



(* 
Definition Model2Emp : EmpLanguage Model_L :=
  Build_EmpLanguage Model_L (fun (m : model) => True).

Class EmpDefinition_Model (empL : EmpLanguage Model_L) : Prop := {
  model2emp : emp = (fun m => True)
}.
 *)
