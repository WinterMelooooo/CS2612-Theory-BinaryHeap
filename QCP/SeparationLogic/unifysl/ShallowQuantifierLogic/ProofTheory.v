Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.RewriteClass.
Require Import Logic.ShallowQuantifierLogic.Syntax.
Require Import Logic.MetaLogicInj.Syntax.
Require Import Morphisms.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Class ShallowExistsDeduction (L : Language) {exL : ShallowExistsLanguage L} (Gamma : Derivable1 L) := {
  shallow_exp_right : forall (A : Type) (P : expr) (Q : A -> expr) (x : A),
    P |-- (Q x) -> P |-- (exp Q);
  shallow_exp_left : forall (A : Type) (P : A -> expr) (Q : expr),
    (forall x, (P x) |-- Q) -> (exp P) |-- Q;
}.

Class ShallowForallDeduction (L : Language) {allL : ShallowForallLanguage L} (Gamma : Derivable1 L) := {
  shallow_all_right : forall (A : Type) (P : expr) (Q : A -> expr),
    (forall x, P |-- (Q x)) -> P |-- (allp Q);
  shallow_all_left : forall (A : Type) (P : A -> expr) (Q : expr) (x : A),
    P x |-- Q -> (allp P) |-- Q;
}.

Require Import Logic.GeneralLogic.ProofTheory.BasicDeduction.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.IterSepcon.
Require Import Logic.MetaLogicInj.ProofTheory.ProofRules.

Section ExistsDeductionRulesAnd.

Context {L : Language}
        {minL : MinimumLanguage L}
        {andL : AndLanguage L}
        {exL : ShallowExistsLanguage L}
        {Gamma : Derivable1 L}
        {andpD : AndDeduction L Gamma}
        {bD: BasicDeduction L Gamma}
        {exD : ShallowExistsDeduction L Gamma}
        {adjD: ImpAndAdjointDeduction L Gamma}
        .
        
Lemma ex_and0 : forall {A : Type} (P Q : A -> expr),
  exp (fun a => (P a) && (Q a)) |-- (exp P) && (exp Q).
Proof. 
  intros.
  apply derivable1_andp_intros.
  + apply shallow_exp_left. intros. 
    eapply derivable1_trans; [apply derivable1_andp_elim1 | ].
    eapply shallow_exp_right. apply derivable1_refl.
  + apply shallow_exp_left. intros.
    eapply derivable1_trans; [apply derivable1_andp_elim2 | ].
    eapply shallow_exp_right. apply derivable1_refl.
Qed.

Lemma ex_and1' : forall {A : Type} (P : A -> expr) (Q : expr),
  exp (fun x => (P x && Q)) |-- ((exp P) && Q).
Proof. 
  intros. apply derivable1_andp_intros.
  + apply shallow_exp_left. intros.
    eapply derivable1_trans; [apply derivable1_andp_elim1 | ].
    eapply shallow_exp_right. apply derivable1_refl.
  + apply shallow_exp_left. intros. 
    apply derivable1_andp_elim2.
Qed.

Lemma ex_and2' : forall {A : Type} (P : expr) (Q : A -> expr),
  exp (fun x => (P && Q x)) |-- (P && (exp Q)).
Proof.
  intros. apply derivable1_andp_intros.
  + apply shallow_exp_left. intros.
    apply derivable1_andp_elim1.
  + apply shallow_exp_left. intros.
    eapply derivable1_trans; [apply derivable1_andp_elim2 | ].
    eapply shallow_exp_right. apply derivable1_refl.
Qed.

Lemma ex_and1_ : forall (A : Type) (P : A -> expr) (Q : expr), 
  ((exp P) && Q) |-- exp (fun x => (P x && Q)).
Proof. 
  intros.
  rewrite <- derivable1_impp_andp_adjoint.
  apply shallow_exp_left. intros. rewrite derivable1_impp_andp_adjoint.
  eapply shallow_exp_right.
  apply derivable1_andp_intros; [| apply derivable1_andp_elim2].
  eapply derivable1_trans; [apply derivable1_andp_elim1 | apply derivable1_refl].
Qed.

Lemma ex_and2_ : forall (A : Type) (P : expr) (Q : A -> expr),
  (P && (exp Q)) |-- exp (fun x => (P && Q x)).
Proof. 
  intros.
  eapply derivable1_trans; [apply derivable1_andp_comm |].
  rewrite <- derivable1_impp_andp_adjoint.
  apply shallow_exp_left. intros. rewrite derivable1_impp_andp_adjoint.
  eapply shallow_exp_right.
  apply derivable1_andp_intros; [apply derivable1_andp_elim2 |].
  eapply derivable1_trans; [apply derivable1_andp_elim1 | apply derivable1_refl]. 
Qed.

Class deduction_exp_and : Type := {
  ex_and1 : forall (A : Type) (P : A -> expr) (Q : expr), 
  ((exp P) && Q) |-- exp (fun x => (P x && Q));
  ex_and2 : forall (A : Type) (P : expr) (Q : A -> expr),
  (P && (exp Q)) |-- exp (fun x => (P && Q x));
}.

Lemma ExpDeduction2ExsitsAnd : deduction_exp_and.
Proof. 
  constructor.
  + apply ex_and1_.
  + apply ex_and2_.
Qed.

End ExistsDeductionRulesAnd.

Section ExistsDeductionRulesSepcon.

Context {L : Language}
        {sepconL : SepconLanguage L}
        {wandL : WandLanguage L}
        {exL : ShallowExistsLanguage L}
        {Gamma : Derivable1 L}
        {sepconD : SepconDeduction L Gamma}
        {bD: BasicDeduction L Gamma}
        {exD : ShallowExistsDeduction L Gamma}
        {wandD : WandDeduction L Gamma}
        .

Lemma ex_sepcon1_ : forall (A : Type) (P : A -> expr) (Q : expr),
  ((exp P) * Q) |-- exp (fun x => (P x * Q)).
Proof. 
  intros.
  rewrite derivable1_wand_sepcon_adjoint.
  apply shallow_exp_left. intros. rewrite <- derivable1_wand_sepcon_adjoint.
  eapply shallow_exp_right.
  apply derivable1_sepcon_mono; apply derivable1_refl.
Qed.

Lemma ex_sepcon2_ : forall (A : Type) (P : expr) (Q : A -> expr),
  (P * (exp Q)) |-- exp (fun x => (P * Q x)).
Proof.
  intros.
  eapply derivable1_trans; [apply derivable1_sepcon_comm |].
  rewrite derivable1_wand_sepcon_adjoint.
  apply shallow_exp_left. intros. rewrite <- derivable1_wand_sepcon_adjoint.
  eapply shallow_exp_right.
  eapply derivable1_trans; [apply derivable1_sepcon_comm |].
  apply derivable1_sepcon_mono; apply derivable1_refl.
Qed.

Class deduction_exp_sepcon : Type := {
  ex_sepcon1 : forall (A : Type) (P : A -> expr) (Q : expr),
  ((exp P) * Q) |-- exp (fun x => (P x * Q));
  ex_sepcon2 : forall (A : Type) (P : expr) (Q : A -> expr),
  (P * (exp Q)) |-- exp (fun x => (P * Q x));
}.

Lemma ExpDeduction2ExsitsSepcon : deduction_exp_sepcon.
Proof. 
  constructor.
  + apply ex_sepcon1_.
  + apply ex_sepcon2_.
Qed.

End ExistsDeductionRulesSepcon.

Section IterSepconDerivedRules.

Context {L : Language}
        {sepconL : SepconLanguage L}
        {empL : EmpLanguage L}
        {itersepconL : IterSepconLanguage L}
        {GammaD1 : Derivable1 L}
        {bD: BasicDeduction L GammaD1}
        {sepconD : SepconDeduction L GammaD1}
        {empD : EmpDeduction L GammaD1}
        {itersepconD : IterSepconDeduction_left L GammaD1}
        
        .

(* fold_left congruence *)
(* itersepcon (a :: l) = a * itersepcon (l) *)

Lemma fold_left_prop : forall {A : Type} (f : A -> A -> A) a b l ,
  (forall x y z, f (f x y) z = f x (f y z)) ->
  fold_left f l (f a b) = f a (fold_left f l b).
Proof. 
  intros. revert a b. induction l as [| a' l'].
  + simpl. reflexivity.
  + intros. simpl. rewrite <- IHl'. rewrite H. reflexivity.
Qed.

Lemma fold_left_sepcon_cong : forall l a b,
  a |-- b ->  
  fold_left sepcon l a |-- fold_left sepcon l b.
Proof.
  intros. revert a b H. induction l as [| a' l'].
  + simpl. tauto.
  + simpl. intros. apply IHl'.
    apply derivable1_sepcon_mono; [apply H | apply derivable1_refl].
Qed. 

Lemma derivable1_sepcon_assoc2 : forall a b c, 
  a * b * c |-- a * (b * c).
Proof.
  intros. 
  rewrite derivable1_sepcon_comm.
  rewrite derivable1_sepcon_assoc1.  
  rewrite <- (derivable1_sepcon_comm (b * c) a).
  rewrite <- (derivable1_sepcon_assoc1 b c a).
  rewrite <- (derivable1_sepcon_comm (c * a) b).
  apply derivable1_refl.
Qed.

Lemma fold_left_prop_sepcon1 : forall a b l, 
  fold_left sepcon l (a * b) |-- a * fold_left sepcon l b.
Proof.
  intros. revert a b. induction l as [| a' l'].
  + intros. simpl. reflexivity.
  + intros. simpl. rewrite <- IHl'.
    apply fold_left_sepcon_cong.
    apply derivable1_sepcon_assoc2.
Qed. 

Lemma fold_left_prop_sepcon2 : forall a b l,
  a * fold_left sepcon l b |-- fold_left sepcon l (a * b).
Proof. 
  intros. revert a b. induction l as [| a' l'].
  + intros. simpl. reflexivity.
  + intros. simpl. rewrite IHl'.
    apply fold_left_sepcon_cong.
    apply derivable1_sepcon_assoc1.
Qed.

Lemma itersepcon_cons : forall (a : expr) (l : list expr),
  iter_sepcon (a :: l) |-- a * iter_sepcon l /\
  a * iter_sepcon l |-- iter_sepcon (a :: l).
Proof. 
  intros. split. 
  + rewrite iter_sepcon_d1_left1. simpl.
    rewrite <- iter_sepcon_d1_left2. simpl.
    apply (derivable1_trans _ (fold_left sepcon l (a * emp))).
    { apply fold_left_sepcon_cong. apply derivable1_sepcon_comm. }
    rewrite fold_left_prop_sepcon1.
    apply derivable1_refl.
  + rewrite iter_sepcon_d1_left1. simpl.
    rewrite <- iter_sepcon_d1_left2. simpl.
    apply (derivable1_trans _ (fold_left sepcon l (a * emp))).
    2:{ apply fold_left_sepcon_cong. apply derivable1_sepcon_comm. }
    rewrite fold_left_prop_sepcon2.
    apply derivable1_refl.
Qed.

Definition itersepcon_cons1 := fun a l => proj1 (itersepcon_cons a l).
Definition itersepcon_cons2 := fun a l => proj2 (itersepcon_cons a l).

Lemma itersepcon_app : forall l1 l2,
  iter_sepcon l1 * iter_sepcon l2 |-- iter_sepcon (l1 ++ l2) /\
  iter_sepcon (l1 ++ l2) |-- iter_sepcon l1 * iter_sepcon l2.
Proof. 
  intros l1. induction l1 as [|a1 l1']; intros.
  + simpl. split. 
    - apply (derivable1_trans _ (emp * iter_sepcon l2)).
      { apply derivable1_sepcon_mono; [| apply derivable1_refl].
        rewrite iter_sepcon_d1_left1. simpl. apply derivable1_refl. }
      rewrite derivable1_sepcon_comm. apply sepcon_emp_left.
    - apply (derivable1_trans _ (emp * iter_sepcon l2)).
      { rewrite <- (derivable1_sepcon_comm (iter_sepcon l2) emp).
        apply sepcon_emp_right. }
      apply derivable1_sepcon_mono; [| apply derivable1_refl].
      rewrite <- iter_sepcon_d1_left2. simpl. apply derivable1_refl.
  + simpl. split.
    - rewrite itersepcon_cons1.
      rewrite <- itersepcon_cons2.
      rewrite derivable1_sepcon_assoc2.
      apply derivable1_sepcon_mono; [apply derivable1_refl |].
      apply (proj1 (IHl1' _)).
    - rewrite itersepcon_cons1.
      rewrite <- itersepcon_cons2.
      rewrite <- derivable1_sepcon_assoc1.
      apply derivable1_sepcon_mono; [apply derivable1_refl |].
      apply (proj2 (IHl1' _)).
Qed.

Definition itersepcon_app1 := fun l1 l2 => proj1 (itersepcon_app l1 l2).
Definition itersepcon_app2 := fun l1 l2 => proj2 (itersepcon_app l1 l2).

Theorem itersepcon_flatten_ : forall xs1 xs2 xs3,
  iter_sepcon (xs1 ++ (iter_sepcon xs2 :: xs3)) |--
  iter_sepcon (xs1 ++ xs2 ++ xs3).
Proof. 
  intros.
  induction xs1 as [| a1' xs1']; simpl.
  + rewrite itersepcon_cons1.
    apply itersepcon_app1.
  + rewrite itersepcon_cons1.
    rewrite <- itersepcon_cons2.
    apply derivable1_sepcon_mono; [apply derivable1_refl |].
    apply IHxs1'.
Qed.

Class IterSepconFlatten : Type := {
  iter_sepcon_flatten : forall xs1 xs2 xs3,
    iter_sepcon (xs1 ++ (iter_sepcon xs2 :: xs3)) |--
    iter_sepcon (xs1 ++ xs2 ++ xs3);
}.

Lemma DeductionSepconFlatten : IterSepconFlatten.
Proof. constructor. intros. apply itersepcon_flatten_. Qed.

Context {exL : ShallowExistsLanguage L}
        {exD : ShallowExistsDeduction L GammaD1}
        {exp_sepcon : deduction_exp_sepcon}
        .

Theorem itersepcon_ex {A : Type} : forall 
  (xs1 : list expr) (x : A -> expr) (xs3 : list expr), 
  iter_sepcon (xs1 ++ (exp x :: xs3)) |-- 
  exp (fun a => iter_sepcon (xs1 ++ (x a) :: xs3)).
Proof. 
  intros.
  rewrite itersepcon_app2.
  rewrite itersepcon_cons1.
  rewrite derivable1_sepcon_assoc1.
  rewrite ex_sepcon2.
  rewrite ex_sepcon1.
  apply shallow_exp_left. intros.
  eapply shallow_exp_right.
  rewrite <- itersepcon_app1.
  rewrite <- itersepcon_cons2.
  rewrite <- derivable1_sepcon_assoc2.
  apply derivable1_refl.
Qed.

Context {truepL : TrueLanguage L}
        {truepD : TrueDeduction L GammaD1}
        {coq_prop_L : CoqPropLanguage L}
        {coq_prop_D : CoqPropDeduction L GammaD1}
        {minL : MinimumLanguage L}
        {andpL : AndLanguage L}
        {andpD : AndDeduction L GammaD1}
        {adjD: ImpAndAdjointDeduction L GammaD1}
        {wandL : WandLanguage L}
        {wandD : WandDeduction L GammaD1}
        .

Lemma sepcon_andp_prop1_ : forall P Q R,
  P * (coq_prop Q && R) |-- (coq_prop Q) && (P * R).
Proof. 
  intros. 
  apply derivable1_andp_intros.
  + rewrite derivable1_sepcon_comm. 
    rewrite derivable1_wand_sepcon_adjoint.
    rewrite <- derivable1_impp_andp_adjoint.
    apply coq_prop_left. intros.
    rewrite derivable1_impp_andp_adjoint.
    rewrite <- derivable1_wand_sepcon_adjoint.
    apply coq_prop_right. apply H.
  + apply derivable1_sepcon_mono; [apply derivable1_refl|].
    apply derivable1_andp_elim2.
Qed.

Lemma sepcon_andp_prop2_ : forall P Q R,
  (coq_prop Q) && (P * R) |-- P * (coq_prop Q && R).
Proof. 
  intros.
  rewrite <- derivable1_impp_andp_adjoint.
  apply coq_prop_left. intros.
  rewrite derivable1_impp_andp_adjoint.
  rewrite derivable1_andp_elim2.
  apply derivable1_sepcon_mono; [apply derivable1_refl |].
  apply derivable1_andp_intros; [| apply derivable1_refl].
  apply coq_prop_right. apply H.
Qed.

Class sepcon_andp_prop : Type := {
  sepcon_andp_prop1 : forall P Q R,
    P * (coq_prop Q && R) |-- (coq_prop Q) && (P * R);
  sepcon_andp_prop2 : forall P Q R,
    (coq_prop Q) && (P * R) |-- P * (coq_prop Q && R)
}.

Lemma sepcon_andp_prop3_ {SAP : sepcon_andp_prop} : 
  forall P Q R,
    P * (Q && coq_prop R) |-- (coq_prop R) && (P * Q).
Proof. 
  intros. 
  rewrite derivable1_andp_comm.
  apply sepcon_andp_prop1.
Qed.

Lemma sepcon_andp_prop4_ {SAP : sepcon_andp_prop} :
  forall P Q R,
    (coq_prop R) && (P * Q) |-- P * (Q && coq_prop R).
Proof.
  intros.
  rewrite sepcon_andp_prop2.
  rewrite derivable1_andp_comm.
  apply derivable1_refl.
Qed.

Lemma sepcon_andp_prop5_ {SAP : sepcon_andp_prop} :
  forall P Q R,
    (coq_prop P && Q) * R |-- (coq_prop P) && (Q * R).
Proof. 
  intros.
  rewrite derivable1_sepcon_comm.
  rewrite sepcon_andp_prop1.
  rewrite derivable1_sepcon_comm.
  apply derivable1_refl.
Qed.

Lemma sepcon_andp_prop6_ {SAP : sepcon_andp_prop} :
  forall P Q R,
    (coq_prop P) && (Q * R) |-- (coq_prop P && Q) * R.
Proof. 
  intros.
  rewrite derivable1_sepcon_comm.
  rewrite sepcon_andp_prop2.
  rewrite derivable1_sepcon_comm.
  apply derivable1_refl.
Qed.

Lemma sepcon_andp_prop7_ {SAP : sepcon_andp_prop} : 
  forall P Q R,
    (P && (coq_prop Q)) * R |-- (coq_prop Q) && (P * R).
Proof. 
  intros.
  rewrite derivable1_sepcon_comm.
  rewrite derivable1_andp_comm.
  rewrite sepcon_andp_prop1.
  rewrite derivable1_sepcon_comm.
  apply derivable1_refl.
Qed.

Lemma sepcon_andp_prop8_ {SAP : sepcon_andp_prop} :
  forall P Q R,
  (coq_prop Q) && (P * R) |-- (P && (coq_prop Q)) * R.
Proof. 
  intros.
  rewrite derivable1_sepcon_comm.
  rewrite sepcon_andp_prop2.
  rewrite derivable1_andp_comm.
  rewrite derivable1_sepcon_comm.
  apply derivable1_refl.
Qed.

Class sepcon_andp_prop_ext : Type := {
  sepcon_andp_prop3 : forall P Q R,
    P * (Q && coq_prop R) |-- (coq_prop R) && (P * Q);
  sepcon_andp_prop4 : forall P Q R,
    (coq_prop R) && (P * Q) |-- P * (Q && coq_prop R);
  sepcon_andp_prop5 : forall P Q R,
    (coq_prop P && Q) * R |-- (coq_prop P) && (Q * R);
  sepcon_andp_prop6 : forall P Q R,
    (coq_prop P) && (Q * R) |-- (coq_prop P && Q) * R;
  sepcon_andp_prop7 : forall P Q R,
    (P && (coq_prop Q)) * R |-- (coq_prop Q) && (P * R);
  sepcon_andp_prop8 : forall P Q R,
    (coq_prop Q) && (P * R) |-- (P && (coq_prop Q)) * R;
}.

Lemma Derived_sepcon_andp_prop : sepcon_andp_prop.
Proof. 
  constructor.
  + apply sepcon_andp_prop1_.
  + apply sepcon_andp_prop2_.
Qed. 

Lemma Derived_sepcon_andp_prop_ext {SAP : sepcon_andp_prop} : sepcon_andp_prop_ext. 
Proof.
  constructor.
  + apply sepcon_andp_prop3_.
  + apply sepcon_andp_prop4_.
  + apply sepcon_andp_prop5_.
  + apply sepcon_andp_prop6_.
  + apply sepcon_andp_prop7_.
  + apply sepcon_andp_prop8_.
Qed.

Lemma iter_sepcon_andp_prop_ : forall xs1 P x2 xs3,
  iter_sepcon (xs1 ++ ((coq_prop P && x2) :: xs3)) |--
  (coq_prop P) && iter_sepcon (xs1 ++ (x2 ::xs3)).
Proof. 
  intros.
  rewrite itersepcon_app2.
  rewrite <- itersepcon_app1.
  rewrite itersepcon_cons1.
  assert (forall P Q R, (coq_prop P && Q) * R |-- (coq_prop P) && (Q * R)).
  { intros.
    rewrite derivable1_sepcon_comm.
    rewrite sepcon_andp_prop1_.
    rewrite derivable1_sepcon_comm.
    apply derivable1_refl. }
  rewrite H.
  rewrite sepcon_andp_prop1_.
  rewrite <- itersepcon_cons2.
  apply derivable1_refl.
Qed.

(* Lemma sepcon_andp_prop5_ {SAP : sepcon_andp_prop} :
  forall P Q R,
    (coq_prop P && Q) * R |-- (coq_prop P) && (Q * R).
Proof. 
  intros.
  rewrite derivable1_sepcon_comm.
  rewrite sepcon_andp_prop1.
  rewrite derivable1_sepcon_comm.
  apply derivable1_refl.
Qed. *)


Class Iter_sepcon_andp_prop : Type := {
  iter_sepcon_andp_prop : forall xs1 P x2 xs3,
  iter_sepcon (xs1 ++ ((coq_prop P && x2) :: xs3)) |--
  (coq_prop P) && iter_sepcon (xs1 ++ (x2 ::xs3))
}.

Lemma Derived_iter_sepcon_andp_prop :
  Iter_sepcon_andp_prop.
Proof.
  intros. 
  constructor.
  apply iter_sepcon_andp_prop_.
Qed.

End IterSepconDerivedRules.


(*
model derive wand
model derive exp, forallp
wand derive (flatten, exp_sepcon, exp_prop)
*)


(* iter_sepcon 三件事：
exists
prop
iter 拍平
*)


(*
Print exp Arguments explicit
*)





(* Lemma exists_and :
  forall (A B : nat -> expr),
  (Exists A) /\ (Exists B) -> Exists (fun n => And (A n) (B n)). *)


(* exp_right: forall {B: Type} (x:B) (P: A) (Q: B -> A),
derives P (Q x) -> derives P (exp Q);
exp_left: forall {B: Type} (P: B -> A) (Q: A),
(forall x, derives (P x) Q) -> derives (exp P) Q; *)


(*
Axiomatization of existsp
|- p [t \ x] -> ∃ x, p

Sequent Calculus of existsp
Phi |- p [t \ x] 
-------------------
Phi |- ∃ x, p




*)

