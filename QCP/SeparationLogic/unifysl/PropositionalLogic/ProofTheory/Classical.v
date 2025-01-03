Require Import Logic.GeneralLogic.Base.
Require Import Logic.GeneralLogic.ProofTheory.BasicSequentCalculus.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.ProofTheory.ExtensionTactic.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfClassicalAxioms.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.

Class ClassicalAxiomatization (L: Language) {minL: MinimumLanguage L} (Gamma: Provable L) := {
  peirce_law: forall x y, |-- ((x --> y) --> x) --> x
}.

Class ClassicalSequentCalculus (L: Language) {negpL: NegLanguage L} (Gamma: Derivable L) := {
  (* derivable_excluded_middle: forall Phi x, Phi |--- x || ~~ x *)
  derivable_by_contradiction : forall Phi x y, (Phi ;;  ~~ x |--- y) -> (Phi ;; ~~ x |--- ~~ y) -> (Phi |--- x)
}. (* change this to by contraidiction, and derive this from by-contradiction *)

Class ClassicalDeduction (L:Language) {orpL: OrLanguage L} {negp:NegLanguage L} (GammaD1:Derivable1 L) := {
  deduction_excluded_middle: forall x y, x |-- y || ~~ y
}.

Class ClassicalPropositionalLogicEquiv (L:Language) {minL: MinimumLanguage L} {andpL: AndLanguage L} {negpL: NegLanguage L}  (GammaE:LogicEquiv L) := {
  equiv_excluded_middle:forall x, x --||-- ~~(~~x);
  equiv_DeMorgen:forall x y, ~~(x && y) --||-- (~~x) && (~~y)
}.

Section DerivableRulesFromAxiomatization0.

Context {L: Language}
        {minL: MinimumLanguage L}
        {orpL: OrLanguage L}
        {negpL: NegLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {cpAX: ClassicalAxiomatization L Gamma}.

Lemma by_contradiction: forall x y, |-- (~~ x --> y) --> (~~ x --> ~~ y) --> x.
Proof.
  pose proof Build_PeirceLaw _ _ _ peirce_law.
  pose proof Peirce2ByContradiction.
  apply __by_contradiction.
Qed.

Lemma double_negp_elim: forall x, |-- ~~ (~~ x) --> x.
Proof.
  pose proof Build_PeirceLaw _ _ _ peirce_law.
  pose proof Peirce2ByContradiction.
  pose proof ByContradiction2DoubleNegElimination.
  apply __double_negp_elim.
Qed.

Lemma classic_analysis: forall x y, |-- (x --> y) --> (~~ x --> y) --> y.
Proof.
  pose proof Build_PeirceLaw _ _ _ peirce_law.
  pose proof Peirce2ByContradiction.
  pose proof ByContradiction2DoubleNegElimination.
  pose proof DoubleNegElimination2ClassicAnalysis.
  apply __classic_analysis.
Qed.

Lemma excluded_middle: forall x, |-- x || ~~ x.
Proof.
  pose proof Build_PeirceLaw _ _ _ peirce_law.
  pose proof Peirce2ByContradiction.
  pose proof ByContradiction2DoubleNegElimination.
  pose proof DoubleNegElimination2ClassicAnalysis.
  pose proof ClassicAnalysis2ExcludedMiddle.
  apply __excluded_middle.
Qed.

Lemma impp2orp1: forall x y, |-- (x --> y) --> (~~ x || y).
Proof.
  pose proof Build_PeirceLaw _ _ _ peirce_law.
  pose proof Peirce2ByContradiction.
  pose proof ByContradiction2DoubleNegElimination.
  pose proof DoubleNegElimination2ClassicAnalysis.
  pose proof ClassicAnalysis2ImplyToOr.
  apply __impp2orp1.
Qed.

Lemma impp2orp {iffpL: IffLanguage L} {iffpAX: IffAxiomatization L Gamma}:
  forall x y, |-- (x --> y) <--> (~~ x || y).
Proof.
  intros.
  apply solve_iffp_intros.
  + apply impp2orp1.
  + apply impp2orp2.
Qed.

Lemma Peirce2cpAX {plAX: PeirceLaw L Gamma}: ClassicalAxiomatization L Gamma.
Proof.
  constructor.
  apply __peirce_law.
Qed.

End DerivableRulesFromAxiomatization0.

Section SequentCalculus2ExcludedMiddleSC.

Context {L : Language}
        (* {minL : MinimumLanguage L} *)
        {negpL : NegLanguage L}
        {orpL : OrLanguage L}
        {Gamma : Derivable L}
        {cpSC : ClassicalSequentCalculus L Gamma}
        {bSC: BasicSequentCalculus L Gamma}
        (* {minSC: MinimumSequentCalculus L Gamma} *)
        {inegpSC: IntuitionisticNegSequentCalculus L Gamma}
        {orpSC: OrSequentCalculus L Gamma}
        .

(* Print IntuitionisticNegSequentCalculus. *)

Lemma derivable_excluded_middle: forall Phi x, Phi |--- x || ~~ x.
Proof.
  intros. 
  apply (derivable_by_contradiction Phi (x || ~~ x) x).
  + apply (derivable_by_contradiction (Phi;; ~~(x || ~~ x)) x (~~ x)).
    - apply derivable_assum.
      apply Union_intror. apply In_singleton.
    - apply (deduction_weaken (Phi;; ~~(x || ~~ x))).
      { unfold Included. intros. inversion H; subst.
        + apply Union_introl. apply Union_introl. apply H0.
        + apply Union_introl. apply Union_intror. apply H0. }
      apply deduction_contrapositivePP.
      apply deduction_orp_intros2.
      apply derivable_assum. apply Union_intror. apply In_singleton.
  + apply deduction_contrapositivePP.
    apply deduction_orp_intros1.
    apply derivable_assum. apply Union_intror. apply In_singleton.
Qed. 

End SequentCalculus2ExcludedMiddleSC.

Section Axiomatization2SequentCalculus.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}
        {cpAX: ClassicalAxiomatization L GammaP}
        {GammaPD: ProvableDerivable L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {andpSC: AndSequentCalculus L GammaD}
        {orpSC: OrSequentCalculus L GammaD}
        {falsepSC: FalseSequentCalculus L GammaD}
        {inegpSC: IntuitionisticNegSequentCalculus L GammaD}
        {iffpSC: IffSequentCalculus L GammaD}
        {truepSC: TrueSequentCalculus L GammaD}.

Lemma Axiomatization2SequentCalculus_cpSC:
  ClassicalSequentCalculus L GammaD.
Proof.
  constructor.
  intros.
  pose proof (by_contradiction x y).
  rewrite deduction_theorem in H.
  rewrite deduction_theorem in H0.
  rewrite provable_derivable in H1.
  rewrite <-deduction_theorem in H1.
  rewrite <-deduction_theorem in H1.
  apply (deduction_subst Phi (empty_context;; ~~ x --> y;; ~~ x --> ~~ y)).
  + intros. inversion H2; subst.
    - inversion H3; subst.
      * unfold empty_context in *. inversion H4.
      * inversion H4; subst. apply H.
    - inversion H3; subst. apply H0. 
  + eapply deduction_weaken; [| apply H1].
    unfold Included. intros. apply Union_intror. apply H2.
Qed.

End Axiomatization2SequentCalculus.

#[export] Instance reg_Axiomatization2SequentCalculus_cpSC:
  RegisterClass P2D_reg (fun cpSC: unit => @Axiomatization2SequentCalculus_cpSC) 10.
Qed.

Section SequentCalculus2Axiomatization.

Context {L: Language}
        {minL: MinimumLanguage L}
        {andpL: AndLanguage L}
        {orpL: OrLanguage L}
        {falsepL: FalseLanguage L}
        {negpL: NegLanguage L}
        {iffpL: IffLanguage L}
        {truepL: TrueLanguage L}
        {GammaP: Provable L}
        {GammaD: Derivable L}
        {GammaPD: ProvableDerivable L GammaP GammaD}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {andpSC: AndSequentCalculus L GammaD}
        {orpSC: OrSequentCalculus L GammaD}
        {falsepSC: FalseSequentCalculus L GammaD}
        {inegpSC: IntuitionisticNegSequentCalculus L GammaD}
        {iffpSC: IffSequentCalculus L GammaD}
        {truepSC: TrueSequentCalculus L GammaD}
        {cpSC: ClassicalSequentCalculus L GammaD}
        {minAX: MinimumAxiomatization L GammaP}
        {andpAX: AndAxiomatization L GammaP}
        {orpAX: OrAxiomatization L GammaP}
        {falsepAX: FalseAxiomatization L GammaP}
        {inegpAX: IntuitionisticNegAxiomatization L GammaP}
        {iffpAX: IffAxiomatization L GammaP}
        {truepAX: TrueAxiomatization L GammaP}.

Lemma SequentCalculus2Axiomatization_cpAX: ClassicalAxiomatization L GammaP.
Proof.
  intros.
  constructor.
  assert (forall x y, |-- (~~ x --> y) --> (~~ x --> ~~ y) --> x). {
    intros.
    rewrite provable_derivable.
    rewrite <-deduction_theorem.
    rewrite <-deduction_theorem.
    apply (derivable_by_contradiction _ _ y).
    + rewrite deduction_theorem.
      apply derivable_assum.
      apply Union_introl. apply Union_intror.
      apply In_singleton.
    + rewrite deduction_theorem.
      apply derivable_assum.
      apply Union_intror. apply In_singleton.
  }
  pose proof (@ByContradiction2DoubleNegElimination L minL negpL GammaP minAX (@Build_ByContradiction L minL negpL GammaP H)).
  pose proof (DoubleNegElimination2ClassicAnalysis).
  pose proof (ClassicAnalysis2PeirceLaw).
  apply __peirce_law.
Qed.

End SequentCalculus2Axiomatization.

#[export] Instance reg_SequentCalculus2Axiomatization_cpAX:
  RegisterClass D2P_reg (fun cpAX: unit => @SequentCalculus2Axiomatization_cpAX) 8.
Qed.

Section DerivableRulesFromAxiomatization1.

Context {L: Language}
        {minL: MinimumLanguage L}
        {orpL: OrLanguage L}
        {negpL: NegLanguage L}
        {Gamma: Provable L}
        {minAX: MinimumAxiomatization L Gamma}
        {orpAX: OrAxiomatization L Gamma}
        {inegpAX: IntuitionisticNegAxiomatization L Gamma}
        {cpAX: ClassicalAxiomatization L Gamma}.

Lemma double_negp {iffpL: IffLanguage L} {iffpAX: IffAxiomatization L Gamma}:
  forall (x: expr), |-- ~~ (~~ x) <--> x.
Proof.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  apply deduction_iffp_intros; rewrite deduction_theorem; rewrite <- provable_derivable.
  + apply double_negp_elim.
  + apply double_negp_intros.
Qed.

#[export] Instance Classical2GodelDummett: GodelDummettAxiomatization L Gamma.
Proof.
  constructor.
  clear - orpAX inegpAX cpAX minAX.
  AddSequentCalculus.
  intros.
  rewrite provable_derivable.
  set (Phi := empty_context).
  clearbody Phi.
  pose proof excluded_middle x.
  apply deduction_weaken0 with (Phi := Phi) in H.
  eapply deduction_modus_ponens; [exact H |].
  apply deduction_orp_elim'.
  + rewrite <- deduction_theorem.
    apply deduction_orp_intros2.
    rewrite deduction_theorem.
    apply derivable_axiom1.
  + rewrite <- deduction_theorem.
    apply deduction_orp_intros1.
    rewrite deduction_theorem.
    apply deduction_impp_arg_switch.
    apply derivable_contradiction_elim2.
Qed.

Lemma contrapositiveNN: forall (x y: expr),
  |-- (~~ y --> ~~ x) --> (x --> y).
Proof.
  AddSequentCalculus.
  intros.
  rewrite <- (double_negp_elim y) at 2.
  rewrite provable_derivable.
  rewrite <- deduction_theorem.
  apply deduction_contrapositivePN'.
  solve_assum.
Qed.

Lemma contrapositiveNP: forall (x y: expr),
  |-- (~~ y --> x) --> (~~ x --> y).
Proof.
  AddSequentCalculus.
  intros.
  rewrite <- (contrapositiveNN (~~ x) y).
  rewrite <- (double_negp_intros x).
  apply provable_impp_refl.
Qed.

Lemma solve_classic: forall x y: expr,
  |-- x --> y ->
  |-- ~~ x --> y ->
  |-- y.
Proof.
  intros.
  eapply modus_ponens; [| apply (excluded_middle x)].
  apply solve_orp_impp; auto.
Qed.

Lemma provable_impp_negp: forall x,
  |-- (x --> ~~ x) --> ~~x.
Proof.
  intros.
  pose proof aux_minimun_theorem02 (~~ x --> ~~ x) (~~ x).
  pose proof modus_ponens _ _ H (provable_impp_refl (~~ x)).
  rewrite <- H0 at 2; clear H H0.
  apply classic_analysis.
Qed.

End DerivableRulesFromAxiomatization1.

Section DerivableRulesFromSequentCalculus.

Context {L: Language}
        {minL: MinimumLanguage L}
        {orpL: OrLanguage L}
        {negpL: NegLanguage L}
        {Gamma: Derivable L}
        {bSC: BasicSequentCalculus L Gamma}
        {minSC: MinimumSequentCalculus L Gamma}
        {orpSC: OrSequentCalculus L Gamma}
        {inegpSC: IntuitionisticNegSequentCalculus L Gamma}
        {cpSC: ClassicalSequentCalculus L Gamma}.

Lemma deduction_contrapositiveNN: forall Phi (x y: expr),
  Phi |--- ~~ y --> ~~ x ->
  Phi |--- x --> y.
Proof.
  AddAxiomatization.
  intros.
  rewrite <- contrapositiveNN.
  auto.
Qed.

Lemma deduction_contrapositiveNP: forall Phi (x y: expr),
  Phi |--- ~~ y --> x ->
  Phi |--- ~~ x --> y.
Proof.
  AddAxiomatization.
  intros.
  rewrite <- contrapositiveNP.
  auto.
Qed.

Lemma deduction_negp_right: forall Phi x,
  Phi;; x |--- ~~ x ->
  Phi |--- ~~ x.
Proof.
  AddAxiomatization.
  intros.
  rewrite <- provable_impp_negp.
  rewrite deduction_theorem in H.
  auto.
Qed.

End DerivableRulesFromSequentCalculus.

Section ClassicalNeg2IntuitionisticNeg.

Context {L : Language}
        {negpL : NegLanguage L}
        {GammaD : Derivable L}
        {bSC : BasicSequentCalculus L GammaD}
        {cSC : ClassicalSequentCalculus L GammaD}
        .

Lemma rev_double_neg : forall (Phi : Ensemble expr) (x : expr),
  Phi;; (~~ (~~ x)) |--- x.
Proof. 
  intros.
  apply (derivable_by_contradiction _ _ (~~ x)).
  + apply derivable_assum. apply Union_intror. apply In_singleton.
  + apply derivable_assum. apply Union_introl. apply Union_intror.
    apply In_singleton.
Qed.

Lemma classical_to_contrapositivepp : forall (Phi : Ensemble expr) (x y : expr), Phi;; y |--- x -> Phi;; ~~ x |--- ~~ y.
Proof. 
  intros.
  apply (derivable_by_contradiction _ _ x).
  + apply (deduction_subst _ (Phi;; y) _).
    - intros. inversion H0; subst.
      * apply derivable_assum. repeat apply Union_introl. apply H1.
      * inversion H1; subst. pose proof (rev_double_neg Phi x0).
        eapply deduction_weaken; [| apply H2].
        unfold Included. intros. inversion H3; subst.
        { repeat apply Union_introl. apply H4. }
        inversion H4; subst. apply Union_intror. apply In_singleton.
    - eapply deduction_weaken; [| apply H].
      unfold Included. intros. apply Union_intror. apply H0.
  + apply derivable_assum. apply Union_introl. apply Union_intror. 
    apply In_singleton.
Qed.

Lemma classical_to_contradiction_elim : forall (Phi : context) (x y : expr), Phi |--- x -> Phi |--- ~~ x -> Phi |--- y.
Proof. 
  intros.
  apply (derivable_by_contradiction _ _ x).
  + eapply deduction_weaken; [| apply H].
    unfold Included; intros. apply Union_introl. apply H1.
  + eapply deduction_weaken; [| apply H0].
    unfold Included; intros. apply Union_introl. apply H1.
Qed.

Lemma classical_to_double_negp_intros : forall (Phi : context) (x : expr), Phi |--- x -> Phi |--- ~~ (~~ x).
Proof. 
  intros.
  apply (derivable_by_contradiction _ _ (x)).
  + eapply deduction_weaken; [| apply H].
    unfold Included; intros. apply Union_introl. apply H0.
  + apply rev_double_neg.
Qed. 

Lemma Classical2Intuitionistic_cSC :
  IntuitionisticNegSequentCalculus L GammaD.
Proof.
  constructor.
  + apply classical_to_contrapositivepp.
  + apply classical_to_contradiction_elim.
  + apply classical_to_double_negp_intros.
Qed.

End ClassicalNeg2IntuitionisticNeg.

Section DerivedSequentCalculusRules.

Context {L : Language}
        {minL : MinimumLanguage L}
        {negpL : NegLanguage L}
        {andpL : AndLanguage L}
        {orpL : OrLanguage L}
        {falsepL : FalseLanguage L}
        {trueL : TrueLanguage L}
        {GammaD : Derivable L}
        {bSC: BasicSequentCalculus L GammaD}
        {minSC: MinimumSequentCalculus L GammaD}
        {andpSC: AndSequentCalculus L GammaD}
        {orpSC: OrSequentCalculus L GammaD}
        {falsepSC: FalseSequentCalculus L GammaD}
        {inegpSC: IntuitionisticNegSequentCalculus L GammaD}
        {truepSC: TrueSequentCalculus L GammaD}
        {cSC : ClassicalSequentCalculus L GammaD}
        .

Lemma deduction_and_neg1_ : forall Phi P Q,
  Phi |--- ~~ P -> Phi |--- ~~ (P && Q).
Proof. 
  intros.
  apply (derivable_by_contradiction _ _ P).
  + apply (deduction_subst _ (Phi ;; P && Q) _).
    - intros. inversion H0; subst.
      * apply derivable_assum. apply Union_introl. apply H1.
      * inversion H1; subst. apply rev_double_neg.
    - apply (deduction_weaken (Phi;; P && Q) _ _).
      * unfold Included. intros. apply Union_intror. apply H0. 
      * apply (deduction_andp_elim1 _ _ Q).
        apply derivable_assum. apply Union_intror. apply In_singleton.
  + apply (deduction_subst _ Phi).
    - intros. apply derivable_assum. apply Union_introl. apply H0.
    - apply (deduction_weaken Phi _ _).
      * unfold Included. intros. apply Union_intror. apply H0.
      * apply H. 
Qed.
      
(* Lemma deduction_and_neg1_ : forall Phi P Q,
  Phi ;; (~~ P) |--- ~~ (P && Q).
Proof.
  intros. 
  apply deduction_contrapositivePP.
  apply (deduction_andp_elim1 _ _ Q).
  apply (derivable_assum). apply Union_intror. apply In_singleton.
Qed. *)

Lemma deduction_and_neg2_ : forall Phi P Q,
  Phi |--- ~~ Q -> Phi |--- ~~ (P && Q).
Proof. 
  intros.
  apply (derivable_by_contradiction _ _ Q).
  + apply (deduction_subst _ (Phi ;; P && Q) _).
    - intros. inversion H0; subst.
      * apply derivable_assum. apply Union_introl. apply H1.
      * inversion H1; subst. apply rev_double_neg.
    - apply (deduction_weaken (Phi;; P && Q) _ _).
      * unfold Included. intros. apply Union_intror. apply H0. 
      * apply (deduction_andp_elim2 _ P Q).
        apply derivable_assum. apply Union_intror. apply In_singleton.
  + apply (deduction_subst _ Phi).
    - intros. apply derivable_assum. apply Union_introl. apply H0.
    - apply (deduction_weaken Phi _ _).
      * unfold Included. intros. apply Union_intror. apply H0.
      * apply H. 
Qed.

(* Lemma deduction_and_neg2_ : forall Phi P Q,
  Phi ;; (~~ Q) |--- ~~ (P && Q).
Proof. 
  intros.
  apply deduction_contrapositivePP.
  apply (deduction_andp_elim2 _ P _).
  apply (derivable_assum). apply Union_intror. apply In_singleton.
Qed. *)

Lemma deduction_or_neg__ : forall Phi P Q,
  Phi ;; (~~ P) ;; (~~ Q) |--- ~~ (P || Q).
Proof.
  intros.
  apply deduction_contrapositivePP.
  apply deduction_orp_elim.
  + apply (deduction_contradiction_elim _ P); apply derivable_assum.
    - apply Union_intror. apply In_singleton.
    - apply Union_introl. apply Union_intror. apply In_singleton.  
  + apply derivable_assum. apply Union_intror. apply In_singleton.
Qed.

Lemma deduction_or_neg_ : forall Phi P Q,
  Phi |--- ~~ P -> Phi |--- ~~ Q -> Phi |--- ~~ (P || Q).
Proof. 
  intros.
  apply (deduction_subst _ (Phi ;; (~~ P) ;; (~~ Q))).
  + intros. inversion H1; subst; [inversion H2; subst |].
    - apply derivable_assum. apply H3.
    - inversion H3; subst. apply H.
    - inversion H2; subst. apply H0.
  + apply (deduction_weaken (Phi;; ~~ P;; ~~ Q)).
    - unfold Included. intros. apply Union_intror. apply H1.
    - apply deduction_or_neg__.
Qed.

Lemma deduction_imp_neg1_ : forall Phi P Q,
  Phi |--- (~~ P) -> Phi |--- P --> Q.
Proof.
  intros.
  apply deduction_impp_intros.
  apply (deduction_contradiction_elim _ P).
  + apply derivable_assum. apply Union_intror. apply In_singleton.
  + eapply deduction_weaken; [| apply H].
    unfold Included. intros. apply Union_introl. apply H0.
Qed.

(* Lemma deduction_imp_neg1_ : forall Phi P Q,
  Phi ;; (~~ P) |--- P --> Q.
Proof. 
  intros.
  rewrite <- deduction_theorem.
  apply (deduction_contradiction_elim _ P); apply derivable_assum.
  + apply Union_intror. apply In_singleton.
  + apply Union_introl. apply Union_intror. apply In_singleton.
Qed. *)

Lemma deduction_imp_neg2__ : forall Phi P Q,
  Phi ;; P ;; (~~ Q) |--- ~~ (P --> Q).
Proof.
  intros.
  apply deduction_contrapositivePP.
  apply (deduction_modus_ponens _ P); apply derivable_assum.
  + apply Union_introl. apply Union_intror. apply In_singleton.
  + apply Union_intror. apply In_singleton.
Qed.

Lemma deduction_imp_neg2_ : forall Phi P Q,
  Phi |--- P -> Phi |--- ~~ Q -> Phi |--- ~~ (P --> Q).
Proof. 
  intros.
  apply (deduction_subst _ (Phi;; P;; (~~ Q))).
  + intros. inversion H1; subst; [inversion H2; subst |].
    - apply derivable_assum. apply H3.
    - inversion H3; subst. apply H. 
    - inversion H2; subst. apply H0.
  + apply (deduction_weaken (Phi;; P;; ~~Q)).
    - unfold Included; intros. apply Union_intror. apply H1.
    - apply deduction_imp_neg2__.
Qed.

Lemma deduction_false_neg_ : forall Phi,
  Phi |--- ~~ FF.
Proof. 
  intros.
  apply (derivable_by_contradiction _ _ FF).
  + apply rev_double_neg.
  + apply deduction_contrapositivePP.
    apply deduction_falsep_elim.
    apply derivable_assum. apply Union_intror. apply In_singleton.
Qed.

Class deduction_derived_neg (L : Language) (GammaD : Derivable L) : Type := {
  deduction_and_neg1 : forall Phi P Q, Phi |--- ~~ P -> Phi |--- ~~ (P && Q);
  deduction_and_neg2 : forall Phi P Q, Phi |--- ~~ Q -> Phi |--- ~~ (P && Q);
  deduction_or_neg : forall Phi P Q, Phi |--- ~~ P -> Phi |--- ~~ Q -> Phi |--- ~~ (P || Q);
  deduction_imp_neg1 : forall Phi P Q, Phi |--- (~~ P) -> Phi |--- P --> Q;
  deduction_imp_neg2 : forall Phi P Q, Phi |--- P -> Phi |--- ~~ Q -> Phi |--- ~~ (P --> Q);
  deduction_false_neg : forall Phi, Phi |--- ~~ FF;  
}.

Lemma SequentCalculus2DeductionDerivedNeg : deduction_derived_neg L GammaD.
Proof.
  constructor.
  + apply deduction_and_neg1_.
  + apply deduction_and_neg2_.
  + apply deduction_or_neg_.
  + apply deduction_imp_neg1_.
  + apply deduction_imp_neg2_.
  + apply deduction_false_neg_.
Qed.

End DerivedSequentCalculusRules.