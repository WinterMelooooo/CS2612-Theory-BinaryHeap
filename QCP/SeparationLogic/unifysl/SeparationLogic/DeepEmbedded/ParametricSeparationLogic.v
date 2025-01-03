Require Import Logic.GeneralLogic.Base.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.MinimumLogic.ProofTheory.RewriteClass.
Require Import Logic.MinimumLogic.Syntax.
Require Import Logic.MinimumLogic.ProofTheory.Minimum.
Require Import Logic.PropositionalLogic.Syntax.
Require Import Logic.PropositionalLogic.ProofTheory.Intuitionistic.
Require Import Logic.PropositionalLogic.ProofTheory.DeMorgan.
Require Import Logic.PropositionalLogic.ProofTheory.GodelDummett.
Require Import Logic.PropositionalLogic.ProofTheory.Classical.
Require Import Logic.PropositionalLogic.ProofTheory.TheoryOfPropositionalConnectives.
Require Import Logic.PropositionalLogic.ProofTheory.RewriteClass.
Require Import Logic.SeparationLogic.Syntax.
Require Import Logic.SeparationLogic.ProofTheory.SeparationLogic.
Require Import Logic.SeparationLogic.ProofTheory.TheoryOfSeparationAxioms.
Require Import Logic.SeparationLogic.DeepEmbedded.Parameter.
Require Logic.SeparationLogic.DeepEmbedded.SeparationEmpLanguage.
Require Import Morphisms.

Local Open Scope logic_base.
Local Open Scope syntax.
Import PropositionalLanguageNotation.
Import SeparationLogicNotation.

Class Parametric_SeparationLogic
      (PAR: SL_Parameter)
      (L: Language)
      {minL: MinimumLanguage L}
      {andpL: AndLanguage L}
      {orpL: OrLanguage L}
      {iffpL: IffLanguage L}
      {negpL: NegLanguage L}
      {falsepL: FalseLanguage L}
      {truepL: TrueLanguage L}
      {sepconL: SepconLanguage L}
      {wandL: WandLanguage L}
      {empL: EmpLanguage L}
      (GammaP: Provable L) := {
  Parametric_DM: WEM = true -> DeMorganAxiomatization L GammaP;
  Parametric_GD: IC = true -> GodelDummettAxiomatization L GammaP;
  Parametric_C: EM = true -> ClassicalAxiomatization L GammaP;
  Parametric_GC: SCE = true -> GarbageCollectSeparationLogic L GammaP;
  Parametric_NE: ESE = true -> NonsplitEmpSeparationLogic L GammaP;
  Parametric_ED: ED = true -> DupEmpSeparationLogic L GammaP
}.

Section SeparationLogic.

Context {Sigma: SeparationEmpLanguage.PropositionalVariables}.

Existing Instances SeparationEmpLanguage.L
                   SeparationEmpLanguage.minL
                   SeparationEmpLanguage.andpL
                   SeparationEmpLanguage.orpL
                   SeparationEmpLanguage.falsepL
                   SeparationEmpLanguage.truepL
                   SeparationEmpLanguage.iffpL
                   SeparationEmpLanguage.negpL
                   SeparationEmpLanguage.sepconL
                   SeparationEmpLanguage.wandL
                   SeparationEmpLanguage.empL
                   SeparationEmpLanguage.iffpDef
                   SeparationEmpLanguage.truepDef
                   SeparationEmpLanguage.negpDef.

Context (PAR: SL_Parameter).

Inductive provable: expr -> Prop :=
| modus_ponens: forall x y, provable (x --> y) -> provable x -> provable y
| axiom1: forall x y, provable (x --> (y --> x))
| axiom2: forall x y z, provable ((x --> y --> z) --> (x --> y) --> (x --> z))
| andp_intros: forall x y, provable (x --> y --> x && y)
| andp_elim1: forall x y, provable (x && y --> x)
| andp_elim2: forall x y, provable (x && y --> y)
| orp_intros1: forall x y, provable (x --> x || y)
| orp_intros2: forall x y, provable (y --> x || y)
| orp_elim: forall x y z, provable ((x --> z) --> (y --> z) --> (x || y --> z))
| falsep_elim: forall x, provable (FF --> x)
| weak_excluded_middle: WEM = true -> forall x, provable (~~ x || ~~ ~~ x)
| impp_choice: IC = true -> forall x y, provable ((x --> y) || (y --> x))
| pierce_law: EM = true -> forall x y, provable (((x --> y) --> x) --> x)
| sepcon_comm_impp: forall x y, provable (x * y --> y * x)
| sepcon_assoc1: forall x y z, provable (x * (y * z) --> (x * y) * z)
| wand_sepcon_adjoint1: forall x y z, provable (x * y --> z) -> provable (x --> (y -* z))
| wand_sepcon_adjoint2: forall x y z, provable (x --> (y -* z)) -> provable (x * y --> z)
| sepcon_emp: forall x, provable (x * emp <--> x)
| sepcon_elim1: SCE = true -> forall x y, provable (x * y --> x)
| emp_sepcon_truep_elim: ESE = true -> forall x, provable (x * TT && emp --> x)
| emp_dup: ED = true -> forall x, provable (x && emp --> x * x).

#[export] Instance GP: Provable SeparationEmpLanguage.L := Build_Provable _ provable.

#[export] Instance GD: Derivable SeparationEmpLanguage.L := Provable2Derivable.

#[export] Instance GDP: DerivableProvable SeparationEmpLanguage.L GP GD :=
  Provable2Derivable_Normal.

#[export] Instance minAX: MinimumAxiomatization SeparationEmpLanguage.L GP.
Proof.
  constructor.
  + apply modus_ponens.
  + apply axiom1.
  + apply axiom2.
Qed.

#[export] Instance andpAX: AndAxiomatization SeparationEmpLanguage.L GP.
Proof.
  constructor.
  + apply andp_intros.
  + apply andp_elim1.
  + apply andp_elim2.
Qed.


#[export] Instance orpAX: OrAxiomatization SeparationEmpLanguage.L GP.
Proof.
  constructor.
  + apply orp_intros1.
  + apply orp_intros2.
  + apply orp_elim.
Qed.

#[export] Instance falsepAX: FalseAxiomatization SeparationEmpLanguage.L GP.
Proof.
  constructor.
  apply falsep_elim.
Qed.

#[export] Instance iffpAX: IffAxiomatization SeparationEmpLanguage.L GP
:= IffFromDefToAX_And_Imp.

#[export] Instance truepAX: TrueAxiomatization SeparationEmpLanguage.L GP :=
  TrueFromDefToAX_False_Imp.

#[export] Instance inegpAX: IntuitionisticNegAxiomatization SeparationEmpLanguage.L GP :=
  NegFromDefToAX_False_Imp.

#[export] Instance wandAX: WandAxiomatization SeparationEmpLanguage.L GP.
Proof.
  constructor.
  intros; split.
  + apply wand_sepcon_adjoint1.
  + apply wand_sepcon_adjoint2.
Qed.

#[export] Instance sepconAX: SepconAxiomatization SeparationEmpLanguage.L GP.
Proof.
  assert (SepconAxiomatization_weak SeparationEmpLanguage.L GP).
  {
    constructor.
    + apply sepcon_comm_impp.
    + apply sepcon_assoc1.
  }
  eapply @SepconAxiomatizationWeak2SepconAxiomatization;
  try typeclasses eauto.
  eapply @Adj2SepconMono;
  try typeclasses eauto.
Qed.

#[export] Instance empAX: EmpAxiomatization SeparationEmpLanguage.L GP.
Proof.
  eapply @EmpAxiomatizationIff2EmpAxiomatization;
  try typeclasses eauto.
  constructor.
  apply sepcon_emp.
Qed.

#[export] Instance sepcon_orp_AX: SepconOrAxiomatization SeparationEmpLanguage.L GP.
Proof.
  eapply @Adj2SepconOr;
  try typeclasses eauto.
Qed.

#[export] Instance sepcon_falsep_AX: SepconFalseAxiomatization SeparationEmpLanguage.L GP.
Proof.
  eapply @Adj2SepconFalse;
  try typeclasses eauto.
Qed.

#[export] Instance ParAX: Parametric_SeparationLogic PAR SeparationEmpLanguage.L GP.
Proof.
  constructor.
  + intros; constructor.
    apply weak_excluded_middle; auto.
  + intros; constructor.
    apply impp_choice; auto.
  + intros; constructor.
    apply pierce_law; auto.
  + intros; constructor.
    apply sepcon_elim1; auto.
  + intros; constructor.
    apply emp_sepcon_truep_elim; auto.
  + intros; constructor.
    apply emp_dup; auto.
Qed.

End SeparationLogic.
