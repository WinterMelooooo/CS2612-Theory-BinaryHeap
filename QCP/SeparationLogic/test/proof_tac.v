From SimpleC.ASRT Require Import DefFiles.
From compcert.lib Require Import Coqlib.
From SimpleC.CSE Require Import Cexpr_def Cexpr_StateMachine.
From SimpleC.CSE Require Import Cstate_def Ceval_sound.

Parameter SAC_Asrt_Denote : list assertion -> list assertion -> Prop. 

Axiom Magic_Theorem : forall Asrt Asrt' P, SAC_Asrt_Denote Asrt Asrt' = P. 

Axiom VSTA_Proof_Trans_correctness :
  forall Pre Post env Funcpred_denote Seppred_denote,
    SAC_Asrt_Denote Pre Post ->  
    @Sound_single_entailment_checker env Funcpred_denote Seppred_denote Pre Post. 

Ltac proof_by_vst_a H := 
  apply VSTA_Proof_Trans_correctness ; 
  let p := type of H in
  rewrite (Magic_Theorem _ _ p) ;  
  apply H.