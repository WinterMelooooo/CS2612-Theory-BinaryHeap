/*@ Extern Coq (program :: * => * => *) */
/*@ Extern Coq (unit :: *) */
/*@ Extern Coq (safeExec : {Sigma} {A} -> (Sigma -> Prop) -> program Sigma A -> (A -> Sigma -> Prop) -> Prop)
               (bind: {Sigma} {A} {B} ->  program Sigma A -> (A -> program Sigma B) -> program Sigma B)
               (return : {Sigma} {A} -> A -> program Sigma A) 
               (tt: unit)
               (LastSeen: list Z -> (list Z -> Prop) -> Prop)
               (ATrue: {A} -> A -> Prop)
                */

/*@ Import Coq From StateMonad.monadnrm Require Export monadbasic safeexec_lib mergeExample */
/*@ Import Coq Export MonadNotation */
/*@ Import Coq Require Import fine_grained_sll_lib */
/*@ Import Coq Import sll_C_Rules */
/*@ Import Coq Local Open Scope stmonad */

/*@ include strategies "safeexec.strategies" */