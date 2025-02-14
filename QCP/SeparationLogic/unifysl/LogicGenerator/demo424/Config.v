Require Import Coq.Lists.List.
Require Import Logic.LogicGenerator.Utils.
Require Import Logic.LogicGenerator.ConfigLang.

Import ListNotations.

Definition how_connectives :=
  [ primitive_connective impp 
  ; primitive_connective andp
  ; primitive_connective orp
  ; primitive_connective exp 
  ; primitive_connective coq_prop
  ; primitive_connective truep
  ; FROM_impp_TO_multi_imp
  ].

Definition how_judgements :=
  [ primitive_judgement derivable1 ].

Definition transparent_names :=
  [expr : parameter].

Definition primitive_rule_classes :=
  [ derivitive1_OF_andp
  ; derivitive1_OF_impp_andp_adjoint
  ; derivitive1_OF_orp
  ; derivitive1_OF_exp
  ; derivitive1_OF_basic_setting
  ; derivitive1_OF_coq_prop
  ].