/*@ Extern Coq 
               (InsideCritical: (Z * Z * Z) -> (list Z * list Z * list Z) -> Assertion)
               (OutsideCritical: (Z * Z * Z) -> (list Z * list Z * list Z) -> Assertion)
               (RTrans_C: (Z * Z * Z) -> (list Z * list Z * list Z) -> (Z * Z * Z) -> (list Z * list Z * list Z) -> Prop)
               (GTrans_C: (Z * Z * Z) -> (list Z * list Z * list Z) -> (Z * Z * Z) -> (list Z * list Z * list Z) -> Prop)
               (RTrans_Abs : (list Z * list Z * list Z) -> (list Z * list Z * list Z) -> Prop)
               (GTrans_Abs : (list Z * list Z * list Z) -> (list Z * list Z * list Z) -> Prop)
               (os_inv: (Z * Z * Z) -> (list Z * list Z * list Z) -> Assertion) */

/*@ Extern Coq (fst : {A} {B} -> A * B -> A)
               (snd : {A} {B} -> A * B -> B) 
               (prod3 : {A} {B} {C} -> A -> B -> C -> A * B * C)
               */

/*@ include strategies "triple_critical.strategies" */

/*@ Import Coq Require Import triple_critical_sll_lib */
