//@ Extern Coq (IntPair :: *)
/*@ Extern Coq Field (a : IntPair -> Z -> Z)
                     (b : IntPair -> Z -> Z)
*/

//@ Extern Coq Record Pair (A :: *) = Build_Pair { a1 : A -> Z ; b1 : A -> Z; }

//@ Extern Coq Record Pair0 = Build_Pair0 { a2 : Z ; b2 : Z; }

/*@ Extern Coq (IntPairSep : Z -> Z -> IntPair -> Assertion) */
/*@ Extern Coq (IntPairSep2 : Z -> IntPair -> Assertion) */
/*@ Extern Coq (IntPairSep3 : {A} -> Z -> Pair A -> A -> A -> Assertion) */
/*@ Extern Coq (IntPairSep4 : Z -> Pair0 -> Assertion)*/

/*@ Import Coq Require Import fieldtest_lib */

int z;

/*@ include strategies "fieldtest.strategies" */