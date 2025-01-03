struct list {
   int data;
   struct list *next;
};

/*@ Extern Coq (sll : Z -> list Z -> Assertion)
 */

/*@ Import Coq Require Import fine_grained_sll_lib */
/*@ Import Coq Import sll_C_Rules */

/*@ include strategies "sll.strategies" */