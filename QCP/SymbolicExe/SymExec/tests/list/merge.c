struct list {
  void *head;
  struct list *next;
};

//@ Export Coq Goal "merge_goal.v"
//@ Export Coq Proof "merge_proof.v"

/*@ Extern Coq (nil : {A} -> list A)
               (cons : {A} -> A -> list A -> list A)
               (app : {A} -> list A -> list A -> list A)
               (sll : {A} -> (Z -> A -> Assertion) -> Z -> list A -> Assertion) 
 */

//@ Extern Coq (ordered : {A} -> (A -> A -> Prop) -> list A -> Prop) 

struct list *merge(struct list *x, struct list *y, int (*cmp)(void *x, void *y))
/*@ With {A} storeA (le : A -> A -> Prop)
    Require exists l1 l2,
            ordered(le, l1) && ordered(le, l2) &&
            (cmp |= int (void *x, void *y)
                  With a b
                  Require storeA(x, a) * storeA(y, b)
                  Ensure __return <= 0 && le(a, b) * storeA(x, a) * storeA(y, b)  || __return > 0 && le(b, a) * storeA(x, a) * storeA(y, b)) &&
            sll(storeA, x, l1) * sll(storeA, y, l2)
    Ensure exists l, ordered(le, l) && sll(storeA, __return, l)
 */
{
   if (x == (void *)0) {
      return y;
   }
   else if (y == (void *)0) {
      return x;
   }
   else {
      /*@
         exists a b l1 l2,
         storeA(x->head, a) && storeA(y->head, b) && 
         sll(storeA, x->next, l1) && sll(storeA, y->next, l2) && 
         ordered(le, cons(a, l1)) && ordered(le, cons(b, l2)) &&
         cmp |= int (void *x, void *y)
                  With a b
                  Require storeA(x, a) * storeA(y, b)
                  Ensure __return <= 0 && le(a, b) && storeA(x, a) * storeA(y, b)  || __return > 0 && le(b, a) && storeA(x, a) * storeA(y, b)
      */
      if (cmp(x->head, y->head) <= 0) {
         x->next = merge(x->next, y, cmp) /*@ where storeA = storeA, le = le; A = A */;
         return x;
      } else {
         y->next = merge(x, y->next, cmp) /*@ where storeA = storeA, le = le; A = A */;
         return y;
      }
   }
}