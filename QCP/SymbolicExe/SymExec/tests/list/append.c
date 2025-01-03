struct list {
   void* head;
   struct list *next;
};

//@ Import Coq From SimpleC.PT Require Import slldef

/*@ Extern Coq (nil : {A} -> list A)
               (cons : {A} -> A -> list A -> list A)
               (app : {A} -> list A -> list A -> list A)
               (rev : {A} -> list A -> list A)
               (sll : {A} -> (Z -> A -> Assertion) -> Z -> list A -> Assertion)
               (sllseg : {A} -> (Z -> A -> Assertion) -> Z -> Z -> list A -> Assertion)
 */

struct list *append(struct list *x, struct list *y)
/*@ With {A} storeA (l1 : list A) l2
    Require sll(storeA, x, l1) * sll(storeA, y, l2)
    Ensure  sll(storeA, __return, app(l1, l2))
*/
{
   if (x == (void *)0) {
      return y;
   } else {
      /*@ x != 0 && sll(storeA, x, l1)
          which implies 
          exists a l1_, l1 == cons(a, l1_) && storeA(x->head, a) * sll(storeA, x->next, l1_)
      */
      struct list *t, *u;
      u = x->next;
      if (u == (void *)0) {
         x->next = y;
         return x;
      }
      t = x;
      u = t->next;
      /*@ Inv
            exists l1a b l1c,
               app(l1a, cons(b, l1c)) == l1 &&
               t->next == u && storeA(t->head, b) &&
               sllseg(storeA, x, t, l1a) *
               sll(storeA, u, l1c) * sll(storeA, y, l2)
      */
      while (u != (void *)0) {
         /*@ exists l1c, u != 0 && sll(storeA, u, l1c)
             which implies 
             exists a l1d, l1c == cons(a, l1d) && storeA(u->head, a) * sll(storeA, u->next, l1d)
         */
         t = u;
         u = t->next;
      }
      t->next = y;
      return x;
   }
}