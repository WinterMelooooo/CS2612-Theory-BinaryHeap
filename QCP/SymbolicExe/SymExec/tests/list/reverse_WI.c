struct list {
   void* head;
   struct list *next;
};

//@ Export Coq Goal "reverse_wi_goal.v"
//@ Export Coq Proof "reverse_wi_proof.v"

/*@ Extern Coq (nil : {A} -> list A)
               (cons : {A} -> A -> list A -> list A)
               (app : {A} -> list A -> list A -> list A)
               (rev : {A} -> list A -> list A)
               (sll : {A} -> (Z -> A -> Assertion) -> Z -> list A -> Assertion)
 */

struct list *reverse(struct list *p) 
/*@ With {A} storeA (l : list A)
    Require sll(storeA, p, l)
    Ensure sll(storeA, __return, rev(l))
*/
{
   struct list *w;
   struct list *v;
   w = (void *)0;
   v = p;
   /*@ Inv exists l1 l2,
            l == app(rev(l1), l2) && 
            sll(storeA, w, l1) * sll(storeA, v, l2)
      */
   while (v) {
      /*@ exists l2, v != 0 && sll(storeA, v, l2)
          which implies 
          exists x xs, l2 == cons(x, xs) && storeA(v->head, x) * sll(storeA, v->next, xs)
      */
      struct list *t;
      t = v->next;
      v->next = w;
      w = v;
      v = t;
   }
   return w;
}