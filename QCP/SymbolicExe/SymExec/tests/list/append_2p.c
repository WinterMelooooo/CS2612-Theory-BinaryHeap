struct list {
   void* head;
   struct list *next;
};

//@ Export Coq Goal "append_2p_goal.v"
//@ Export Coq Proof "append_2p_proof.v"

/*@ Extern Coq (nil : {A} -> list A)
               (cons : {A} -> A -> list A -> list A)
               (app : {A} -> list A -> list A -> list A)
               (rev : {A} -> list A -> list A)
               (sll : {A} -> (Z -> A -> Assertion) -> Z -> list A -> Assertion)
               (sllseg : {A} -> (Z -> A -> Assertion) -> Z -> Z -> list A -> Assertion)
               (lbseg : {A} -> (Z -> A -> Assertion) -> Z -> Z -> list A -> Assertion)
 */

struct list ** append_2p(struct list ** x, struct list ** y)
/*@ With {A} storeA l1 l2
    Require sll(storeA, *x, l1) * sll(storeA, *y, l2)
    Ensure  exists py, sll(storeA, *(__return), app(l1, l2)) * data_at(y, py)
*/
{
  struct list ** t;
  t = x;
  /*@ Inv
        exists l3, exists l4, exists pt,
          y == y@pre && l1 == app(l3, l4) &&
          lbseg(storeA, x, t, l3) * sll(storeA, *t, l4) * sll(storeA, *y, l2)
  */
  while (* t != (void *) 0) {
    /*@ exists l3, exists l4, exists l5, exists pt, exists h,
         y == y@pre && l1 == app(l3, l4) && l4 == cons(h, l5) &&
         lbseg(storeA, x, t, l3) * storeA((*t)->head, h) * sll(storeA, (*t)->next, l4) * sll(storeA, *y, l2)
    */
    t = &((*t) -> next);
  }
  *t = *y;
  return x;
}