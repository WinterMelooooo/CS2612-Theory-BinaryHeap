struct list {
  void *head;
  struct list *next;
};

//@ Export Coq Goal "merge_wh_goal.v"
//@ Export Coq Proof "merge_wh_proof.v"


/*@ Extern Coq (nil : {A} -> list A)
               (cons : {A} -> A -> list A -> list A)
               (app : {A} -> list A -> list A -> list A)
               (storeZ : Z -> Z -> Assertion)
               (Le : Z -> Z -> Prop)
               (sll : {A} -> (Z -> A -> Assertion) -> Z -> list A -> Assertion) 
               (ordered : {A} -> (A -> A -> Prop) -> list A -> Prop) 
 */

struct list *merge(struct list *x, struct list *y, int (*cmp)(void *x, void *y))
/*@ With {A} (storeA : Z -> A -> Assertion) (le : A -> A -> Prop)
    Require exists l1 l2,
            ordered(le, l1) && ordered(le, l2) &&
            (cmp |= int (void *x, void *y)
                  With a b
                  Require storeA(x, a) * storeA(y, b)
                  Ensure __return <= 0 && le(a, b) * storeA(x, a) * storeA(y, b)  || __return > 0 && le(b, a) * storeA(x, a) * storeA(y, b)) &&
            sll(storeA, x, l1) * sll(storeA, y, l2)
    Ensure exists l, ordered(le, l) && sll(storeA, __return, l)
 */;

struct list * malloc_ordered_Zlist()
/*@ Require emp
    Ensure exists l, ordered(Le, l) && sll(storeZ, __return, l)
*/;


int Zcmp(void *x, void *y)
/*@ With a b
    Require storeZ(x, a) * storeZ(y, b)
    Ensure __return <= 0 && Le(a, b) && storeZ(x, a) * storeZ(y, b)  || __return > 0 && Le(b, a) && storeZ(x, a) * storeZ(y, b)
*/;

int main()
{
  struct list *x, *y, *z;
  x = malloc_ordered_Zlist();
  y = malloc_ordered_Zlist();
  z = merge(x, y, Zcmp) /*@ where storeA = storeZ, le = Le; A = Z */;  
  return 0;
}