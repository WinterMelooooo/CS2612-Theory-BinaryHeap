/*@ Extern Coq (app : {A} -> list A -> list A -> list A)
               (rev : {A} -> list A -> list A)
               (sublist : {A} -> list A -> Z -> Z -> list A)
               (nil : {A} -> list A) */

//@ Let listEq(l1 : list Z, l2 : list Z) = emp

struct pair {
  struct pair *car;
  struct pair *cdr;
};

int f() {
  struct pair *p;
  /*@ exists l, Arr(p, 10, l) && listEq(app(rev(l), nil), sublist(l, 0, 1)) */
}
