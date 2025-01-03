/*@
  Extern Coq Record nelist (A :: *) = mk {
    head: list A;
    last: A;
  } */

/*@ Extern Coq (nil : list Z) */
/*@ Extern Coq Field (f: {A} -> A -> A) */

void f()
/*@ With (l: nelist Z)
    Require l.last == 0 && l.f == f
    Ensure  (mk(nil, 0)).last == 0 */
{ }
