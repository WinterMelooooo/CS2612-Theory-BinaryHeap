/*@ Extern Coq addr := Z */
/*@ Extern Coq AddrList := list addr */
/*@ Extern Coq (cons : {A} -> A -> list A -> list A) */

int f() {
  /*@ exists (n : Z) (l : AddrList), l == cons(n, l) */
}
