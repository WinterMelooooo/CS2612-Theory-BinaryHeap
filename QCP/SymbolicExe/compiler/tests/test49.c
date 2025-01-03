/*@ Extern Coq (state :: *) */

/*@ Extern Coq Record EDenote {
      nrm: state -> Z -> Prop;
      err: state -> Prop;
    } */

struct EDenote {
  int nrm;
  int err;
};

void f() {
  /*@ exists D s n, (D.nrm)(s, n) && emp */
  /*@ exists D, D->nrm == D->err */
}
