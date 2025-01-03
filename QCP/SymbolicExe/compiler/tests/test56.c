//@ Extern Coq (EDenote :: *) (CDenote :: *)
/*@ Extern Coq Field (nrm : EDenote -> Z -> Prop)
                     (nrm : CDenote -> Z -> Z -> Prop) */
/*@
  Extern Coq Record nelistZ = MkList {
    head: list Z;
    last: Z;
  } */

int f()
/*@ With (l: nelistZ) (nil: list Z)
    Require l.last == 0
    Ensure  l.last == MkList(nil, 0).last */
{
  //@ exists (D1: EDenote) (D2: CDenote), D1.nrm(0) && D2.nrm(0, 0) && emp
}
