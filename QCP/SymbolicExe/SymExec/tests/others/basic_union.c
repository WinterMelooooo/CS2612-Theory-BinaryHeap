struct TS {
  int S1;
  int S2;
};

union TU {
  struct TS U1;
  struct TS U2;
};

/*@ Extern Coq (StoreTS : Z -> Z -> Z -> Assertion) */
/*@ Extern Coq (partial_store_TS_missing1: Z -> Z -> Assertion)*/
/*@ Extern Coq (partial_store_TS_missing2: Z -> Z -> Assertion)*/

int test(union TU * u)
/*@ Require data_at(&(u->U1.S1), 0) * data_at(&(u->U1.S2), 1)
    Ensure __return == 0
*/
{
  u->U2.S1 = u->U1.S1;
  return u->U2.S1;
}

int test2(union TU * u)
/*@ With x y
    Require StoreTS(&(u->U1), x, y)
    Ensure  exists v, __return == x + 1 && StoreTS(&(u->U1), x + 1, v)
*/
{
  u->U1.S1 = u->U1.S1 + 1;
  return u->U1.S1;
}

int test3(union TU * u)
/*@ With x y
    Require StoreTS(&(u->U1), x, y)
    Ensure  exists v, __return == x + 1 && StoreTS(&(u->U2), x + 1, v)
*/
{
  u->U2.S1 = u->U1.S1 + 1;
  return u->U2.S1;
}