int f() {
  int *x;
  // OK:
  //@ forall y, *{int}x == y
  // not OK:
  //@ forall y, *{int}y == x
}
