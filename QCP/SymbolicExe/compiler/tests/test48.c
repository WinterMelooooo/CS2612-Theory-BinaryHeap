//@ Extern Coq (Z::lt : Z -> Z -> Z)

int f() {
  int x = 0;
  /*@ x == 0 by core */
  x = 1;
  /*@ Assert x == 1 by core */
  x = x;
  /*@ x == x by core which implies x == x by core */
  /*@ x == x which implies x == x by core */
  /*@ x == x by core which implies x == x */
  /*@ Assert Inv x > 0 by core */
  while (1) {
    x++;
  }
  return x;
}
