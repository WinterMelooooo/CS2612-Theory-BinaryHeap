//@ Extern Coq (nil : nat)

//@ Let P(x) = x == 0

int g();

struct X {
  int x;
};

int f() {
  int x;
  struct X *xx;
  g() /*@ where x = &x, p = nil ; A = nat */;
  //@ (exists y, x == y) || (exists y, x != y) which implies (x != y + 1) || (exists y, x == y)
  //@ exists (x : Z), x == 1 which implies x == 1
  //@ exists [x : Z], x == 1 which implies x == 1
  //@ xx != 0 which implies xx->x == 0
  //@ xx->x == 0 which implies xx != 0
  //@ xx->x == 0 which implies xx->x == 0
  g() /*@ where x = x, y = *{int}x */;
  g() /*@ where ; A = Prop */;
  //@ x == 0 which implies x == 0 || x == 1
  /*@ x == 0 || x == 1 which implies
      x == 2 || (x == 3 || x == 4) */
}

