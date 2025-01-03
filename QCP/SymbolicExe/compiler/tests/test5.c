//@ Extern Coq (sublist : {A} -> list A -> Z -> Z -> list A)

int f() {
  int a[10];
  int *p;
  //@ exists l, Arr(p, 10, l) && l[0] == 0
  //@ a[0] == 0
  //@ exists l, Arr(p, 10, l) && sublist(l, 2, 5)[3] == 0
  //@ exists l, Arr(a + 5, int, 5, l) && (a + 5)[0] == 0
  //@ forall i, 0 <= i && i < 10 => exists n, a[i] == n * 2
}
