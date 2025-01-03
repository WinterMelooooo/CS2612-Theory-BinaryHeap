int f() {
  int x;
  int *p;
  int y;
  int z;
  p = &x;
  x = 0;
  x = x;
  x += 1;
  x -= x;
  //@ &y == 0
  y = y;
  //@ z == 1
  z = z;
  return 0;
}
