int x;

int f() {
  x = 0;
  x += 1;
  x = (int)4294967295;
  x = x;
  x += x;
  int y;
  y = x;
  x = y;
  y += x;
  x += y;
  x = x * y;
  int *p;
  p = &x;
  *p = x;
  //@ x == 1
  //@ p == &x
  return y;
}
