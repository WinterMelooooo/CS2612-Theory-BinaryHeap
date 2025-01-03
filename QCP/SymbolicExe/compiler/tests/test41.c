int f() {
  int x, y, z;
  int *p;
  p = x ? &y : &z;
  int a[2 ? 3 : 4];
  int b[2 ? 3 : z];
}
