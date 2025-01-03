int f() {
  {
    int x, *y, **z, *w;
  }
  {
    int x = 1, y = x, *z = &y;
  }
  {
    struct { int x; } x, *y, z[10];
  }
}
