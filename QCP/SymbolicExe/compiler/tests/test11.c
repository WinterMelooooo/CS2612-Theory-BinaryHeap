int f() {
  {
    long long x;
    char y;
    short z;
    x = (long long)0;
    y = (char)0;
    z = (short)0;
    if (x < (long long)1)
      ;
    if ((long long)1 < x)
      ;
    if ((long long)1 < (long long)1)
      ;
    if (x < (long long)4294967295)
      ;
    if ((long long)4294967295 < x)
      ;
    if (y < y)
      ;
    if (z < z)
      ;
  }

  {
    int x;
    x = 1;
    x = ~x;
  }

  {
    int si;
    unsigned int ui;
    long long sl;
    unsigned long long ul;
    si = 0;
    ui = (unsigned int)0;
    sl = (long long)0;
    ul = (unsigned long long)0;
    sl = (long long)si;
    sl = (long long)ui;
    ul = (unsigned long long)si;
    ul = (unsigned long long)ui;
  }

  {
    long long x;
    x = (long long)0;
    x += (long long)4294967295;
  }

  return 0;
}
