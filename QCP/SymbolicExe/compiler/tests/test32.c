struct X {
  int x;
};

struct Y {
  struct X x[10];
};

int f() {
  int a = 1;
  int aa[10] = {1, [3] = 2, 3};
  struct X x = {.x = 1};
  struct X xx = {1};
  struct Y y = {.x = {{.x = 1}}};
  struct Y yy[100] = {[0].x[0].x = 1};
}
