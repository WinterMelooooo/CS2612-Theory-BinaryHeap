struct X {
  char c;
  long long ll;
  int x;
};

struct Y {
  char a;
  struct X x[10];
};

struct X z;

int f()
/*@ Require emp
  Ensure emp */
{
  struct X x;
  struct X y;
  x = y;
  y = x;
  y = y;
  x = x;
  z = x;
  x = z;

  if (1) {
    struct Y z;
    struct Y w;
    z = w;
  }
  return x.x;
}
