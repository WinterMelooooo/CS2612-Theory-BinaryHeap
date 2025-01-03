int x;
int x;
int x;
struct A;
struct A { int x; };
struct A;
union B;
union B { int x; };
union B;
enum C;
enum C { X, Y };
enum C;
typedef int D;
typedef int D;
typedef int D;
int f(int a, int b, int c)
/*@
  Require a == b && b == c
  Ensure a == b && b == c && c == __return
*/;
int f(int a, int b, int c)
/*@
  Require a == b && b == c
  Ensure a == b && b == c && c == __return
*/
{
  return 0;
}
int f(int a, int b, int c)
/*@
  Require a == b && b == c
  Ensure a == b && b == c && c == __return
*/;

