void swap(int * px, int * py)
/*@ neq : all
    With x y
    Require (px != py) && x == *px && y == *py
    Ensure  y == *px && x == *py
*/;

void swap(int * px, int * py)
/*@ all
    With x y
    Require (px != py) && x == *px && y == *py || px == py && x == y && x == *py
    Ensure (px != py) && y == *px && x == *py || px == py && x == *py
*/
{
  int t;
  t = * px;
  * px = * py;
  * py = t;
}

int f() {
  int x = 1;
  int y = 2;
  swap(&x, &y) /*@ neq where x = 1, y = 2 */;
}
