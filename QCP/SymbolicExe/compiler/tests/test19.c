void swap(int * px, int * py)
/*@ With x y
    Require (px != py) && x == *px && y == *py
    Ensure  y == *px && x == *py
*/;

void swap(int * px, int * py)
/*@ With x y
    Require (px != py) && x == *px && y == *py
    Ensure  y == *px && x == *py
*/
{
  int t;
  t = * px;
  * px = * py;
  * py = t;
}
