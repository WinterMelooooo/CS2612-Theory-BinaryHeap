int slow_add(int x, int p)
/*@ With x0 p0
    Require (x == x0) && (p == p0) && (1 <= x) && (x <= 100) && (1 <= p) && (p <= 100) && emp
    Ensure __return == (x + p) && emp
*/
{
    while (p) {
        x++;
        p--;
        //@ x + p == (x0 + p0) && 1 < x && x <= 101 && 0 <= p && p <= 99 && emp
    }
    return x;
}
