int slow_add(int x, int p)
/*@ With x0 p0
    Require (x == x0) && (p == p0) && (1 <= x) && (x <= 100) && (1 <= p) && (p <= 100) && emp
    Ensure __return == x0 + p0
*/
{
    while (p) {
        x++;
        p--;
        //@ x + p == x0 + p0 && 1 < x && x <= 200 && 0 <= p && p <= 99 && emp
    }
    return x;
}

int slow_add2(int x, int p)
/*@ With x0 p0
    Require (x == x0) && (p == p0) && (1 <= x0) && (x0 <= 100) && (1 <= p0) && (p0 <= 100) && emp
    Ensure __return == x0 + p0 && emp
*/
{
    while (p) {
        p--;
        x++;
        if (p % 3 != 0) {
            p--;
            x++;
        }
        //@ x + p == x0 + p0 && 1 < x && x <= 200 && 0 <= p && p <= 99 && emp
    }
    return x;
}