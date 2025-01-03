// This case can't be executed becuase invariant is left empty.

int slow_mul(int x, int p)
/*@ Require 1 <= x && x <= 10000 && 1 <= p && p <= 10000 && emp
    Ensure __return == x * p && emp
*/
{
    int ans;
    ans = 0;
    while (p) {
        if (p & 1) ans += x;
        p >>= 1;
        x = x + x;
    }
    return ans;
}