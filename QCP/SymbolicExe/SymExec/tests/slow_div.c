int slow_div(int n, int a) 
/*@ With a0 b0
    Require n >= 0 && a > 0 && a == a0 && a0 * b0 <= n && n < a0 * (b0 + 1) && emp
    Ensure __return == b0 && emp
*/
{
    int cnt;
    cnt = 0;
    while (1) {
        n = n - a;
        ++cnt;
        if (n < a) {
            break;
        }
        //@ n >= 0 && a0 * b0 <= (n + a * cnt) && (n + a * cnt) < a0 * (b0 + 1) && emp
    }
    return cnt;
}