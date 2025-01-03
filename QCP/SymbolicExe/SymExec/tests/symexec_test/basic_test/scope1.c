int main() 
/*@ Require emp
    Ensure emp
*/
{
    int a;
    a = 1;
    {
        int b;
        b = a + 1;
        a = b + 1;
    }
    if (a == 3) {
        int c;
        c = a - 1;
    } else {
        int d;
        d = a + 1;
    }
    while (a > 0) {
        int e;
        e = a - 1;
        a = e;
        //@ a >= 0 && emp
    }
    return a;
}