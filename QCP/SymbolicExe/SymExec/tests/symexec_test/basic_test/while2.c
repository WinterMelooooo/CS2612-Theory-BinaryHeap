struct list {
    int head;
    struct list* tail;
};

int main(int a, int b, int c, struct list * d)
/*@ Require (1 <= a) && (a <= 100) && emp
    Ensure emp
*/
{
    int x;
    x = 1;
    while (x < a) {
        x = x + 1;
        //@ (1 <= a) && (a <= 100) && (x <= a) && emp
    }
    //@ (1 <= a) && (a <= 100) && (x == a) && emp
}
