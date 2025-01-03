struct list {
    int data;
    struct list * next;
};
int func(int n, struct list * balabala) {
    return 1;
}
int main() 
/*@ Require emp
    Ensure __return == 0 && emp
*/
{
    int a;
    struct list * l;
    for (a = 1; a <= 10; ++a) {
        do {
            a = a + 1;
        } while (a < 5);
        a = func(a, l);
    }
    return 0;
}
