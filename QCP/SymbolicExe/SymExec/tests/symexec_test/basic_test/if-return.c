struct list {
    int head;
    struct list* tail;
};

int main(int a, int b, int c, struct list * d)
/*@ Require a == 1 && (d->{list.head} == b) * (d->{list.tail} == d)
    Ensure emp
*/
{
    if (a) {
        b = c;
        if (b) {
            return 1234;
        } else {
            b = a;
        }
        return b;
    }
}
