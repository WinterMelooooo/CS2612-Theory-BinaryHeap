struct list {
    int head;
    struct list* tail;
};

int main(int a, int b, int c, struct list * d)
/*@ Require a == 1 && (d->{list.head} == b) * (d->{list.tail} == d)
    Ensure emp
*/
{
    int x;
    struct list * y;
    d->tail = y;
    x = b;
    if (x != -1) {
        switch (b) {
            default:
                if (c == 0) c = 2;
        }
        int z;
        ++z;
        d->head = ~z;
    }
}
