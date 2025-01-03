struct list {
    int head;
    struct list* tail;
};

int main(int a, int b, int c, struct list * d)
/*@ Require a == 1 && (d->{list.head} == b) * (d->{list.tail} == d)
    Ensure emp
*/
{
    a = 2;
    b = 3;
    a = a + b;
    c = a + b + c + d->head;
    d->head = d->head + d->head + d->head;
    d->tail = d->tail;
}
