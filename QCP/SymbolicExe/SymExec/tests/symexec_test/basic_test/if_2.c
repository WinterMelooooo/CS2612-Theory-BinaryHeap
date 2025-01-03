struct list {
    int head;
    struct list* tail;
};

int main(int a, int b, int c, struct list * d)
/*@ Require a == 1 && (d->{list.head} == b) * (d->{list.tail} == d)
    Ensure emp
*/
{
    if (d->head == b && d->tail == (struct list * ) 0) {
        a = (a && (b == 1)) || (c > 2);
        b = b < 2 && b != 3 && b <= 1 && b >= -1;
    } else {
        d->head = ((((((((a + b - 1) * c / d->head) & a) | b) & c) % d->head) << 1) >> 1234) ^ 0;
        if (1 < d->head || d->head > 10) {
            a = d->head;
        } else {
            a = b;
        }
    }
}
