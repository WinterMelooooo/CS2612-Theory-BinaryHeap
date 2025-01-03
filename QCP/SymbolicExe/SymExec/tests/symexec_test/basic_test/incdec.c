struct list {
    int head;
    struct list* tail;
};

int main(int a, int b, int c, struct list * d)
/*@ Require a == 1 && (d->{list.head} == b)
    Ensure emp
*/
{
    ++a;
    --a;
    a++;
    a--;
    ++(d->head);
    --(d->head);
    (d->head)++;
    (d->head)--;
}
