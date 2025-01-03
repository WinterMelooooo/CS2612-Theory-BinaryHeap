struct list {
    int head;
    struct list* tail;
};

int main(int a, int b, int c, struct list * d)
/*@ Require a == 1 && (d->{list.head} == b) * (d->{list.tail} == d)
    Ensure emp
*/
{
    c = 10;
    switch (a) {
        case 1:
            b = 1;
        case 2:
            b = 2;
        default:
            b = c;
    }
}
