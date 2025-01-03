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
        b = 0;
        if (b) {
            c = 0;
        } else {
            c = 1;
        }
    }
}
