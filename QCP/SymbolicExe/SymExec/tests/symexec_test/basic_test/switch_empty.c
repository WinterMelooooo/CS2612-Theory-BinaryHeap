// special case: switch statement with no cases
// symexec accept. But coq ACStmt_to_ps may need to be modified

struct list {
    int head;
    struct list* tail;
};

int main(int a, int b, int c, struct list * d)
/*@ Require a == 1 && (d->{list.head} == b) * (d->{list.tail} == d)
    Ensure emp
*/
{
    switch (a) {}
}
