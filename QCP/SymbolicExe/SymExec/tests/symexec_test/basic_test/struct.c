struct list {
    int head;
    struct list * next;
};



int main(struct list * l, struct list * l2, struct list * l3)
/*@ Require (l->{list.head} == 2) * (l->{list.next} == l2) * (l2->{list.head} == 3) * (l2->{list.next} == l3) * (l3->{list.head} == 4)
    Ensure __return == 2 && emp
*/
{
    struct list * tmp;
    tmp = l;
    tmp = tmp->next;
    tmp = tmp->next;
    return tmp->head;
}