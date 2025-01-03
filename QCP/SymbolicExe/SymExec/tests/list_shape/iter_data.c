struct list {
    int data1;
    int data2;
    struct list *tail;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists v1 v2,
        l->data1 == v1 &&
        l->data2 == v2 &&
        listrep(l->tail)
 */

/*@ Let lseg(x, y) = x == y && emp ||
      exists v1 v2,
        x->data1 == v1 &&
        x->data2 == v2 &&
        lseg(x->tail, y)
 */

struct list *iter(struct list *l)
/*@ Require listrep(l)
    Ensure  listrep(__return)
 */
{
    struct list *p;
    p = l;
    // p->data1 = 1;
    /*@ Inv listrep(p) * lseg(l, p) */
    while (p) {
        if (p->data1 == (void *)0) {
            p->data2 = 1;
        }
        p = p->tail;
    }
    return l;
}
