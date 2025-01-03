struct list {
    struct { int d1; int d2; } data;
    struct list *next;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists v1 v2,
        l->data.d1 == v1 &&
        l->data.d2 == v2 &&
        listrep(l->next)
 */

/*@ Let lseg(x, y) = x == y && emp ||
      exists v1 v2,
        x->data.d1 == v1 &&
        x->data.d2 == v2 &&
        lseg(x->{list.next}, y)
 */

struct list *iter(struct list *l)
/*@ Require listrep(l)
    Ensure  listrep(__return)
 */
{
    struct list *p;
    p = l;
    /*@ Inv listrep(p) * lseg(l, p) */
    while (p) {
        if ((p->data).d1 == 0) {
            (p->data).d2 = 1;
        }
        p = p->next;
    }
    return l;
}
