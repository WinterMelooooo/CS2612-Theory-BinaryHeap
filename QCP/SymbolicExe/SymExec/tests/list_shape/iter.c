struct list {
    int head;
    struct list *tail;
};

/*@ Let listrep(l) = l == 0 && emp ||
      exists t, (l->tail == t) * listrep(t)
 */
 
/*@ Let lseg(x, y) = x == y && emp ||
      exists z, (x->tail == z) * lseg(z, y)
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
        p = p->tail;
    }
    return l;
}
