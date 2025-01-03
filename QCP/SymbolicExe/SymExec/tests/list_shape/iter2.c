struct list {
    int data;
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
    struct list *q;
    p = l;
    /*@ Inv listrep(p) *
        lseg(l, p) */
    while (p) {
        q = p->tail;
        /*@
          Inv exists p1,
            (p->tail == p1) *
            lseg(p1, q) *
            listrep(q) *
            lseg(l, p)
         */
        while (q) {
           q = q->tail;
        }
        p = p->tail;
    }
    return l;
}
