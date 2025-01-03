struct list {
    int head;
    struct list *tail;
};

/*@ Let listrep(l) = l == 0 && emp || listrep(l->tail) */

/*@ Let lseg(x, y) = x == y && emp || lseg(x->tail, y) */

struct list * append(struct list * x, struct list * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct list *t;
    struct list *u;
    if (x == (void *)0) {
        return y;
    } else {
        t = x;
        u = t->tail;
        /*@ Inv u == t->tail &&
            listrep(y) *
            listrep(u) *
            lseg(x, t)
         */
        while (u) {
            t = u;
            u = t->tail;
        }
        t->tail = y;
        return x;
    }
}
