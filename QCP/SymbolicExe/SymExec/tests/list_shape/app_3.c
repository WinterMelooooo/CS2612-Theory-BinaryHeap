struct list {
    int head;
    struct list *tail;
};

/*@ Let listrep(l) = l == 0 && emp || listrep(l->tail) */

/*@ Let lseg(x, y) = x == y && emp || lseg(x->tail, y) */

struct list * append_3(struct list * x, struct list * y, struct list * z)
/*@ Require listrep(x) * listrep(y) * listrep(z)
    Ensure  listrep(__return)
 */
{
    struct list *t;
    struct list *u;
    if (x == (void *)0) {
        if (y == (void *)0) {
            return z;
        } else {
            t = y;
            u = t->tail;
            /*@ Inv u == t->tail &&
                listrep(z) *
                listrep(u) *
                lseg(y, t)
             */
            while (u) {
                t = u;
                u = t->tail;
            }
            t->tail = z;
            return y;
        }
    } else {
        t = x;
        u = t->tail;
        /*@ Inv u == t->tail &&
            listrep(z) *
            listrep(y) *
            listrep(u) *
            lseg(x, t)
         */
        while (u) {
            t = u;
            u = t->tail;
        }
        t->tail = y;
        u = t->tail;
        /*@ Inv u == t->tail &&
            listrep(z) *
            listrep(u) *
            lseg(x, t)
         */
        while (u) {
            t = u;
            u = t->tail;
        }
        t->tail = z;
        return x;
    }
}
