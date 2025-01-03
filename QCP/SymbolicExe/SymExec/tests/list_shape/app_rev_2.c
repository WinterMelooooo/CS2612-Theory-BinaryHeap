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

//    append_reverse(x, y)
// == append(reverse(y), reverse(x))
// == reverse(append(x, y)) (here)

struct list * append_reverse(struct list * x, struct list * y)
/*@ Require listrep(x) * listrep(y)
    Ensure listrep(__return)
 */
{
    struct list *result;
    if (x == (void *)0)
        result = y;
    else {
        struct list *t;
        struct list *u;
        t = x;
        u = t->tail;
        /*@ Inv listrep(y) *
            listrep(u) *
            lseg(x, t) *
            (t->tail == u)
         */
        while (u) {
            t = u;
            u = t->tail;
        }
        t->tail = y;
        result = x;
    }

    struct list *w;
    struct list *t;
    struct list *v;
    w = (void *)0;
    v = result;
    /*@ Inv listrep(w) * listrep(v) */
    while (v) {
        t = v->tail;
        v->tail = w;
        w = v;
        v = t;
    }
    return w;
}
