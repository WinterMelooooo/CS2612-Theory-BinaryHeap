struct list {
    int head;
    struct list *tail;
};

/*@ Let listrep(l) = l == 0 && emp || listrep(l->tail) */

struct list *reverse(struct list *p)
/*@ Require listrep(p)
    Ensure  listrep(__return)
 */
{
    struct list *w;
    struct list *t;
    struct list *v;
    w = (void *)0;
    v = p;
    /*@ Inv listrep(w) * listrep(v) */
    while (v) {
        t = v->tail;
        v->tail = w;
        w = v;
        v = t;
    }
    return w;
}
