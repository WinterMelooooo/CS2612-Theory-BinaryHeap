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

struct list *rev_append_twice(struct list *p, struct list *q)
/*@ Require listrep(p) * listrep(q)
    Ensure  listrep(__return)
 */
{
    struct list *w;
    struct list *t;
    struct list *v;
    w = q;
    v = p;
    /*@ Inv lseg(w, q) * listrep(v) * listrep(q) */
    while (v) {
      t = v->tail;
      v->tail = w;
      w = v;
      v = t;
      if (v) {
        t = v->tail;
        v->tail = w;
        w = v;
        v = t;
      }
    }
    return w;
}
