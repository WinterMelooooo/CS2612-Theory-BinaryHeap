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

struct list *reverse(struct list *p)
/*@ Require listrep(p)
    Ensure  listrep(__return)
 */;

struct list *append(struct list * x, struct list * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */;

struct list *multi_rev(struct list *p, struct list *q)
/*@ Require listrep(p) * listrep(q)
    Ensure  listrep(__return)
 */
{
    struct list *w;
    struct list *t;
    struct list *v;
    struct list *x;
    struct list *y;
    w = (void *)0;
    x = (void *)0;
    v = p;
    y = q;
    /*@ Inv listrep(w) * listrep(v) * listrep(x) * listrep(y) */
    while (1) {
      if (v) {
        t = v->tail;
        v->tail = w;
        w = v;
        v = t;
      }
      else {
        if (y) {
          t = y->tail;
          y->tail = x;
          x = y;
          y = t;
        }
        else { 
          t = append(w , x);
          return t;
        }
      }
    }
  // Deadcode : return 0;
}
