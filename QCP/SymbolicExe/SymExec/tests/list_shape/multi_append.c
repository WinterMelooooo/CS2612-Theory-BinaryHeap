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

struct list * append(struct list * x, struct list * y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */;

struct list *multi_append(struct list *x, struct list *y, struct list *z)
/*@ Require listrep(x) * listrep(y) * listrep(z)
    Ensure  listrep(__return)
 */
{
    struct list *t;
    struct list *u;
    if (x == (void *)0) {
        t = append(y , z);
        return t;
    } else {
        t = x;
        u = t->tail;
        /*@ Inv (t->tail == u) * 
            listrep(y) *
            listrep(z) * 
            listrep(u) *
            lseg(x, t)
         */
        while (u) {
            if (y) {
              t -> tail = y;
              t = y;
              y = y -> tail;
              t -> tail = u;
              t = u;
              u = u -> tail;
            }
            else {
              u = append(u , z);
              t -> tail = u;
              return x;   
            }
        }
        t->tail = append(y,z);
        return x;
    }
}
