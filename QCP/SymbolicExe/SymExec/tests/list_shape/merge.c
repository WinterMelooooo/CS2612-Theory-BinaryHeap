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

struct list *merge(struct list *x , struct list *y)
/*@ Require listrep(x) * listrep(y)
    Ensure  listrep(__return)
 */
{
    struct list *z;
    struct list *t;
    if (x == (void *)0) {
      return y; 
    }
    else {
      z = x;
      /*@ Inv x != 0 && lseg(z , x) * listrep(x) * listrep(y) */
      while (y) {
        t = y -> tail;
        y -> tail = x -> tail;
        x -> tail = y;
        if (y -> tail == (void *)0) {
          y -> tail = t;
          return z;
        }
        else {
          x = y -> tail;
          y = t;
        }
      }
    }
    
    return z;
}
