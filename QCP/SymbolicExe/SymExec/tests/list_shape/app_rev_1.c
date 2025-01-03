// unpassed

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
// == append(reverse(y), reverse(x)) (here)
// == reverse(append(x, y))

struct list * append_reverse(struct list * x, struct list * y)
/*@ Require listrep(x) * listrep(y)
    Ensure listrep(__return)
 */
{
    struct list *w1;
    struct list *t1;
    struct list *v1;
    w1 = (void *)0;
    v1 = y;
    /*@ Inv y == v1 && w1 == 0 && listrep(v1) * listrep(x)
     || listrep(v1) * lseg(w1, y) * (y->tail == 0) * listrep(x) */
    while (v1) {
        t1 = v1->tail;
        v1->tail = w1;
        w1 = v1;
        v1 = t1;
    }

    struct list *w2;
    struct list *t2;
    struct list *v2;
    w2 = (void *)0;
    v2 = x;
    /*@ Inv y == v1 && v1 == 0 && listrep(w2) * listrep(v2)
     || listrep(w2) * listrep(v2) * lseg(w1, y) * (y->tail == 0) */
    while (v2) {
        t2 = v2->tail;
        v2->tail = w2;
        w2 = v2;
        v2 = t2;
    }
    if (y) {
     y->tail = w2;
     return w1;
    }
  	else {
      return w2;
    }
}
