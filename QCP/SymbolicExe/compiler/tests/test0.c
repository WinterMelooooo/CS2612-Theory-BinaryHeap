struct list {
    int head;
    struct list *tail;
};

/*@ Let listrep(l) = l == 0 ||
      exists t, (l->tail == t) * listrep(t)
 */

/*@ Let lseg(x, y) = x == y ||
      exists z, (z->tail == z) * lseg(z, y)
 */

int find_ring(struct list *p)
/*@ With p1 p2
    Require listrep(p) || lseg(p, p1) * lseg(p1, p2) * (p2->tail == p1)
    Ensure lseg(p, p1) * lseg(p1, p2) * (p2->tail == p1)
 */
{
    struct list * x;
    struct list * y;
    if (p == (struct list *)0) 
        return 0; 
    else {
        x = p;
        y = p->tail;
        /*@ Inv (lseg(p, x) * lseg(x, y) * listrep(y)) ||
          (exists p1, exists p2,
            lseg(p, x) * lseg(x, y) * lseg(y, p1) * lseg(p1, p2) * (p2->tail == p1)) ||
            (exists p1, exists p2,
            lseg(p, x) * lseg(x, p1) * lseg(p1, y) * lseg(y, p2) * (p2->tail == p1)) ||
            (exists p1, exists p2,
            lseg(p, p1) * lseg(p1, x) * lseg(x, y) * lseg(y, p2) * (p2->tail == p1)) ||
            (exists p1, exists p2,
            lseg(p, p1) * lseg(p1, y) * lseg(y, x) * lseg(x, p2) * (p2->tail == p1))
        */
        while (y != (struct list *)0) {
            if (x == y)
                return 1;
            else if (y->tail == (struct list *)0)
                return 0;
            else {
                x = x->tail;
                y = y->tail->tail;
            }
        }
        return 0;
    }
}
