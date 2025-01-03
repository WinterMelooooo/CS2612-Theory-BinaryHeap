struct data_record {
    int d1;
    int d2;
};

struct list {
    struct data_record *data;
    struct list *next;
};

/*@ Let datarep(p) = p == 0 && emp ||
      exists v1 v2,
        p->d1 == v1 && p->d2 == v2 && emp
 */

/*@ Let listrep(l) = l == 0 && emp ||
      datarep(l->data) * listrep(l->next)
 */

/*@ Let lseg(x, y) = x == y && emp ||
      datarep(x->data) * lseg(x->next, y)
 */

struct list *iter(struct list *l)
/*@ Require listrep(l)
    Ensure  listrep(__return)
 */
{
    struct list *p;
    struct data_record *v;
    p = l;
    /*@ Inv listrep(p) * lseg(l, p) */
    while (p) {
        v = p->data;
        if (v) {
            if (v->d1 == 0) {
                v ->d2 = 1;
            }
        }
        p = p->next;
    }
    return l;
}
