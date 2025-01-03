struct list {
    int head_;
    struct list *tail_;
};

struct listlist {
    struct list *head;
    struct listlist *tail;
};

/*@ Let listrep(l) = l == 0 && emp || listrep(l->{list.tail_})
 */

/*@ Let lseg(x, y) = x == y && emp || lseg(x->{list.tail_},y)
 */

/*@ Let listlistrep(l) = l == 0 && emp ||
        listrep(l->head) * listlistrep(l->tail)
 */

/*@ Let listlseg(x, y) = x == y && emp ||
      	listrep(x->head) * listlseg(x->tail, y)
 */

struct list * expand(struct listlist * x)
/*@ Require listlistrep(x)
    Ensure listrep(__return) * listlistrep(x)
*/
{
    struct listlist *t;
    struct list *v;
    struct list *ans;
    t = x;
    ans = (void *)0;
    /*@ Inv listlistrep(t) * listlseg(x, t) * listrep(ans) */
    while (t) {
      v = t->head;
      if (v) {
        /*@ Inv v != 0 && listlistrep(t->tail) *
          listlseg(x, t) *
          lseg(t->head, v) *
          listrep(v) * listrep(ans)
        */
      	while (v -> tail_) {
        	v = v -> tail_;
      	}
      	v -> tail_ = ans;
        ans = t -> head;
      	t -> head = (void *)0;
      }
      t = t->tail;
   }
   return ans;
}
