struct list {
   int head;
   struct list *tail;
};

//@ Extern Coq app, rev, cons, nil
/*@ Let repr(p, l) = p == NULL && l == nil && emp || 
                     exists x y l' , p != NULL && l == cons(x,l') && data_at(field_addr(p, head), x) * data_at(field_addr(p, tail), y) * repr(y, l')
*/
/*@ Let lseg(p, q, l) = p == q && l == nil && emp || 
                     exists x y l' , p != q && l == cons(x,l') && data_at(field_addr(p, head), x) * data_at(field_addr(p, tail), y) * lseg(y, q, l')
*/
//@ Let data_at_head(p, x) = data_at(field_addr(p, head), x)
//@ Let data_at_tail(p, x) = data_at(field_addr(p, tail), x)

void split_listrep(struct list *p)
/*@ With t
    Require data_at(field_addr(p, tail), t)
    Ensure data_at(field_addr(p, tail), t)
*/;

struct list *reverse(struct list *p) 
/*@ With l
    Require repr(p, l)
    Ensure repr(__return, rev(l))
*/
{
   struct list *w;
   struct list *v;
   w = (void *)0;
   v = p;
   /*@ Inv exists l1, exists l2,
            p == p && l == app(rev(l1), l2) && 
            repr(w, l1) * repr(v, l2)
      */
   while (v) {
      /*@ exists l1, exists l2, exists l3, exists hv, exists tv, 
          p == p && l == app(rev(l1, l2)) && l2 == cons(hv, l3) &&
          repr(w, l1) * data_at(field_addr(v, head), hv) * data_at(field_addr(v, tail), tv) * repr(tv, l3)
      */
      struct list *t;
      t = v->tail;
      v->tail = w;
      w = v;
      v = t;
   }
   return w;
}