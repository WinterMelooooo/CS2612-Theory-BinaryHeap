//@ Extern Coq (app : Z -> Z -> Z) (rev : Z -> Z) (cons : Z -> Z -> Z)
//@ Let listrep(l : Z, p : Z) = emp

struct list {
   int head;
   struct list *tail;
};

struct list *reverse(struct list *p) 
/*@ With l
    Require listrep(l, p)
    Ensure listrep(rev(l), __return)
*/
{
   struct list *w;
   struct list *v;
   w = (void *)0;
   v = p;
   /*@ Inv exists l1, exists l2, exists mp,
            p == mp && l == app(rev(l1), l2) &&
            listrep(l1, w) * listrep(l2, v)
      */
   while (v) {
      /*@ exists l1 , exists x, exists l2, exists (u : Z), exists mp,
          p == mp && app(rev(l1), cons(x, l2)) == l &&
         (v -> {list.head} == x) * (v -> {struct list.tail} == w) * listrep(l1,w) * listrep(l2,v) 
      */
      struct list *t;
      t = v->tail;
      v->tail = w;
      w = v;
      v = t;
   }
   return w;
}
