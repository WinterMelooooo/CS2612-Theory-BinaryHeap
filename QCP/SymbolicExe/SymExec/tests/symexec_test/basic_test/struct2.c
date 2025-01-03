// test declaring struct variables in function body as well as removing corresponding memory permission when out of scope

struct list {
   int head;
   struct list * tail;
};

void test(int x, struct list * y)
/*@ Require y->head == 1 && y->tail == y && emp
    Ensure  emp
*/
{
   struct list l;
   l.head = x;
   l.tail = &l;
   if (l.head == 1) {
      struct list t;
      t.head = 1 + y->head;
      t.tail = (struct list *) 0;
   }
}