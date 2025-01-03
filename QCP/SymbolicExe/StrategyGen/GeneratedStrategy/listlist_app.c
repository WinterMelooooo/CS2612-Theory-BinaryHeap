#include "verification_stdlib.h"
#include "verification_list.h"
#include "listlist_app.h"

struct list {
    int head_;
    struct list *tail_;
};

struct listlist {
    struct list *head;
    struct listlist *tail;
};

struct list * expand(struct listlist * x)
/*@ Require listlistrep(x)
    Ensure listrep(__return) * listlistrep(x)
*/
{
    struct listlist *t;
    struct list *v, *ans;
    t = x;
  	ans = (struct list * ) 0;
    /*@ Inv listlistrep(t) * listlseg(x, t) * listrep(ans) */
    while (t) {
      v = t->head;
      t = t->tail;
   }
   return ans;
}