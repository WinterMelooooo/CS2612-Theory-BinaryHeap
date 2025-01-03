#include "../../GeneratedStrategy/verification_list.h"
#include "../../GeneratedStrategy/verification_stdlib.h"
#include "llist.h"

/* Change From kernel/bpf/memalloc.c */


void free_one(struct llist_node *llnode, int percpu)
/*@ With v  
    Require llnode -> next == v 
    Ensure emp 
*/;

static unsigned int free_all(struct llist_node *llnode, int percpu)
/*@ Require llistrep(llnode) 
    Ensure exists v, __return == v
*/
{
	struct llist_node *pos, *t;
	unsigned int cnt = 0;
  /*@ Inv 
      exists v, cnt == v && llistrep(pos)
  */
	for (pos = llnode; pos ; (pos) = (t)) {
    t = pos->next;
    free_one(pos, percpu);
		cnt++;
	}
	return cnt;
}