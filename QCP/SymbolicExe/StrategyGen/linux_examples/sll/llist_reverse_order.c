#include "../../GeneratedStrategy/verification_list.h"
#include "../../GeneratedStrategy/verification_stdlib.h"
#include "llist.h"

/* Copy From lib/llist.c */

/**
 * llist_reverse_order - reverse order of a llist chain
 * @head:	first item of the list to be reversed
 *
 * Reverse the order of a chain of llist entries and return the
 * new first entry.
 */
struct llist_node *llist_reverse_order(struct llist_node *head)
/*@ Require llistrep(head) 
    Ensure llistrep(__return) 
*/
{
	struct llist_node *new_head = (struct llist_node *) 0;
  /*@ Inv 
      llistrep(head) * llistrep(new_head)
  */
	while (head) {
		struct llist_node *tmp = head;
		head = head->next;
		tmp->next = new_head;
		new_head = tmp;
	}

	return new_head;
}