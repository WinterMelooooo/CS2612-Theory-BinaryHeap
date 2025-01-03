#include "../../GeneratedStrategy/verification_list.h"
#include "../../GeneratedStrategy/verification_stdlib.h"
/* Copy From kernel/irq_work.c */

struct Data_record;
struct irq_work {
    struct Data_record *data;
	struct __call_single_node node;
};

struct __call_single_node {
	struct llist_node	llist;
}

/*
Let irq_work_llistrep(llist : llist_node) := 
llist == NULL && emp || exists l' irq data, &(irq -> llnode.llist) == llist && irq -> data == data &&  llist -> next == l' && irq_work_listrep(l')
*/

static inline bool llist_empty(const struct llist_head *head)
/*@ Require emp
    Ensure exists v, __return == v
*/
;

struct llist_node * llist_del_all(struct llist_head *list)
/*@ Require emp
    Ensure exists v, __return == v
*/
;

void irq_work_single(struct irq_work *work)
/*@
*/
;

struct irq_work *list_irq_work_entry(struct llist_node *llnode)
/*@ Require emp
    Ensure &(__return -> node.llist) == llnode 
*/
;

static void irq_work_run_list(struct llist_head *list)
/*@ With Prev
    Require 
    Ensure
*/
{
	struct irq_work *work, *tmp;
	struct llist_node *llnode;

	/*
	 * On PREEMPT_RT IRQ-work which is not marked as HARD will be processed
	 * in a per-CPU thread in preemptible context. Only the items which are
	 * marked as IRQ_WORK_HARD_IRQ will be processed in hardirq context.
	 */

	if (llist_empty(list))
		return;

	llnode = llist_del_all(list);

    for (work = list_irq_work_entry(llnode); 
        work->node.llist != NULL && tmp = list_irq_work_entry((work->node.llist)->next);
        work = tmp)
        irq_work_single(work);
}