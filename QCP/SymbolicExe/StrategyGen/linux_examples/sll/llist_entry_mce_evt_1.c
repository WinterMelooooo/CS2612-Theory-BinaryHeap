#include "../../GeneratedStrategy/verification_list.h"
#include "../../GeneratedStrategy/verification_stdlib.h"
/* Copy From arch/x86/kernel/cpu/mce/genpool.c */

/*@ Extern Coq (mce_data : Z -> Assertion)*/
/*@ Extern Coq (mce_evt_lseg : Z -> Z -> Assertion)*/
/*@ Extern Coq (mce_evt_llistrep : Z -> Assertion)*/
/*@ Extern Coq (mce_evt_llistrep_no_data : Z -> Assertion)*/

/*@ include strategies "mce1.strategies" */

struct llist_node {
	struct llist_node *next;
};

struct mce {
  int something;
};

struct mce_evt_llist {
  struct mce data;
  struct llist_node llnode;
};

/*
Let mce_llistrep(llnode : llist_node) := 
	llnode == NULL && emp || exists l' mce_evt mce, &(mce_evt -> llnode) == llnode
	&& mce_data(&(mce_evt->mce)) &&  llnode -> next == l' && mce_evt_listrep(l')

Let mce_evt_llistrep(l : mce_evt_llist) := 
	&l->llnode == NULL && mce_data(&(l->mce)) || exists l' mce, l->llnode.next == &l'->llnode 
	&& mce_data(&(l->mce)) && mce_llistrep(l')
*/

struct mce_evt_llist *list_mce_evt_entry(struct llist_node *llnode)
/*@ Require emp
    Ensure &(__return -> llnode) == llnode 
*/
;

int mce_cmp(struct mce *a, struct mce *b)
/*@ Require mce_data(a) * mce_data(b)
    Ensure exists v, __return == v && mce_data(a) * mce_data(b)
*/
;

static int is_duplicate_mce_record(struct mce_evt_llist *t, struct mce_evt_llist *l)
/*@ Require mce_evt_llistrep(t) * mce_evt_llistrep(l)
    Ensure exists v, __return == v && mce_evt_llistrep(t) * mce_evt_llistrep(l)
*/
{
	struct mce_evt_llist *node;
	struct mce *m1, *m2;

	m1 = &t->data;
  /*@ Inv  
      mce_evt_lseg(l, node) * mce_evt_llistrep(node)
  */
	for (node = l; &node->llnode != 0; node = list_mce_evt_entry(node->llnode.next)){
		m2 = &node->data;

		if (mce_cmp(m1, m2) == 0)
			return 1;
	}
	return 0;
	/*
	llist_for_each_entry(node, &l->llnode, llnode) {
		m2 = &node->mce;

		if (!mce_cmp(m1, m2))
			return true;
	}
	return false;*/
}