#include "../../GeneratedStrategy/verification_list.h"
#include "../../GeneratedStrategy/verification_stdlib.h"
/* Copy From arch/x86/kernel/cpu/mce/core.c */

/*@ Extern Coq (store_char_array : Z -> Assertion) */
/*@ Extern Coq (mce_llistrep : Z -> Assertion)*/
/*@ Extern Coq (mce_lseg : Z -> Z -> Assertion)*/

/*@ include strategies "mce.strategies"*/

struct llist_node {
	struct llist_node *next;
};

struct mce_evt_llist {
  char *msg;
  struct llist_node llnode;
};


/*
Let mce_llistrep(llnode : llist_node) := 
llnode == NULL && emp || exists l' mce , &(mce -> llnode) == llnode &&  store_char_array(mce -> msg) &&  llnode -> next == l' && mce_listrep(l')
*/

char *final;

struct mce_evt_llist *list_mce_evt_entry(struct llist_node *llnode)
/*@ Require emp
    Ensure &(__return -> llnode) == llnode 
*/
;

int strcmp(char *s1, char *s2)
/*@ Require store_char_array(s1) * store_char_array(s2)
    Ensure exists v, __return == v && store_char_array(s1) * store_char_array(s2)
*/
;

int mce_panic(struct llist_node *pending)
/*@ Require mce_llistrep(pending) * store_char_array(final)
    Ensure exists v, __return == v && mce_llistrep(pending) * store_char_array(final)
*/
{
  struct mce_evt_llist *l;
  /*@ Inv 
      mce_lseg(pending, &(l->llnode)) * mce_llistrep(&(l->llnode))
  */
  for (l = list_mce_evt_entry(pending); &l->llnode != 0; l = list_mce_evt_entry(l->llnode.next)) {
    if (strcmp(l->msg, final) == 0) {
      return 1;
    }
  }
  return 0;
}