struct llist_node {
	struct llist_node *next;
};
struct llist_head {
	struct llist_node *first;
};


/*@ Extern Coq (llistrep : Z -> Z -> Assertion)
               (llistseg : Z -> Z -> Z -> Assertion)
 */

/*@ Import Coq Require Import sll_shape_lib */

/*@ include strategies "llist.strategies" */

/* Let(struct llist_node) llistrep(x, l) = x == 0 && l == 0 && emp ||
      exists t, data_at(field_addr(l, next), t) * llistrep(t, l - 1)
 */
 
/* Let(struct llist_node) llistseg(x, y, l) = x == y && l == 0 && emp ||
      exists z, data_at(field_addr(x, next), z) * llistseg(z, y, l - 1)
 */
