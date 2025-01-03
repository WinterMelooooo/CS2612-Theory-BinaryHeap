#include "../../GeneratedStrategy/verification_list.h"
#include "../../GeneratedStrategy/verification_stdlib.h"

struct Data_record;
struct siw_qp {
  struct Data_record *data;
  struct llist_node tx_list;
};

struct siw_qp *list_siw_entry(struct llist_node *llnode);
/*@ Require emp
    Ensure &(__return -> tx_list) == llnode
*/

void siw_sq_resume(struct siw_qp *qp);
/*@ 
*/


int siw_run_sq(struct llist_node *active)
/*@ With prev
    Require siw_llistrep(active)
    Ensure exists v, __return == v
*/
{
  if (active == NULL) {
    return 0;
  }
  struct siw_qp *qp;
  for (qp = list_siw_entry(active); qp->tx_list != NULL; qp = list_siw_entry(qp->tx_list.next)) {
    qp->tx_list.next = NULL;
		siw_sq_resume(qp);
  }
}