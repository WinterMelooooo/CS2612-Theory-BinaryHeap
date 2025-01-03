#include "../../GeneratedStrategy/verification_list.h"
#include "../../GeneratedStrategy/verification_stdlib.h"
/* Copy From mm/memory-failure.c */

struct page;

struct raw_hwp_page {
	struct llist_node node;
	struct page *page;
};

struct folio {
       struct page page;
};

struct llist_head {
	struct llist_node *first;
};

/*
Let raw_hwp_llistrep(node : llist_node) := 
node == NULL && emp || exists l' raw_hwp page, &(raw_hwp -> node) == node && raw_hwp -> page == page &&  node -> next == l' && raw_hwp_listrep(l')
*/


struct folio * page_folio(struct page *page)
/*@ Require emp
	Ensure exists v, __return == v
*/
;

bool folio_test_hwpoison(struct folio *folio)
/*@ Require emp
	Ensure exists v, __return == v
*/
;

bool folio_test_hugetlb(struct folio *folio)
/*@ Require emp
	Ensure exists v, __return == v
*/
;

bool folio_test_hugetlb_raw_hwp_unreliable(struct folio *folio)
/*@ Require emp
	Ensure exists v, __return == v
*/
;

bool PageHWPoison(struct page *page)
/*@ Require emp
	Ensure exists v, __return == v
*/
;

static inline struct llist_head *raw_hwp_list_head(struct folio *folio)
/*@ Require emp
	Ensure exists v, __return == v
*/
;

struct raw_hwp_page *list_raw_entry(struct llist_node *node)
/*@ Require emp
    Ensure &(__return -> node) == node
*/
;

bool is_raw_hwpoison_page_in_hugepage(struct page *page)
/*@ With prev
    Require emp
    Ensure exists v, __return == v
 */
{
	struct llist_head *raw_hwp_head;
	struct raw_hwp_page *p;
	struct folio *folio = page_folio(page);
	bool ret = false;

	if (!folio_test_hwpoison(folio))
		return false;

	if (!folio_test_hugetlb(folio))
		return PageHWPoison(page);

	/*
	 * When RawHwpUnreliable is set, kernel lost track of which subpages
	 * are HWPOISON. So return as if ALL subpages are HWPOISONed.
	 */
	if (folio_test_hugetlb_raw_hwp_unreliable(folio))
		return true;

	raw_hwp_head = raw_hwp_list_head(folio);

	for (p = list_raw_entry(raw_hwp_head->first); p->node!=NULL; p = list_raw_entry(p->node.next)){
		if (page == p->page){
			ret = true;
			break;
		}
	}

	return ret;
}