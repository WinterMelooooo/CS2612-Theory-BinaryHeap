#include "../../GeneratedStrategy/verification_list.h"
#include "../../GeneratedStrategy/verification_stdlib.h"
/* Copy From drivers/iommu/amd/iommu.c */

struct llist_node {
	struct llist_node *next;
};

struct llist_head {
	struct llist_node *first;
};

struct iommu_dev_data {
	u16 devid;
	struct llist_node dev_data_list;
};

struct amd_iommu_pci_seg {
	struct llist_head dev_data_list;
}

struct amd_iommu {
	struct amd_iommu_pci_seg *pci_seg;
}

/*
Let iommu_llistrep(dev_data_list : llist_node) := 
dev_data_list == NULL && emp || exists l' iommu v, &(iommu -> dev_data_list) == dev_data_list && iommu -> devid == v && dev_data_list -> next == l' && iommu_listrep(l')
*/

struct iommu_dev_data *list_iommu_dev_entry(struct llist_node *dev_data_list)
/*@ Require emp
    Ensure &(__return -> dev_data_list) == dev_data_list 
*/
;

static bool llist_empty(const struct llist_head *head)
/*@ Require emp
	Ensure exists v, __return == v
*/
;

static struct iommu_dev_data *search_dev_data(struct amd_iommu *iommu, u16 devid)
/*@ With prev
    Require iommu_llistrep(iommu->pci_seg->dev_data_list.first)
    Ensure exists v, __return == v
*/
{
	struct llist_node *node;
	struct amd_iommu_pci_seg *pci_seg = iommu->pci_seg;

	if (llist_empty(&pci_seg->dev_data_list))
		return NULL;

	node = pci_seg->dev_data_list.first;

	struct iommu_dev_data *dev_data;
	for (dev_data = list_iommu_dev_entry(node); dev_data->dev_data_list != NULL;
			dev_data = list_iommu_dev_entry(dev_data->dev_data_list.next)){
				if (dev_data->devid == devid)
					return dev_data;
			}

	/*llist_for_each_entry(dev_data, node, dev_data_list) {
		if (dev_data->devid == devid)
			return dev_data;
	}*/

	return NULL;
}