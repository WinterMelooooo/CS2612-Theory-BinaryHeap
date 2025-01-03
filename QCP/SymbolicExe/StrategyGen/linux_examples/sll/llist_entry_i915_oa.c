#include "../../GeneratedStrategy/verification_list.h"
#include "../../GeneratedStrategy/verification_stdlib.h"
/* Copy From drivers/gpu/drm/i915/i915_perf.c */

struct i915_vma;

struct i915_oa_config_bo {
	struct llist_node node;

	struct i915_oa_config *oa_config;
	struct i915_vma *vma;
};

struct i915_perf_stream{
	struct llist_head oa_config_bos;
};

#define	UUID_STRING_LEN		36

struct i915_oa_config {
	char uuid[UUID_STRING_LEN + 1];
};

/*
Let i915_llistrep(node : llist_node) := 
node == NULL && emp || exists l' i915 oa_config vma, &(i915 -> node) == node && i915 -> oa_config == oa_config &&
 i915 -> vma == vma && node -> next == l' && i915_listrep(l')
*/

struct i915_oa_config_bo *list_i915_oa_entry(struct llist_node *llnode)
/*@ Require emp
    Ensure &(__return -> node) == node 
*/
;

int memcmp(const void *cs, const void *ct, size_t count)
/*@ Require emp
    Ensure exists v, __return == v
*/
;

static struct i915_vma * i915_vma_get(struct i915_vma *vma)
/*@ Require emp
    Ensure __return == vma
*/
;

static struct i915_vma *
get_oa_vma(struct i915_perf_stream *stream, struct i915_oa_config *oa_config)
/*@ With prev
    Require i915_llistrep(stream->oa_config_bos.first)
    Ensure exists v, __return == v
*/
{
	struct i915_oa_config_bo *oa_bo;

	/*
	 * Look for the buffer in the already allocated BOs attached
	 * to the stream.
	 */

	for (oa_bo = list_i915_oa_entry(stream->oa_config_bos.first); oa_bo->node != NULL; oa_bo=list_i915_oa_entry(oa_bo->node.next)){
		if (oa_bo->oa_config == oa_config && 
			memcmp(oa_bo->oa_config->uuid, oa_config->uuid, sizeof(oa_config->uuid)) == 0)
			return i915_vma_get(oa_bo->vma);
	}

	// llist_for_each_entry(oa_bo, stream->oa_config_bos.first, node) {
	// 	if (oa_bo->oa_config == oa_config &&
	// 	    memcmp(oa_bo->oa_config->uuid,
	// 		   oa_config->uuid,
	// 		   sizeof(oa_config->uuid)) == 0)
	// 		goto out;
	// }

	return i915_vma_get(oa_bo->vma);
}