struct LOS_DL_LIST {
  struct LOS_DL_LIST *pstPrev; /**< Current node's pointer to the previous node */
  struct LOS_DL_LIST *pstNext; /**< Current node's pointer to the next node */
};
typedef struct LOS_DL_LIST LOS_DL_LIST;

/*@ Extern Coq (DL_Node :: * => *) */
/*@ Extern Coq (DL_Node_data : {A} -> DL_Node A -> A)
               (DL_Node_ptr  : {A} -> DL_Node A -> Z)
               (MkDL_Node    : {A} -> A -> Z -> DL_Node A) */
/*@ Extern Coq (nil : {A} -> list A) (cons : {A} -> A -> list A -> list A) */

/*@ Let dll_seg({A}; storeA : Z -> A -> Assertion, x, px, y, py, l) =
      x == y && px == py && l == nil ||
      exists a l0 z,
        l == cons(a, l0) &&
        x == DL_Node_ptr(a) &&
        storeA(x, DL_Node_data(a)) &&
        x->pstPrev == px &&
        x->pstNext == z &&
        dll_seg(storeA, z, x, y, py, l0)
 */

/*@ Let store_dll({A}; storeA : Z -> A -> Assertion, x, l) =
      exists h pt, x->pstPrev == pt && x->pstNext == h && dll_seg(storeA, h, x, x, pt, l)
 */

void LOS_ListAdd(LOS_DL_LIST *list, LOS_DL_LIST *node)
/*@ With {A} (storeA : Z -> A -> Assertion) l a
    Require store_dll(storeA, list, l) &&
            exists _, node->pstPrev == _ &&
            exists _, node->pstNext == _ &&
            storeA(node, a)
    Ensure exists dn, 
             DL_Node_data(dn) == a &&
             DL_Node_ptr(dn) == node &&
             store_dll(storeA, list, cons(dn, l))
 */
{
    node->pstNext = list->pstNext;
    node->pstPrev = list;
    list->pstNext->pstPrev = node;
    list->pstNext = node;
}

