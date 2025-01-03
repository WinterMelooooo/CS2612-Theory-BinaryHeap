#include <assert.h>
#include "AssDef.h"
#include "../Utility/InnerAsrtPrinter.h"

void* (*LocalDeepCopy)(void*);
void* (*LocalMerge)(void*, void*);
void* (*LocalSubst)(void*, struct ExprVal*, struct ExprVal*);
void* (*LocalSubstPolyType)(void*, struct PolyType*, struct PolyType*);
void  (*LocalFree)(void *);

struct AsrtList* AsrtListNil() { return NULL; }

struct AsrtList* AsrtListCons(struct Assertion * asrt, struct AsrtList * next) {
   struct AsrtList * ret = (struct AsrtList *) malloc(sizeof(struct AsrtList));
   ret->head = asrt;
   ret->next = next;
   return ret;
}

struct AsrtList* AsrtListLink(struct AsrtList *left, struct AsrtList *right) {
   if (left == NULL) return right;
   if (right == NULL) return left;
   struct AsrtList * tmp = left;
   while (tmp->next != NULL) {
      tmp = tmp->next;
   }
   tmp->next = right;
   return left;
}

struct AsrtList * AsrtListReverse(struct AsrtList * asrt_list) {
   struct AsrtList * ret = NULL;
   while (asrt_list != NULL) {
      struct AsrtList * tmp = asrt_list->next;
      asrt_list->next = ret;
      ret = asrt_list;
      asrt_list = tmp;
   }
   return ret;
}

struct Assertion * CreateAsrt() {
  struct Assertion * asrt = (struct Assertion*) malloc(sizeof(struct Assertion));
  asrt->prop_list = PropListNil();
  asrt->local_list = CreateLocalLinkedHashMap();
  asrt->sep_list = SepListNil();
  asrt->exist_list = ExistListNil();
  asrt->fp_spec_list = FPSpecListNil();
  return asrt;
}

struct AsrtLabeledGroup * CreateAsrtLabeledGroupf(char * label, struct AsrtList * asrt_list) {
   struct AsrtLabeledGroup * ret = (struct AsrtLabeledGroup *) malloc(sizeof(struct AsrtLabeledGroup));
   ret->label = label;
   ret->asrt_list = asrt_list;
   return ret;
}

struct AsrtLabeledGroupList * AsrtLabeledGroupListNil() {
   return NULL;
}

struct AsrtLabeledGroupList * AsrtLabeledGroupListCons(struct AsrtLabeledGroup * group, struct AsrtLabeledGroupList * next) {
   struct AsrtLabeledGroupList * ret = (struct AsrtLabeledGroupList *) malloc(sizeof(struct AsrtLabeledGroupList));
   ret->head = group;
   ret->next = next;
   return ret;
}

struct AsrtLabeledGroupList * AsrtLabeledGroupListLink(struct AsrtLabeledGroupList * left, struct AsrtLabeledGroupList * right) {
   if (left == NULL) return right;
   if (right == NULL) return left;
   struct AsrtLabeledGroupList * tmp = left;
   while (tmp->next != NULL) {
      tmp = tmp->next;
   }
   tmp->next = right;
   return left;
}

struct ExprVal * GetDataAtValue(struct Assertion * inner_asrt, struct ExprVal * expr) {
   struct SepList * sep_list = inner_asrt->sep_list;
   while (sep_list != NULL) {
      if (sep_list->head->t == T_DATA_AT) {
         if (ExprValCheckEqual(expr, sep_list->head->d.DATA_AT.left)) {
            return sep_list->head->d.DATA_AT.right;
         }
      }
      sep_list = sep_list->next;
   }
   return NULL;
}

// 0 if success, 1 if fail
int ReplaceDataAtValue(struct Assertion * inner_asrt, 
                                    struct ExprVal * lexpr, struct ExprVal * rexpr) {
   struct SepList * sep_list = inner_asrt->sep_list;
   while (sep_list != NULL) {
      if (sep_list->head->t == T_DATA_AT) {
         if (ExprValCheckEqual(lexpr, sep_list->head->d.DATA_AT.left)) {
            sep_list->head->d.DATA_AT.right = rexpr;
            return 0;
         }
      } else if (sep_list->head->t == T_UNDEF_DATA_AT) {
         if (ExprValCheckEqual(lexpr, sep_list->head->d.UNDEF_DATA_AT.left)) {
            sep_list->head->t = T_DATA_AT;
            sep_list->head->d.DATA_AT.left = lexpr;
            sep_list->head->d.DATA_AT.right = rexpr;
            return 0;
         }
      }
      sep_list = sep_list->next;
   }
   return 1;
}

struct Assertion * AsrtDeepCopy(struct Assertion * asrt) {
   struct Assertion * res = (struct Assertion *) malloc(sizeof(struct Assertion));
   res->prop_list = PropListDeepCopy(asrt->prop_list);
   res->local_list = LocalDeepCopy(asrt->local_list);
   res->sep_list = SepListDeepCopy(asrt->sep_list);
   res->exist_list = ExistListDeepCopy(asrt->exist_list);
   res->fp_spec_list = FPSpecListDeepCopy(asrt->fp_spec_list);
   return res;
}

struct AsrtList * AsrtListDeepCopy(struct AsrtList * asrt_list) {
   if (asrt_list == NULL) return NULL;
   return AsrtListCons(AsrtDeepCopy(asrt_list->head), AsrtListDeepCopy(asrt_list->next));
}

void AsrtFree(struct Assertion *asrt) {
   if (asrt == NULL) return;
#ifdef DEBUG_MEMORY
   printf("Free asrt : %p\n", asrt);
   PrintAsrtAllMemInfo(asrt);
#endif
   PropListFree(asrt->prop_list);
   LocalFree(asrt->local_list);
   SepListFree(asrt->sep_list);
   ExistListFree(asrt->exist_list);
   FPSpecListFree(asrt->fp_spec_list);
   free(asrt);
}

void AsrtListFree(struct AsrtList *asrt_list) {
   if (asrt_list == NULL) return;
   AsrtFree(asrt_list->head);
   AsrtListFree(asrt_list->next);
   free(asrt_list);
}

void AsrtLabeledGroupFree(struct AsrtLabeledGroup *asrt_group) {
   if (asrt_group == NULL) return;
   AsrtListFree(asrt_group->asrt_list);
   free(asrt_group);
}  

void AsrtLabeledGroupListFree(struct AsrtLabeledGroupList *asrt_group_list) {
   if (asrt_group_list == NULL) return;
   AsrtLabeledGroupFree(asrt_group_list->head);
   AsrtLabeledGroupListFree(asrt_group_list->next);
}

struct FuncRetType * FuncRetTypeNil() {
   return NULL;
}

struct FuncRetType * FuncRetTypeCons(struct Assertion * asrt, 
                                     struct ExprVal * val, struct FuncRetType * next) {
   struct FuncRetType * FuncRetType = malloc(sizeof(struct FuncRetType));
   FuncRetType->asrt = asrt;
   FuncRetType->val = val;
   FuncRetType->next = next;
   return FuncRetType;
}

struct FuncRetType * FuncRetTypeLink(struct FuncRetType * list1, struct FuncRetType * list2) {
   if (list1 == NULL) return list2;
   if (list2 == NULL) return list1;
   struct FuncRetType * tmp = list1;
   while (tmp->next != NULL) {
      tmp = tmp->next;
   }
   tmp->next = list2;
   return list1;
}

struct FuncRetType * FuncRetTypeDeepCopy(struct FuncRetType * ret) {
   if (ret == NULL) return NULL;
   return FuncRetTypeCons(AsrtDeepCopy(ret->asrt), ExprValDeepCopy(ret->val), FuncRetTypeDeepCopy(ret->next));
}

void FuncRetTypeFree(struct FuncRetType * ret) {
   if (ret == NULL) return;
   AsrtFree(ret->asrt);
   ExprValFree(ret->val);
   FuncRetTypeFree(ret->next);
   free(ret);
}

struct FuncRetTypeList * FuncRetTypeListNil() {
   return NULL;
}

struct FuncRetTypeList * FuncRetTypeListCons(struct FuncRetType * ret, struct StringList * scopes, struct FuncRetTypeList * next) {
   struct FuncRetTypeList * list = malloc(sizeof(struct FuncRetTypeList));
   list->head = ret;
   list->scopes = scopes;
   list->next = next;
   return list;
}

struct FuncRetTypeList * FuncRetTypeListLink(struct FuncRetTypeList * list1, struct FuncRetTypeList * list2) {
   if (list1 == NULL) return list2;
   if (list2 == NULL) return list1;
   struct FuncRetTypeList * tmp = list1;
   while (tmp->next != NULL) {
      tmp = tmp->next;
   }
   tmp->next = list2;
   return list1;
}

// substitute all pre into post
struct Assertion * AsrtSubst(struct Assertion * asrt, struct ExprVal * pre, struct ExprVal * post) {
   asrt->prop_list = PropListSubst(asrt->prop_list, pre, post);
   asrt->sep_list = SepListSubst(asrt->sep_list, pre, post);
   asrt->local_list = LocalSubst(asrt->local_list, pre, post);
   asrt->exist_list = ExistListSubst(asrt->exist_list, pre, post);
   return asrt;
}

struct Assertion * AsrtSubstPolyType(struct Assertion * asrt, struct PolyType * pre, struct PolyType * post, struct persistent_env * env) {
   asrt->local_list = LocalSubstPolyType(asrt->local_list, pre, post);
   asrt->prop_list = PropListSubstPolyType(asrt->prop_list, pre, post);
   asrt->sep_list = SepListSubstPolyType(asrt->sep_list, pre, post);
   asrt->exist_list = ExistListSubstPolyType(asrt->exist_list, pre, post, env);
   return asrt;
}

struct AsrtList * AsrtListSubst(struct AsrtList * asrt_list, struct ExprVal * pre, struct ExprVal * post) {
   for (struct AsrtList * iter = asrt_list; iter != NULL; iter = iter->next) {
      iter->head = AsrtSubst(iter->head, pre, post);
   }
   return asrt_list;
}

struct AsrtList * AsrtListSubstPolyType(struct AsrtList * asrt_list, struct PolyType * pre, struct PolyType * post, struct persistent_env * env) {
   for (struct AsrtList * iter = asrt_list; iter != NULL; iter = iter->next) {
      iter->head = AsrtSubstPolyType(iter->head, pre, post, env);
   }
   return asrt_list;
}

struct Assertion * AsrtMerge(struct Assertion * asrt1, struct Assertion * asrt2) {
   if (asrt1 == NULL) return asrt2;
   if (asrt2 == NULL) return asrt1;
   asrt1->exist_list = ExistListLink(asrt1->exist_list, asrt2->exist_list);
   asrt1->prop_list = PropListLink(asrt1->prop_list, asrt2->prop_list);
   asrt1->sep_list = SepListLink(asrt1->sep_list, asrt2->sep_list);
   asrt1->local_list = LocalMerge(asrt1->local_list, asrt2->local_list);
   asrt1->fp_spec_list = FPSpecListLink(asrt1->fp_spec_list, asrt2->fp_spec_list);
   free(asrt2);
   return asrt1;
}