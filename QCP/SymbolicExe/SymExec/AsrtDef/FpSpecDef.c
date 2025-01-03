#include "FpSpecDef.h"
#include "ExprValDef.h"
#include "../../compiler/lang.h"

struct FPSpec * CreateFPSepc(struct ExprVal * fp_addr, struct func_info * func_info) {
   struct FPSpec * res = (struct FPSpec *) malloc(sizeof(struct FPSpec));
   res->fp_addr = fp_addr;
   res->func_info = func_info;
   res->func_info = func_info;
   return res;
}

struct FPSpec * FPSpecDeepCopy(struct FPSpec * spec) {
   return CreateFPSepc(ExprValDeepCopy(spec->fp_addr), spec->func_info);
}

void FPSpecFree(struct FPSpec * spec) {
   ExprValFree(spec->fp_addr);
   free(spec);
}

struct FPSpecListNode* FPSpecListNodeDeepCopy(struct FPSpecListNode * node) {
   if (node == NULL) return NULL;
   struct FPSpecListNode * res = (struct FPSpecListNode *) malloc(sizeof(struct FPSpecListNode));
   res->data = FPSpecDeepCopy(node->data);
   res->next = FPSpecListNodeDeepCopy(node->next);
   return res;
}

void FPSpecListNodeFree(struct FPSpecListNode * node) {
   if (node == NULL) return;
   FPSpecFree(node->data);
   free(node);
}

DEFINE_LIST(FPSpecList, struct FPSpec*, data)

struct func_info * FPSpecListFind(struct ExprVal * fp_addr, struct FPSpecList * list) {
   struct FPSpecListNode * cur = list->head;
   while (cur != NULL) {
      if (ExprValCheckEqual(cur->data->fp_addr, fp_addr)) {
         return cur->data->func_info;
         return cur->data->func_info;
      }
      cur = cur->next;
   }
   return NULL;
}

struct FPSpec * FPSpecSubst(struct FPSpec * spec, struct ExprVal * pre, struct ExprVal * post) {
   spec->func_info->spec->pre = AsrtListSubst(spec->func_info->spec->pre, pre, post);
   spec->func_info->spec->post = AsrtListSubst(spec->func_info->spec->post, pre, post);
   return spec;
}

struct FPSpec * FPSpecSubstPolyType(struct FPSpec * spec, struct PolyType * pre, struct PolyType * post, struct persistent_env * env) {
   spec->func_info->spec->pre = AsrtListSubstPolyType(spec->func_info->spec->pre, pre, post, env);
   spec->func_info->spec->post = AsrtListSubstPolyType(spec->func_info->spec->post, pre, post, env);
   return spec;
}

struct FPSpecList * FPSpecListSubst(struct FPSpecList * list, struct ExprVal * pre, struct ExprVal * post) {
   struct FPSpecListNode * cur = list->head;
   while (cur != NULL) {
      cur->data = FPSpecSubst(cur->data, pre, post);
      cur = cur->next;
   }
   return list;
}

struct FPSpecList * FPSpecListSubstPolyType(struct FPSpecList * list, struct PolyType * pre, struct PolyType * post, struct persistent_env * env) {
   struct FPSpecListNode * cur = list->head;
   while (cur != NULL) {
      cur->data = FPSpecSubstPolyType(cur->data, pre, post, env);
      cur = cur->next;
   }
   return list;
}
