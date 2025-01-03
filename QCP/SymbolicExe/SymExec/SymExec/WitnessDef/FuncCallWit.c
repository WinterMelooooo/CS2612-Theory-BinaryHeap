#include "FuncCallWit.h"

struct FuncCallWit * FuncCallWitNil() {
   return NULL;
}

struct FuncCallWit * FuncCallWitCons(struct func_spec * spec, 
                                     struct ExprValList *param, struct ExprValList * args, struct ExprValList * with_vals, 
                                     struct Assertion * pre, struct Assertion * frame, 
                                     struct ExistList * post_exist_inst, struct FuncCallWit * next) {
   struct FuncCallWit * res = (struct FuncCallWit *) malloc(sizeof(struct FuncCallWit));
   res->spec = spec;
   res->args = args;
   res->with_vals = with_vals;
   res->pre = pre;
   res->frame = frame;
   res->param = param;
   res->post_exist_inst = post_exist_inst;
   res->next = next;
   return res;
}

struct FuncCallWit * FuncCallWitLink(struct FuncCallWit * wit1, struct FuncCallWit * wit2) {
   if (wit1 == NULL) return wit2;
   if (wit2 == NULL) return wit1;
   struct FuncCallWit * tmp = wit1;
   while (tmp->next != NULL) {
      tmp = tmp->next;
   }
   tmp->next = wit2;
   return wit1;
}

void FuncCallWitFree(struct FuncCallWit * wit) {
   if (wit == NULL) return;
   ExprValListFree(wit->args);
   ExprValListFree(wit->with_vals);
   AsrtFree(wit->pre);
   AsrtFree(wit->frame);
   FuncCallWitFree(wit->next);
   ExistListFree(wit->post_exist_inst);
   func_spec_free(wit->spec);
   free(wit);
}

struct AsrtList * FuncCallWitRecoverPostSingle(struct FuncCallWit * wit, struct environment * env) {
   struct Assertion * frame = wit->frame;
   struct func_spec * spec = wit->spec;
   struct AsrtList * res = AsrtListNil();
   for (struct AsrtList * i = spec->post; i != NULL; i = i->next) {
      struct Assertion * post = AsrtDeepCopy(i->head);
      post = AsrtMerge(post, AsrtDeepCopy(wit->frame));
      for (struct ExprValListNode * j = wit->param->head, *k = wit->args->head; j != NULL; j = j->next, k = k->next) {
         post = AsrtSubst(post, j->data, k->data);
      }
      for (struct ExistList * j = spec->with; j != NULL;) {
         for (struct ExprValListNode * k = wit->with_vals->head; j != NULL; j = j->next, k = k->next) {
            struct ExprVal * tmp = ExprVal_V_VARI(j->id);
            post = AsrtSubst(post, tmp, k->data);
            ExprValFree(tmp);
         }
      }
      for (struct ExistList *j = post->exist_list, *k = wit->post_exist_inst; j != NULL; j = j->next, k = k->next) {
         struct ExprVal * t1 = ExprVal_V_VARI(j->id);
         struct ExprVal * t2 = ExprVal_V_VARI(k->id);
         post = AsrtSubst(post, t1, t2);
         ExprValFree(t1);
         ExprValFree(t2);
      }
      res = AsrtListCons(post, res);
   }
   return res;
}

struct AsrtList * FuncCallWitRecoverPost(struct FuncCallWit * wit, struct environment * env) {
   if (wit == NULL) return AsrtListNil();
   return AsrtListLink(FuncCallWitRecoverPostSingle(wit, env), FuncCallWitRecoverPost(wit->next, env));
}