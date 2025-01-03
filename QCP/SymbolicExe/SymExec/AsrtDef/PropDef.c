#include <string.h>
#include "PropDef.h"

struct Proposition * PropTrue() {
   struct Proposition * res = (struct Proposition *) malloc(sizeof(struct Proposition));
   res->t = T_PROP_TRUE;
   return res;
}

struct Proposition * PropFalse() {
   struct Proposition * res = (struct Proposition *) malloc(sizeof(struct Proposition));
   res->t = T_PROP_FALSE;
   return res;
}

struct Proposition * PropUnary(enum PropUOP op, struct Proposition * prop) {
   struct Proposition * res = (struct Proposition *) malloc(sizeof(struct Proposition));
   res->t = T_PROP_UNARY;
   res->d.UNARY.op = op;
   res->d.UNARY.prop = prop;
   return res;
}

struct Proposition * PropBinary(enum PropBinOP op, struct Proposition * prop1, struct Proposition * prop2) {
   struct Proposition * res = (struct Proposition *) malloc(sizeof(struct Proposition));
   res->t = T_PROP_BINARY;
   res->d.BINARY.op = op;
   res->d.BINARY.prop1 = prop1;
   res->d.BINARY.prop2 = prop2;
   return res;
}

struct Proposition * PropPtr(enum PropPtrOP op, struct ExprVal * expr) {
   struct Proposition * res = (struct Proposition *) malloc(sizeof(struct Proposition));
   res->t = T_PROP_PTR;
   res->d.PTR.op = op;
   res->d.PTR.expr = expr;
   return res;
}

struct Proposition * PropCompare(enum PropCompOp op, struct ExprVal * expr1, struct ExprVal * expr2) {
   struct Proposition * res = (struct Proposition *) malloc(sizeof(struct Proposition));
   res->t = T_PROP_COMPARE;
   res->d.COMPARE.op = op;
   res->d.COMPARE.expr1 = expr1;
   res->d.COMPARE.expr2 = expr2;
   return res;
}

struct Proposition * PropQuantifier(enum PropQuantifier op, int ident, struct Proposition * prop) {
   struct Proposition * res = (struct Proposition *) malloc(sizeof(struct Proposition));
   res->t = T_PROP_QUANTIFIER;
   res->d.QUANTIFIER.op = op;
   res->d.QUANTIFIER.ident = ident;
   res->d.QUANTIFIER.prop = prop;
   return res;
}

struct Proposition * PropOther(int predicate, struct PolyTypeList *types, struct ExprValList * args){
   struct Proposition * res = (struct Proposition *) malloc(sizeof(struct Proposition));
   res->t = T_PROP_OTHER;
   res->d.OTHER.predicate = predicate;
   res->d.OTHER.types = types;
   res->d.OTHER.args = args;
   return res;
}

struct PropList* PropListNil() { return NULL; }

struct PropList* PropListCons(struct Proposition * prop, struct PropList * next) {
   struct PropList * ret = (struct PropList *) malloc(sizeof(struct PropList));
   ret->head = prop;
   ret->next = next;
  return ret;
}

struct PropList* PropListLink(struct PropList * list1, struct PropList * list2) {
   if (list1 == NULL) return list2;
   if (list2 == NULL) return list1;
   struct PropList * tmp = list1;
   while (tmp->next != NULL) {
      tmp = tmp->next;
   }
   tmp->next = list2;
   return list1;
}

struct PropList* PropListRemove(struct PropList * pos, struct PropList * list) {
   if (list == NULL) return NULL;
   if (list == pos) return list->next;
   list->next = PropListRemove(pos, list->next);
   return list;
}

int PropositionCheckEqual(struct Proposition * prop1, struct Proposition * prop2) {
   if (prop1 == NULL && prop2 == NULL) return 1;
   if (prop1 == NULL || prop2 == NULL) return 0;
   if (prop1->t != prop2->t) return 0;
   switch (prop1->t) {
   case T_PROP_TRUE:
      return 1;
      break;
   case T_PROP_FALSE:
      return 1;
      break;
   case T_PROP_UNARY:
      if (prop1->d.UNARY.op != prop2->d.UNARY.op) return 0;
      else return PropositionCheckEqual(prop1->d.UNARY.prop, prop2->d.UNARY.prop);
      break;
   case T_PROP_BINARY:
      if (prop1->d.BINARY.op != prop2->d.BINARY.op) return 0;
      else return PropositionCheckEqual(prop1->d.BINARY.prop1, prop2->d.BINARY.prop1) &&
                  PropositionCheckEqual(prop1->d.BINARY.prop2, prop2->d.BINARY.prop2);
      break;
   case T_PROP_PTR:
      if (prop1->d.PTR.op != prop2->d.PTR.op) return 0;
      else return ExprValCheckEqual(prop1->d.PTR.expr, prop2->d.PTR.expr);
      break;
   case T_PROP_COMPARE:
      if (prop1->d.COMPARE.op != prop2->d.COMPARE.op) return 0;
      else return ExprValCheckEqual(prop1->d.COMPARE.expr1, prop2->d.COMPARE.expr1) &&
                  ExprValCheckEqual(prop1->d.COMPARE.expr2, prop2->d.COMPARE.expr2);
      break;
   case T_PROP_QUANTIFIER:
      if (prop1->d.QUANTIFIER.op != prop2->d.QUANTIFIER.op) return 0;
      else return prop1->d.QUANTIFIER.ident == prop2->d.QUANTIFIER.ident &&
                  PropositionCheckEqual(prop1->d.QUANTIFIER.prop, prop2->d.QUANTIFIER.prop);
      break;
   case T_PROP_OTHER:
      if (prop1->d.OTHER.predicate != prop2->d.OTHER.predicate) return 0;
      else return ExprValListCheckEqual(prop1->d.OTHER.args, prop2->d.OTHER.args);
      break;
   default:
      break;
   }
   return 0;
}

int PropListCheckEqual(struct PropList * list1, struct PropList * list2) {
   if (list1 == list2) return 1;
   if (list1 == NULL || list2 == NULL) return 0;
   if (PropositionCheckEqual(list1->head, list2->head)) {
      return PropListCheckEqual(list1->next, list2->next);
   } else {
      return 0;
   }
}

struct Proposition * PropDeepCopy(struct Proposition * prop) {
   if (prop == NULL) return NULL;
   struct Proposition * res = (struct Proposition *) malloc(sizeof(struct Proposition));
   res->t = prop->t;
   switch (prop->t) {
      case T_PROP_TRUE:
         break;
      case T_PROP_FALSE:
         break;
      case T_PROP_UNARY:
         res->d.UNARY.op = prop->d.UNARY.op;
         res->d.UNARY.prop = PropDeepCopy(prop->d.UNARY.prop);
         break;
      case T_PROP_BINARY:
         res->d.BINARY.op = prop->d.BINARY.op;
         res->d.BINARY.prop1 = PropDeepCopy(prop->d.BINARY.prop1);
         res->d.BINARY.prop2 = PropDeepCopy(prop->d.BINARY.prop2);
         break;
      case T_PROP_PTR:
         res->d.PTR.op = prop->d.PTR.op;
         res->d.PTR.expr = ExprValDeepCopy(prop->d.PTR.expr);
         break;
      case T_PROP_COMPARE:
         res->d.COMPARE.op = prop->d.COMPARE.op;
         res->d.COMPARE.expr1 = ExprValDeepCopy(prop->d.COMPARE.expr1);
         res->d.COMPARE.expr2 = ExprValDeepCopy(prop->d.COMPARE.expr2);
         break;
      case T_PROP_QUANTIFIER:
         res->d.QUANTIFIER.op = prop->d.QUANTIFIER.op;
         res->d.QUANTIFIER.ident = prop->d.QUANTIFIER.ident;
         res->d.QUANTIFIER.prop = PropDeepCopy(prop->d.QUANTIFIER.prop);
         break;
      case T_PROP_OTHER:
         res->d.OTHER.predicate = prop->d.OTHER.predicate;
         res->d.OTHER.types = PolyTypeListDeepCopy(prop->d.OTHER.types);
         res->d.OTHER.args = ExprValListDeepCopy(prop->d.OTHER.args);
         break;
      default:
         fprintf(stderr, "Error: unknown proposition type %d\n", prop->t);
         exit(1);
   }
   return res;
}

struct Proposition * PropSubst(struct Proposition * prop, struct ExprVal * pre, struct ExprVal * post) {
   if (prop == NULL) return NULL;
   switch (prop->t) {
      case T_PROP_TRUE:
         break;
      case T_PROP_FALSE:
         break;
      case T_PROP_UNARY:
         prop->d.UNARY.prop = PropSubst(prop->d.UNARY.prop, pre, post);
         break;
      case T_PROP_BINARY:
         prop->d.BINARY.prop1 = PropSubst(prop->d.BINARY.prop1, pre, post);
         prop->d.BINARY.prop2 = PropSubst(prop->d.BINARY.prop2, pre, post);
         break;
      case T_PROP_PTR:
         prop->d.PTR.expr = ExprValSubst(prop->d.PTR.expr, pre, post);
         break;
      case T_PROP_COMPARE:
         prop->d.COMPARE.expr1 = ExprValSubst(prop->d.COMPARE.expr1, pre, post);
         prop->d.COMPARE.expr2 = ExprValSubst(prop->d.COMPARE.expr2, pre, post);
         break;
      case T_PROP_QUANTIFIER:
         if (pre->t == FUNCAPP && prop->d.QUANTIFIER.ident == pre->d.FUNCAPP.id) {
            if (post->t != FUNCAPP) {
               fprintf(stderr, "Error: forall variable %d cannot be substituted by non-variable\n", prop->d.QUANTIFIER.ident);
               exit(1);
            } else {
               prop->d.QUANTIFIER.ident = post->d.FUNCAPP.id;
            }
         }
         prop->d.QUANTIFIER.prop = PropSubst(prop->d.QUANTIFIER.prop, pre, post);
         break;
      case T_PROP_OTHER: {
         if (pre->t == FUNCAPP && pre->d.FUNCAPP.id == prop->d.OTHER.predicate && ExprValListIsEmpty(pre->d.FUNCAPP.args) && PolyTypeListIsEmpty(prop->d.OTHER.types)) {
            prop->d.OTHER.predicate = post->d.FUNCAPP.id;
         }
         prop->d.OTHER.args = ExprValListSubst(prop->d.OTHER.args, pre, post);
         break;
      }
      default:
         fprintf(stderr, "Error: unknown proposition type %d\n", prop->t);
         exit(1);   
   }
   return prop;
}

struct Proposition * PropSubstPolyType(struct Proposition * prop, struct PolyType * pre, struct PolyType * post) {
   if (prop == NULL) return NULL;
   switch (prop->t) {
      case T_PROP_TRUE:
         break;
      case T_PROP_FALSE:
         break;
      case T_PROP_UNARY:
         prop->d.UNARY.prop = PropSubstPolyType(prop->d.UNARY.prop, pre, post);
         break;
      case T_PROP_BINARY:
         prop->d.BINARY.prop1 = PropSubstPolyType(prop->d.BINARY.prop1, pre, post);
         prop->d.BINARY.prop2 = PropSubstPolyType(prop->d.BINARY.prop2, pre, post);
         break;
      case T_PROP_PTR:
         prop->d.PTR.expr = ExprValSubstPolyType(prop->d.PTR.expr, pre, post);
         break;
      case T_PROP_COMPARE:
         prop->d.COMPARE.expr1 = ExprValSubstPolyType(prop->d.COMPARE.expr1, pre, post);
         prop->d.COMPARE.expr2 = ExprValSubstPolyType(prop->d.COMPARE.expr2, pre, post);
         break;
      case T_PROP_QUANTIFIER:
         prop->d.QUANTIFIER.prop = PropSubstPolyType(prop->d.QUANTIFIER.prop, pre, post);
         break;
      case T_PROP_OTHER:
         prop->d.OTHER.types = PolyTypeListSubst(prop->d.OTHER.types, pre, post);
         prop->d.OTHER.args = ExprValListSubstPolyType(prop->d.OTHER.args, pre, post);
         break;
      default:
         fprintf(stderr, "Error: unknown proposition type %d\n", prop->t);
         exit(1);   
   }
   return prop;
}

struct PropList * PropListSubst(struct PropList * prop_list, struct ExprVal * pre, struct ExprVal * post) {
   for (struct PropList * iter = prop_list; iter != NULL; iter = iter->next) {
      iter->head = PropSubst(iter->head, pre, post);
   }
   return prop_list;
}

struct PropList * PropListSubstPolyType(struct PropList * prop_list, struct PolyType * pre, struct PolyType * post) {
   for (struct PropList * iter = prop_list; iter != NULL; iter = iter->next) {
      iter->head = PropSubstPolyType(iter->head, pre, post);
   }
   return prop_list;
}

int Used_ExprVal_in_Prop(struct Proposition * prop, struct ExprVal * goal) {
   if (prop == NULL) return 0;
   switch (prop->t) {
      case T_PROP_TRUE:
         break;
      case T_PROP_FALSE:
         break;
      case T_PROP_UNARY:
         return Used_ExprVal_in_Prop(prop->d.UNARY.prop, goal);
      case T_PROP_BINARY:
         return Used_ExprVal_in_Prop(prop->d.BINARY.prop1, goal) || Used_ExprVal_in_Prop(prop->d.BINARY.prop2,goal);
      case T_PROP_PTR:
         return Used_ExprVal(prop->d.PTR.expr, goal);
      case T_PROP_COMPARE:
        return Used_ExprVal(prop->d.COMPARE.expr1,goal) || Used_ExprVal(prop->d.COMPARE.expr2,goal);
      default:
         break;
   }
   return 0;
}

struct PropList * PropListDeepCopy(struct PropList * prop_list) {
   if (prop_list == NULL) return NULL;
   return PropListCons(PropDeepCopy(prop_list->head), PropListDeepCopy(prop_list->next));
}

void PropFree(struct Proposition * prop) {
   if (prop == NULL) return;
#ifdef DEBUG_MEMORY
   printf("Free prop : %p\n", prop);
#endif
   switch (prop->t) {
      case T_PROP_TRUE:
         break;
      case T_PROP_FALSE:
         break;
      case T_PROP_UNARY:
         PropFree(prop->d.UNARY.prop);
         break;
      case T_PROP_BINARY:
         PropFree(prop->d.BINARY.prop1);
         PropFree(prop->d.BINARY.prop2);
         break;
      case T_PROP_PTR:
         ExprValFree(prop->d.PTR.expr);
         break;
      case T_PROP_COMPARE:
         ExprValFree(prop->d.COMPARE.expr1);
         ExprValFree(prop->d.COMPARE.expr2);
         break;
      case T_PROP_QUANTIFIER:
         PropFree(prop->d.QUANTIFIER.prop);
         break;
      case T_PROP_OTHER:
         PolyTypeListFree(prop->d.OTHER.types);
         ExprValListFree(prop->d.OTHER.args);
         break;
      default:
         fprintf(stderr, "Error: unknown proposition type %d\n", prop->t);
         exit(1);
   }
   free(prop);
}

void PropListFree(struct PropList * prop_list) {
   if (prop_list == NULL) return;
   PropFree(prop_list->head);
   PropListFree(prop_list->next);
   free(prop_list);
}
