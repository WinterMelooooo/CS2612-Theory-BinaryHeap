#include <stdio.h>
#include <stdlib.h>
#include "string.h"
#include "ExprValDef.h"
#include "../../compiler/lang.h"

struct ExprVal * ExprVal_EZ_VAL(unsigned long long number) {
   struct ExprVal * res = (struct ExprVal *) malloc(sizeof(struct ExprVal));
   res->t = EZ_VAL;
   res->d.EZ_VAL.number = number;
   return res;
}

struct ExprVal * ExprVal_V_VARI(int ident) {
   return ExprVal_FUNCAPP(ident, PolyTypeListNil(), ExprValListNil());
}

struct ExprVal * ExprVal_SIZE_OF(struct SimpleCtype * type) {
   struct ExprVal * res = (struct ExprVal *) malloc(sizeof(struct ExprVal));
   res->t = SIZE_OF;
   res->d.SIZE_OF.type = type;
   return res;
}

struct ExprVal * ExprVal_VFIELD_ADDRESS(struct ExprVal * expr, int field_id) {
   struct ExprVal * res = (struct ExprVal *) malloc(sizeof(struct ExprVal));
   res->t = VFIELD_ADDRESS;
   res->d.VFIELD_ADDRESS.expr = expr;
   res->d.VFIELD_ADDRESS.field_id = field_id;
   return res;
}

struct ExprVal * ExprVal_VUOP(enum InnerUnaryOperation op, struct ExprVal * expr) {
   struct ExprVal * res = (struct ExprVal *) malloc(sizeof(struct ExprVal));
   res->t = VUOP;
   res->d.VUOP.op = op;
   res->d.VUOP.expr = expr;
   return res;
}

struct ExprVal * ExprVal_VBOP(enum InnerBinaryOperation op, struct ExprVal * expr1, struct ExprVal * expr2) {
   struct ExprVal * res = (struct ExprVal *) malloc(sizeof(struct ExprVal));
   res->t = VBOP;
   res->d.VBOP.op = op;
   res->d.VBOP.expr1 = expr1;
   res->d.VBOP.expr2 = expr2;
   return res;
}

struct ExprVal * ExprVal_FUNCAPP(int id, struct PolyTypeList * types, struct ExprValList * args) {
   struct ExprVal * res = (struct ExprVal *) malloc(sizeof(struct ExprVal));
   res->t = FUNCAPP;
   res->d.FUNCAPP.id = id;
   res->d.FUNCAPP.types = types;
   res->d.FUNCAPP.args = args;
   return res;
}

struct ExprVal * ExprVal_LINDEX(struct ExprVal *list, struct ExprVal *index) {
   struct ExprVal * res = (struct ExprVal *) malloc(sizeof(struct ExprVal));
   res->t = LINDEX;
   res->d.LINDEX.list = list;
   res->d.LINDEX.index = index;
   return res;
}

struct ExprVal * ExprVal_TIME_COST() {
   struct ExprVal * res = (struct ExprVal *) malloc(sizeof(struct ExprVal));
   res->t = TIME_COST;
   return res;
}

int IsBitwiseOperator(enum InnerBinaryOperation op) {
   return op == Oand || op == Oor || op == Oxor || op == Oshl || op == Oshr;
}

int ExprValCheckEqual(struct ExprVal * expr1, struct ExprVal * expr2) {
  if (expr1 == expr2) return 1;
  if (expr1 == NULL || expr2 == NULL) return 0;
  if (expr1->t != expr2->t) return 0;
  switch (expr1->t) {
    case TIME_COST:
      return 1;
    case EZ_VAL:
      return expr1->d.EZ_VAL.number == expr2->d.EZ_VAL.number;
    case SIZE_OF:
      return SimpleCtypeCheckEqual(expr1->d.SIZE_OF.type, expr2->d.SIZE_OF.type);
    case VFIELD_ADDRESS:
      return ExprValCheckEqual(expr1->d.VFIELD_ADDRESS.expr, expr2->d.VFIELD_ADDRESS.expr) &&
             expr1->d.VFIELD_ADDRESS.field_id == expr2->d.VFIELD_ADDRESS.field_id;
    case VUOP:
      return expr1->d.VUOP.op == expr2->d.VUOP.op &&
             ExprValCheckEqual(expr1->d.VUOP.expr, expr2->d.VUOP.expr);
    case VBOP:
      return expr1->d.VBOP.op == expr2->d.VBOP.op &&
             ExprValCheckEqual(expr1->d.VBOP.expr1, expr2->d.VBOP.expr1) &&
             ExprValCheckEqual(expr1->d.VBOP.expr2, expr2->d.VBOP.expr2);
    case FUNCAPP: {
      if (expr1->d.FUNCAPP.id != expr2->d.FUNCAPP.id) return 0;
      return ExprValListCheckEqual(expr1->d.FUNCAPP.args, expr2->d.FUNCAPP.args) &&
             PolyTypeListCheckEqual(expr1->d.FUNCAPP.types, expr2->d.FUNCAPP.types);
    }
    case LINDEX:
       return ExprValCheckEqual(expr1->d.LINDEX.list, expr2->d.LINDEX.list) &&
              ExprValCheckEqual(expr1->d.LINDEX.index, expr2->d.LINDEX.index);
  }
  return 0;
}

struct ExprVal * ExprValDeepCopy(struct ExprVal * val) {
   if (val == NULL) return NULL;
   struct ExprVal * res = (struct ExprVal *) malloc(sizeof(struct ExprVal));
   res->t = val->t;
   switch (val->t) {
      case TIME_COST:
         break;
      case EZ_VAL:
         res->d.EZ_VAL.number = val->d.EZ_VAL.number;
         break;
      case SIZE_OF:
         res->d.SIZE_OF.type = SimpleCtypeDeepCopy(val->d.SIZE_OF.type);
         break;
      case VFIELD_ADDRESS:
         res->d.VFIELD_ADDRESS.expr = ExprValDeepCopy(val->d.VFIELD_ADDRESS.expr);
         res->d.VFIELD_ADDRESS.field_id = val->d.VFIELD_ADDRESS.field_id;
         break;
      case VUOP:
         res->d.VUOP.op = val->d.VUOP.op;
         res->d.VUOP.expr = ExprValDeepCopy(val->d.VUOP.expr);
         break;
      case VBOP:
         res->d.VBOP.op = val->d.VBOP.op;
         res->d.VBOP.expr1 = ExprValDeepCopy(val->d.VBOP.expr1);
         res->d.VBOP.expr2 = ExprValDeepCopy(val->d.VBOP.expr2);
         break;
      case FUNCAPP:
         res->d.FUNCAPP.id = val->d.FUNCAPP.id;
         res->d.FUNCAPP.types = PolyTypeListDeepCopy(val->d.FUNCAPP.types);
         res->d.FUNCAPP.args = ExprValListDeepCopy(val->d.FUNCAPP.args);
         break;
      case LINDEX:
         res->d.LINDEX.list = ExprValDeepCopy(val->d.LINDEX.list);
         res->d.LINDEX.index = ExprValDeepCopy(val->d.LINDEX.index);
         break;
   }
   return res;
}

DEFINE_LIST(ExprValList, struct ExprVal*, data)

struct ExprValListNode* ExprValListNodeDeepCopy(struct ExprValListNode * node) {
  if (node == NULL) return NULL;
  struct ExprValListNode * res = (struct ExprValListNode *) malloc(sizeof(struct ExprValListNode));
  res->data = ExprValDeepCopy(node->data);
  res->next = NULL;
  return res;
}

void ExprValListNodeFree(struct ExprValListNode * node) {
  if (node == NULL) return;
  ExprValFree(node->data);
  free(node);
}

struct ExprVal * ExprValSubst(struct ExprVal * expr, struct ExprVal * pre, struct ExprVal * post) {
   if (expr == NULL) return NULL;
   if (ExprValCheckEqual(expr, pre)) {
      ExprValFree(expr);
      return ExprValDeepCopy(post);
   }
   switch (expr->t) {
      case TIME_COST:
      case EZ_VAL:
      case SIZE_OF:
         break;
      case VFIELD_ADDRESS:
         expr->d.VFIELD_ADDRESS.expr = ExprValSubst(expr->d.VFIELD_ADDRESS.expr, pre, post);
         break;
      case VUOP:
         expr->d.VUOP.expr = ExprValSubst(expr->d.VUOP.expr, pre, post);
         break;
      case VBOP:
         expr->d.VBOP.expr1 = ExprValSubst(expr->d.VBOP.expr1, pre, post);
         expr->d.VBOP.expr2 = ExprValSubst(expr->d.VBOP.expr2, pre, post);
         break;
      case FUNCAPP:
         if (pre->t == FUNCAPP && post->t == FUNCAPP && expr->d.FUNCAPP.id == pre->d.FUNCAPP.id) {
            expr->d.FUNCAPP.id = post->d.FUNCAPP.id;
            expr->d.FUNCAPP.args = ExprValListLink(ExprValListDeepCopy(post->d.FUNCAPP.args), ExprValListSubst(expr->d.FUNCAPP.args, pre, post));
         }
         else expr->d.FUNCAPP.args = ExprValListSubst(expr->d.FUNCAPP.args, pre, post);
         break;
      case LINDEX:
         expr->d.LINDEX.list = ExprValSubst(expr->d.LINDEX.list, pre, post);
         expr->d.LINDEX.index = ExprValSubst(expr->d.LINDEX.index, pre, post);
   }
   return expr;
}

int Used_ExprVal(struct ExprVal * expr, struct ExprVal * goal) {
   if (expr == NULL) return 0;
   if (ExprValCheckEqual(expr, goal)) return 1;
   switch (expr->t) {
      case TIME_COST:
      case EZ_VAL:
         break;
      case VFIELD_ADDRESS:
         return Used_ExprVal(expr->d.VFIELD_ADDRESS.expr, goal);
      case VUOP:
         return Used_ExprVal(expr->d.VUOP.expr,goal);
      case VBOP:
         return Used_ExprVal(expr->d.VBOP.expr1,goal) || Used_ExprVal(expr->d.VBOP.expr2,goal);
      case FUNCAPP:
         return Used_ExprValList(expr->d.FUNCAPP.args->head, goal);
      case LINDEX:
         return Used_ExprVal(expr->d.LINDEX.list,goal) || Used_ExprVal(expr->d.LINDEX.index,goal);
   }
   return 0;
}

struct ExprValList * ExprValListSubst(struct ExprValList * list, struct ExprVal * pre, struct ExprVal * post) {
   struct ExprValListNode * iter;
   for (iter = list->head; iter != NULL; iter = iter->next) {
      iter->data = ExprValSubst(iter->data, pre, post);
   }
   return list;
}

struct ExprVal * ExprValSubstPolyType(struct ExprVal * expr, struct PolyType * pre, struct PolyType * post) {
   if (expr == NULL) return NULL;
   switch (expr->t) {
      case TIME_COST:
      case EZ_VAL:
      case SIZE_OF:
         break;
      case VFIELD_ADDRESS:
         expr->d.VFIELD_ADDRESS.expr = ExprValSubstPolyType(expr->d.VFIELD_ADDRESS.expr, pre, post);
         break;
      case VUOP:
         expr->d.VUOP.expr = ExprValSubstPolyType(expr->d.VUOP.expr, pre, post);
         break;
      case VBOP:
         expr->d.VBOP.expr1 = ExprValSubstPolyType(expr->d.VBOP.expr1, pre, post);
         expr->d.VBOP.expr2 = ExprValSubstPolyType(expr->d.VBOP.expr2, pre, post);
         break;
      case FUNCAPP:
         expr->d.FUNCAPP.types = PolyTypeListSubst(expr->d.FUNCAPP.types, pre, post);
         expr->d.FUNCAPP.args = ExprValListSubstPolyType(expr->d.FUNCAPP.args, pre, post);
         break;
      case LINDEX:
         expr->d.LINDEX.list = ExprValSubstPolyType(expr->d.LINDEX.list, pre, post);
         expr->d.LINDEX.index = ExprValSubstPolyType(expr->d.LINDEX.index, pre, post);
         break;
   }
   return expr;
}

struct ExprValList * ExprValListSubstPolyType(struct ExprValList * list, struct PolyType * pre, struct PolyType * post) {
   struct ExprValListNode * iter;
   for (iter = list->head; iter != NULL; iter = iter->next) {
      iter->data = ExprValSubstPolyType(iter->data, pre, post);
   }
   return list;
}


int Used_ExprValList(struct ExprValListNode * list, struct ExprVal * goal) {
   if (list == NULL) return 0;
   return Used_ExprVal(list->data, goal) || Used_ExprValList(list->next, goal);
}

int ExprValListCheckEqual(struct ExprValList * list1, struct ExprValList * list2) {
   if (list1 == list2) return 1;
   if (list1 == NULL || list2 == NULL) return 0;
   struct ExprValListNode * l1 = list1->head, * l2 = list2->head;
   while (l1 != NULL && l2 != NULL) {
      if (!ExprValCheckEqual(l1->data, l2->data)) return 0;
      l1 = l1->next;
      l2 = l2->next;
   }
   return l1 == NULL && l2 == NULL;
}

void ExprValFree(struct ExprVal *val) {
   if (val == NULL) return;
   switch (val->t) {
      case TIME_COST:
      case EZ_VAL:
         break;
      case SIZE_OF:
         SimpleCtypeFree(val->d.SIZE_OF.type);
         break;
      case VFIELD_ADDRESS:
         ExprValFree(val->d.VFIELD_ADDRESS.expr);
         break;
      case VUOP:
         ExprValFree(val->d.VUOP.expr);
         break;
      case VBOP:
         ExprValFree(val->d.VBOP.expr1);
         ExprValFree(val->d.VBOP.expr2);
         break;
      case FUNCAPP:
         PolyTypeListFree(val->d.FUNCAPP.types);
         ExprValListFree(val->d.FUNCAPP.args);
         break;
      case LINDEX:
         ExprValFree(val->d.LINDEX.list);
         ExprValFree(val->d.LINDEX.index);
         break;
   }
   free(val);
}

struct ExprVal * ExprVal_Constant(struct Constant * c) {
  if (c == NULL) return NULL;
  unsigned long long number = abs_number_of_Constant(c);
  // printf("ExprVal_Constant: %c%llu\n", c->pos == 0 ? '-' : ' ', number);
  if (c->pos == 0) return ExprVal_VUOP(Oneg, ExprVal_EZ_VAL(number));
  return ExprVal_EZ_VAL(number);
}


struct Constant * ConstantFold(struct ExprVal *expr, struct persistent_env * env) {
   if (expr == NULL) return NULL;
   struct Constant * res;
   switch (expr->t) {
     case EZ_VAL:
       res = Constant_number(expr->d.EZ_VAL.number);
       break;
     case SIZE_OF:
       res = Constant_number(type_size(type_of_simple_ctype(expr->d.SIZE_OF.type, env)));
       break;
     case VUOP: {
       struct Constant * c = ConstantFold(expr->d.VUOP.expr, env);
       if (c == NULL) return NULL;
       switch (expr->d.VUOP.op) {
         case Onot:
           res = Constant_not(c);
           break;
         case Oneg:
           res = Constant_neg(c);
           break;
         case Onint:
           res = Constant_nint(c);
           break;
       }
       break;
     }
     case VBOP: {
        struct Constant * c1 = ConstantFold(expr->d.VBOP.expr1, env);
        struct Constant * c2 = ConstantFold(expr->d.VBOP.expr2, env);
        // printf("VBOP: ");
        // ConstantPrint(c1);
        // printf(" %d ", expr->d.VBOP.op);
        // ConstantPrint(c2);
        // printf("\n");
        if (c1 == NULL || c2 == NULL) return NULL;
        switch (expr->d.VBOP.op) {
          case Oadd:
            res = Constant_add(c1, c2);
            break;
          case Osub:
            res = Constant_sub(c1, c2);
            break;
          case Omul:
            res = Constant_mul(c1, c2);
            break;
          case Odiv:
            return NULL; /* TODO: */
            break;
          case Omod:
            return NULL; /* TODO: */
            break;
          case Oand:
            res = Constant_and(c1, c2);
            break;
          case Oor:
            res = Constant_or(c1, c2);
            break;
          case Oxor:
            res = Constant_xor(c1, c2);
            break;
          case Oshl:
            res = Constant_shl(c1, c2);
            break;
          case Oshr:
            res = Constant_shr(c1, c2);
            break;
        }
        break;
     }
     case FUNCAPP: {
       if (expr->d.FUNCAPP.id == 10) { // ZPOW
         struct Constant *e = ConstantFold(expr->d.FUNCAPP.args->head->data, env);
         if (e == NULL) return NULL;
         struct Constant *e2 = ConstantFold(expr->d.FUNCAPP.args->head->next->data, env);
         if (e2 == NULL)
           return NULL;
         res = Constant_ZPOW(e, e2);
       }
       else if (expr->d.FUNCAPP.id == 8) { // MAXINT
         res = Constant_number(2147483647);
       }
       else if (expr->d.FUNCAPP.id == 9) { // MININT
         res = Constant_neg(Constant_number(2147483648ll));
       }
       else if (expr->d.FUNCAPP.id == 12) { // LNB
         struct Constant *e = ConstantFold(expr->d.FUNCAPP.args->head->data, env);
         if (e == NULL) return NULL;
         struct Constant *e2 = ConstantFold(expr->d.FUNCAPP.args->head->next->data, env);
         if (e2 == NULL)
           return NULL;
         res = Constant_LNB(e, e2);
       }
       else if (expr->d.FUNCAPP.id == 11) { // ULNB
         struct Constant *e = ConstantFold(expr->d.FUNCAPP.args->head->data, env);
         if (e == NULL) return NULL;
         struct Constant *e2 = ConstantFold(expr->d.FUNCAPP.args->head->next->data, env);
         if (e2 == NULL)
           return NULL;
         res = Constant_ULNB(e, e2);
       }
       else
         return NULL;
       break;
     }
     default :
       return NULL;
  }
   return res;
}

struct ExprVal * ExprValConstantFold(struct ExprVal * expr, struct persistent_env * env) {
  if (expr == NULL) return NULL;
  // printf("Start ConstantFold\n");
  struct Constant * c = ConstantFold(expr, env);
  // printf("Finish ConstantFold\n");
  // printf("ConstantFold result: ");
  // if (c != NULL) ConstantPrint(c);
  // else printf("NULL\n");
  if (c != NULL) return ExprVal_Constant(c);
  // printf("ConstantFold failed\n");
  struct ExprVal * res; 
  switch (expr -> t) {
    case EZ_VAL: {
      res = ExprValDeepCopy(expr);
      break;
    }
    case SIZE_OF: {
      // normally this case will not happen
      // struct type * at = type_of_simple_ctype(expr->d.SIZE_OF.type, env);
      // res = ExprVal_EZ_VAL(type_size(at));
      // break;
      res = ExprValDeepCopy(expr);
      break;
    }
    case VFIELD_ADDRESS: {
      res = ExprVal_VFIELD_ADDRESS(ExprValConstantFold(expr->d.VFIELD_ADDRESS.expr, env), expr->d.VFIELD_ADDRESS.field_id);
      break;
    }
    case VUOP: {
      res = ExprVal_VUOP(expr->d.VUOP.op, ExprValConstantFold(expr->d.VUOP.expr, env));
      break;
    }
    case VBOP: {
      res = ExprVal_VBOP(expr->d.VBOP.op, ExprValConstantFold(expr->d.VBOP.expr1, env), ExprValConstantFold(expr->d.VBOP.expr2, env));
      break;
    }
    case FUNCAPP: {
      res = ExprVal_FUNCAPP(expr->d.FUNCAPP.id, PolyTypeListDeepCopy(expr->d.FUNCAPP.types), ExprValListConstantFold(expr->d.FUNCAPP.args, env));
      break;
    }
    case LINDEX: {
      struct ExprVal * list = ExprValConstantFold(expr->d.LINDEX.list, env);
      struct ExprVal * index = ExprValConstantFold(expr->d.LINDEX.index, env);
      res = ExprVal_LINDEX(list, index);
      break;
    }
    case TIME_COST: {
      res = ExprValDeepCopy(expr);
      break;
    }
  }
  return res;
}

struct ExprValList * ExprValListConstantFold(struct ExprValList * list, struct persistent_env * env) {
  struct ExprValList *res = ExprValListNil();
  if (list == NULL) return NULL;
  if (ExprValListIsEmpty(list)) return ExprValListNil();
  struct ExprValListNode *iter;
  for (iter = list->head; iter != NULL; iter = iter->next) {
    res = ExprValListCons(ExprValConstantFold(iter->data , env), res);
  }
  return ExprValListReverse(res);
}