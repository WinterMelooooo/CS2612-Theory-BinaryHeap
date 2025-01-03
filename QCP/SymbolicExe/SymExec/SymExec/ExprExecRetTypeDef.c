#include "ExprExecRetTypeDef.h"

struct ExprExecRetValue * ExprExecRetValueNil() {
   return NULL;
}

struct ExprExecRetValue * ExprExecRetValueCons(struct Assertion * asrt, struct ExprVal * val, struct PropList * constraits, struct IntList * vars,  struct ExprExecRetValue * next) {
   struct ExprExecRetValue * res = (struct ExprExecRetValue *) malloc(sizeof(struct ExprExecRetValue));
   res->asrt = asrt;
   res->val = val;
   res->constraits = constraits;
   res->introed_vars = vars;
   res->next = next;
   return res;
}

struct ExprExecRetValue * ExprExecRetValueLink(struct ExprExecRetValue * list1, struct ExprExecRetValue * list2) {
   if (list1 == NULL) return list2;
   if (list2 == NULL) return list1;
   struct ExprExecRetValue * tmp = list1;
   while (tmp->next != NULL) {
      tmp = tmp->next;
   }
   tmp->next = list2;
   return list1;
}

struct ExprExecRetType * NewExprExecRetType() {
   struct ExprExecRetType * ret;
   ret = (struct ExprExecRetType *) malloc(sizeof(struct ExprExecRetType));
   ret->ret_value = ExprExecRetValueNil();
   ret->witness = NewWitness();
   return ret;
}

struct ExprExecRetValue * ExprValToBool(struct Assertion * asrt, struct ExprVal * val) {
   struct ExprExecRetValue * ret = ExprExecRetValueNil();
   if (val == NULL) {
     printf("Invalid Input for ExprValToBool.\n");
     exit(1);
   }
   if (val->t == EZ_VAL) {
      if (val->d.EZ_VAL.number == 0) {
         ret = ExprExecRetValueCons(asrt, ExprVal_EZ_VAL(0), PropListNil(), IntListNil(), ret);
      } else {
         ret = ExprExecRetValueCons(asrt, ExprVal_EZ_VAL(1), PropListNil(), IntListNil(), ret);
      }
      ExprValFree(val);
   } else {
      struct Proposition * new_prop1, * new_prop2;
      new_prop1 = PropCompare(PROP_EQ, ExprValDeepCopy(val), ExprVal_EZ_VAL(0));
      struct Assertion * new_asrt;
      new_asrt = AsrtDeepCopy(asrt);
      new_asrt->prop_list = PropListCons(new_prop1, new_asrt->prop_list);
      ret = ExprExecRetValueCons(new_asrt, ExprVal_EZ_VAL(0), PropListCons(PropDeepCopy(new_prop1), PropListNil()), IntListNil(), ret);
      new_prop2 = PropCompare(PROP_NEQ, val, ExprVal_EZ_VAL(0));
      asrt->prop_list = PropListCons(new_prop2, asrt->prop_list);
      ret = ExprExecRetValueCons(asrt, ExprVal_EZ_VAL(1), PropListCons(PropDeepCopy(new_prop2), PropListNil()), IntListNil(), ret);
   }
   return ret;
}

struct ExprExecRetType * ExprExecRetTypeToBool(struct ExprExecRetType * origin) {
   struct ExprExecRetValue * new_list = ExprExecRetValueNil();
   struct ExprExecRetValue * list;
   list = origin->ret_value;
   while (list != NULL) {
      new_list = ExprExecRetValueLink(ExprValToBool(list->asrt, list->val), new_list);
      struct ExprExecRetValue * tmp;
      tmp = list;
      list = list->next;
      free(tmp);
   }
   origin->ret_value = new_list;
   return origin;
}

int ExprExecRetValueEqual(struct ExprExecRetValue * v1, struct ExprExecRetValue * v2) {
   if (v1 == v2) return 1;
   if (v1 == NULL || v2 == NULL) return 0;
   if (PropListCheckEqual(v1->constraits, v2->constraits) == 0) return 0;
   if (ExprValCheckEqual(v1->val, v2->val) == 0) return 0;
   struct IntListNode * tmp1, * tmp2;
   tmp1 = v1->introed_vars->head;
   tmp2 = v2->introed_vars->head;
   while (tmp1 != NULL || tmp2 != NULL) {
      if (tmp1 == NULL || tmp2 == NULL) return 0;
      if (tmp1->data != tmp2->data) return 0;
      tmp1 = tmp1->next;
      tmp2 = tmp2->next;
   }
   return ExprExecRetValueEqual(v1->next, v2->next);
}

void ExprExecRetValueFree(struct ExprExecRetValue * ret_value) {
   if (ret_value == NULL) return;
   ExprExecRetValueFree(ret_value->next);
   free(ret_value);
}

void ExprExecRetTypeFree(struct ExprExecRetType * ret_type) {
   ExprExecRetValueFree(ret_type->ret_value);
   free(ret_type);
}

struct ExprListExecRetValue * ExprListExecRetValueNil() {
   return NULL;
}

struct ExprListExecRetValue * ExprListExecRetValueCons(struct Assertion * asrt, struct ExprValList * val, struct PropList * constraits, struct IntList * vars,  struct ExprListExecRetValue * next) {
   struct ExprListExecRetValue * res = (struct ExprListExecRetValue *) malloc(sizeof(struct ExprListExecRetValue));
   res->asrt = asrt;
   res->val = val;
   res->constraits = constraits;
   res->introed_vars = vars;
   res->next = next;
   return res;
}

struct ExprListExecRetValue * ExprListExecRetValueLink(struct ExprListExecRetValue * list1, struct ExprListExecRetValue * list2) {
   if (list1 == NULL) return list2;
   if (list2 == NULL) return list1;
   struct ExprListExecRetValue * tmp = list1;
   while (tmp->next != NULL) {
      tmp = tmp->next;
   }
   tmp->next = list2;
   return list1;
}

void ExprListExecRetValueFree(struct ExprListExecRetValue * ret_value) {
   if (ret_value == NULL) return;
   ExprListExecRetValueFree(ret_value->next);
   free(ret_value);
}

struct ExprListExecRetType * NewExprListExecRetType() {
   struct ExprListExecRetType * ret;
   ret = (struct ExprListExecRetType *) malloc(sizeof(struct ExprListExecRetType));
   ret->ret_value = NULL;
   ret->witness = NewWitness();
   return ret;
}

void ExprListExecRetTypeFree(struct ExprListExecRetType * ret_type) {
   ExprListExecRetValueFree(ret_type->ret_value);
   free(ret_type);
}