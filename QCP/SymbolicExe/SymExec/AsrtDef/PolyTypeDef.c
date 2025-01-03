#include <assert.h>
#include "../../compiler/env.h"
#include "PolyTypeDef.h"

struct PolyType * PolyTypeAsrt() {
   return PolyTypeFuncApp(BUILTINTYPE_ASSERTION, PolyTypeListNil());
}

struct PolyType * PolyTypeProp() {
   return PolyTypeFuncApp(BUILTINTYPE_PROP, PolyTypeListNil());
}

struct PolyType * PolyTypePrimitive(enum PrimitiveType type) {
   switch (type) {
      case NAT_TYPE:
         return PolyTypeFuncApp(BUILTINTYPE_NAT, PolyTypeListNil());
      case Z_TYPE:
         return PolyTypeFuncApp(BUILTINTYPE_Z, PolyTypeListNil());
      case BOOL_TYPE:
         return PolyTypeFuncApp(BUILTINTYPE_BOOL, PolyTypeListNil());
      case PROP_TYPE:
         return PolyTypeProp();
      case ASRT_TYPE:
         return PolyTypeAsrt();
      default:
         assert(0);
   }
   return NULL;
}

struct PolyType * PolyTypeVar(int id) {
   struct PolyType * res = (struct PolyType *) malloc(sizeof(struct PolyType));
   res->t = POLY_VAR;
   res->d.VAR.id = id;
   return res;
}

struct PolyType * PolyTypeFuncApp(int func, struct PolyTypeList * args) {
   struct PolyType * res = (struct PolyType *) malloc(sizeof(struct PolyType));
   res->t = POLY_FUNCAPP;
   res->d.FUNCAPP.func = func;
   res->d.FUNCAPP.args = args;
   return res;
}

struct PolyType * PolyTypeArrow(struct PolyType * left, struct PolyType * right) {
   struct PolyType * res = (struct PolyType *) malloc(sizeof(struct PolyType));
   res->t = POLY_ARROW;
   res->d.ARROW.left = left;
   res->d.ARROW.right = right;
   return res;
}

struct PolyType * PolyTypeList(struct PolyType * inner_type) {
   return PolyTypeFuncApp(BUILTINTYPE_LIST, PolyTypeListCons(inner_type, PolyTypeListNil()));
}

struct PolyType * PolyTypeDeepCopy(struct PolyType * t) {
   if (t == NULL) return NULL;
   struct PolyType * res = (struct PolyType *) malloc(sizeof(struct PolyType));
   res->t = t->t;
   switch (t->t) {
      case POLY_VAR:
         res->d.VAR.id = t->d.VAR.id;
         break;
      case POLY_FUNCAPP:
         res->d.FUNCAPP.func = t->d.FUNCAPP.func;
         res->d.FUNCAPP.args = PolyTypeListDeepCopy(t->d.FUNCAPP.args);
         break;
      case POLY_ARROW:
         res->d.ARROW.left = PolyTypeDeepCopy(t->d.ARROW.left);
         res->d.ARROW.right = PolyTypeDeepCopy(t->d.ARROW.right);
         break;
   }
   return res;
}

void PolyTypeFree(struct PolyType * t) {
   switch (t->t) {
      case POLY_VAR:
         break;
      case POLY_FUNCAPP:
         PolyTypeListFree(t->d.FUNCAPP.args);
         break;
      case POLY_ARROW:
         PolyTypeFree(t->d.ARROW.left);
         PolyTypeFree(t->d.ARROW.right);
         break;
   }
}

int PolyTypeCheckEqual(struct PolyType * t1, struct PolyType * t2) {
   if (t1 == t2) return 1;
   if (t1 == NULL || t2 == NULL) return 0;
   if (t1->t != t2->t) return 0;
   switch (t1->t) {
      case POLY_VAR:
         return t1->d.VAR.id == t2->d.VAR.id;
      case POLY_FUNCAPP:
         if (t1->d.FUNCAPP.func != t2->d.FUNCAPP.func) return 0;
         return PolyTypeListCheckEqual(t1->d.FUNCAPP.args, t2->d.FUNCAPP.args);
      case POLY_ARROW:
         return PolyTypeCheckEqual(t1->d.ARROW.left, t2->d.ARROW.left) && PolyTypeCheckEqual(t1->d.ARROW.right, t2->d.ARROW.right);
   }
   return 0;
}

int PolyTypeListCheckEqual(struct PolyTypeList * l1, struct PolyTypeList * l2) {
   if (l1 == l2) return 1;
   if (l1 == NULL || l2 == NULL) return 0;
   struct PolyTypeListNode * n1 = l1->head, * n2 = l2->head;
   while (n1 != NULL && n2 != NULL) {
      if (!PolyTypeCheckEqual(n1->data, n2->data)) return 0;
      n1 = n1->next;
      n2 = n2->next;
   }
   return n1 == NULL && n2 == NULL;
}

struct PolyType * PolyTypeSubst(struct PolyType * t, struct PolyType * pre, struct PolyType * post) {
   if (t == NULL) return NULL;
   if (PolyTypeCheckEqual(t, pre)) return PolyTypeDeepCopy(post);
   switch (t->t) {
      case POLY_VAR:
         return t;
      case POLY_FUNCAPP:
         return PolyTypeFuncApp(t->d.FUNCAPP.func, PolyTypeListSubst(t->d.FUNCAPP.args, pre, post));
      case POLY_ARROW:
         return PolyTypeArrow(PolyTypeSubst(t->d.ARROW.left, pre, post), PolyTypeSubst(t->d.ARROW.right, pre, post));
   }
   return NULL;
}

struct PolyTypeList * PolyTypeListSubst(struct PolyTypeList * l, struct PolyType * pre, struct PolyType * post) {
   if (l == NULL) return NULL;
   struct PolyTypeListNode * iter;
   for (iter = l->head; iter != NULL; iter = iter->next) {
      iter->data = PolyTypeSubst(iter->data, pre, post);
   }
   return l;
}

DEFINE_LIST(PolyTypeList, struct PolyType *, data)

struct PolyTypeListNode* PolyTypeListNodeDeepCopy(struct PolyTypeListNode * node) {
   if (node == NULL) return NULL;
   struct PolyTypeListNode * res = (struct PolyTypeListNode *) malloc(sizeof(struct PolyTypeListNode));
   res->data = PolyTypeDeepCopy(node->data);
   res->next = PolyTypeListNodeDeepCopy(node->next);
   return res;
}

void PolyTypeListNodeFree(struct PolyTypeListNode * node) {
   if (node == NULL) return;
   PolyTypeFree(node->data);
   free(node);
}
