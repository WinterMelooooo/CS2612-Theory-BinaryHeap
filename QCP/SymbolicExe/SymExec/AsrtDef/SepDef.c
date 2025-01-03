#include "SepDef.h"

struct Separation * SepDataAt(struct ExprVal * left, struct SimpleCtype * ty, struct ExprVal * right) {
   struct Separation * res = (struct Separation *) malloc(sizeof(struct Separation));
   res->t = T_DATA_AT;
   res->d.DATA_AT.left = left;
   res->d.DATA_AT.ty = ty;
   res->d.DATA_AT.right = right;
   return res;
}

struct Separation * SepUndefDataAt(struct ExprVal * left, struct SimpleCtype * ty) {
   struct Separation * res = (struct Separation *) malloc(sizeof(struct Separation));
   res->t = T_UNDEF_DATA_AT;
   res->d.UNDEF_DATA_AT.left = left;
   res->d.UNDEF_DATA_AT.ty = ty;
   return res;
}

struct Separation * SepArr(struct ExprVal * addr, struct SimpleCtype * ty, struct ExprVal * value, struct ExprVal * size) {
   struct Separation * res = (struct Separation *) malloc(sizeof(struct Separation));
   res->t = T_ARR;
   res->d.ARR.addr = addr;
   res->d.ARR.ty = ty;
   res->d.ARR.value = value;
   res->d.ARR.size = size;
   return res;
}

struct Separation * SepOther(int ident, struct PolyTypeList * types, struct ExprValList * exprs) {
   struct Separation * res = (struct Separation *) malloc(sizeof(struct Separation));
   res->t = T_OTHER;
   res->d.OTHER.sep_id = ident;
   res->d.OTHER.types = types;
   res->d.OTHER.exprs = exprs;
   return res;
}

struct SepList* SepListNil() { return NULL; }

struct SepList* SepListCons(struct Separation * sep, struct SepList * next) {
   struct SepList * ret = (struct SepList *) malloc(sizeof(struct SepList));
   ret->head = sep;
   ret->next = next;
  return ret;
}

struct SepList* SepListLink(struct SepList * left, struct SepList * right) {
   if (left == NULL) return right;
   if (right == NULL) return left;
   struct SepList * iter;
   iter = left;
   while (iter->next != NULL) iter = iter->next;
   iter->next = right;
   return left;
}

struct SepList* SepListRemove(struct SepList * pos, struct SepList * list) {
   if (list == NULL) return NULL;
   if (list == pos) {
      struct SepList * next = pos->next;
      SepFree(pos->head);
      free(pos);
      return next;
   }
   list->next = SepListRemove(pos, list->next);
   return list;
}

int SeparationCheckEqual(struct Separation * sep1, struct Separation * sep2) {
   if (sep1 == sep2) {
      return 1;
   }
   if (sep1 == NULL || sep2 == NULL) {
      return 0;
   }
   if (sep1->t != sep2->t) {
      return 0;
   }
   switch (sep1->t) {
   case T_DATA_AT:
      return ExprValCheckEqual(sep1->d.DATA_AT.left, sep2->d.DATA_AT.left)
          && ExprValCheckEqual(sep1->d.DATA_AT.right, sep2->d.DATA_AT.right)
          && SimpleCtypeCheckEqual(sep1->d.DATA_AT.ty, sep2->d.DATA_AT.ty);
   case T_UNDEF_DATA_AT:
      return ExprValCheckEqual(sep1->d.UNDEF_DATA_AT.left, sep2->d.UNDEF_DATA_AT.left)
          && SimpleCtypeCheckEqual(sep1->d.UNDEF_DATA_AT.ty, sep2->d.UNDEF_DATA_AT.ty);
   case T_ARR:
      return ExprValCheckEqual(sep1->d.ARR.addr, sep2->d.ARR.addr)
          && ExprValCheckEqual(sep1->d.ARR.size, sep2->d.ARR.size)
          && ExprValCheckEqual(sep2->d.ARR.value, sep2->d.ARR.value)
          && SimpleCtypeCheckEqual(sep1->d.ARR.ty, sep2->d.ARR.ty);
   case T_OTHER:
      return sep1->d.OTHER.sep_id == sep2->d.OTHER.sep_id
          && ExprValListCheckEqual(sep1->d.OTHER.exprs, sep2->d.OTHER.exprs);
   }
}

struct Separation * SepDeepCopy(struct Separation * sep) {
   if (sep == NULL) return NULL;
   struct Separation * res = (struct Separation *) malloc(sizeof(struct Separation));
   res->t = sep->t;
   switch (sep->t) {
      case T_DATA_AT:
         res->d.DATA_AT.left = ExprValDeepCopy(sep->d.DATA_AT.left);
         res->d.DATA_AT.ty = SimpleCtypeDeepCopy(sep->d.DATA_AT.ty);
         res->d.DATA_AT.right = ExprValDeepCopy(sep->d.DATA_AT.right);
         break;
      case T_UNDEF_DATA_AT:
         res->d.UNDEF_DATA_AT.left = ExprValDeepCopy(sep->d.UNDEF_DATA_AT.left);
         res->d.UNDEF_DATA_AT.ty = SimpleCtypeDeepCopy(sep->d.UNDEF_DATA_AT.ty);
         break;
      case T_ARR:
         res->d.ARR.addr = ExprValDeepCopy(sep->d.ARR.addr);
         res->d.ARR.ty = SimpleCtypeDeepCopy(sep->d.ARR.ty);
         res->d.ARR.value = ExprValDeepCopy(sep->d.ARR.value);
         res->d.ARR.size = ExprValDeepCopy(sep->d.ARR.size);
         break;
      case T_OTHER:
         res->d.OTHER.sep_id = sep->d.OTHER.sep_id;
         res->d.OTHER.types = PolyTypeListDeepCopy(sep->d.OTHER.types);
         res->d.OTHER.exprs = ExprValListDeepCopy(sep->d.OTHER.exprs);
         break;
   }
   return res;
}

struct SepList * SepListDeepCopy(struct SepList * sep_list) {
   if (sep_list == NULL) return NULL;
   return SepListCons(SepDeepCopy(sep_list->head), SepListDeepCopy(sep_list->next));
}

struct Separation * SepSubst(struct Separation * sep, struct ExprVal * pre, struct ExprVal * post) {
   if (sep == NULL) return NULL;
   switch (sep->t) {
      case T_DATA_AT:
         sep->d.DATA_AT.left = ExprValSubst(sep->d.DATA_AT.left, pre, post);
         sep->d.DATA_AT.right = ExprValSubst(sep->d.DATA_AT.right, pre, post);
         break;
      case T_UNDEF_DATA_AT:
         sep->d.UNDEF_DATA_AT.left = ExprValSubst(sep->d.UNDEF_DATA_AT.left, pre, post);
         break;
      case T_ARR:
         sep->d.ARR.addr = ExprValSubst(sep->d.ARR.addr, pre, post);
         sep->d.ARR.value = ExprValSubst(sep->d.ARR.value, pre, post);
         sep->d.ARR.size = ExprValSubst(sep->d.ARR.size, pre, post);
         break;
      case T_OTHER: {
         if (pre->t == FUNCAPP && pre->d.FUNCAPP.id == sep->d.OTHER.sep_id && PolyTypeListIsEmpty(sep->d.OTHER.types)) {
            sep->d.OTHER.sep_id = post->d.FUNCAPP.id;
            sep->d.OTHER.types = PolyTypeListDeepCopy(post->d.FUNCAPP.types);
            sep->d.OTHER.exprs = ExprValListLink(ExprValListDeepCopy(post->d.FUNCAPP.args), ExprValListSubst(sep->d.OTHER.exprs, pre, post));
         }
         else sep->d.OTHER.exprs = ExprValListSubst(sep->d.OTHER.exprs, pre, post);
         break;
      }
      default:
         break;
   }
   return sep;
}

struct Separation * SepSubstPolyType(struct Separation * sep, struct PolyType * pre, struct PolyType * post) {
   if (sep == NULL) return NULL;
   switch (sep->t) {
      case T_DATA_AT:
         sep->d.DATA_AT.left = ExprValSubstPolyType(sep->d.DATA_AT.left, pre, post);
         sep->d.DATA_AT.right = ExprValSubstPolyType(sep->d.DATA_AT.right, pre, post);
         break;
      case T_UNDEF_DATA_AT:
         sep->d.UNDEF_DATA_AT.left = ExprValSubstPolyType(sep->d.UNDEF_DATA_AT.left, pre, post);
         break;
      case T_ARR:
         sep->d.ARR.addr = ExprValSubstPolyType(sep->d.ARR.addr, pre, post);
         sep->d.ARR.value = ExprValSubstPolyType(sep->d.ARR.value, pre, post);
         sep->d.ARR.size = ExprValSubstPolyType(sep->d.ARR.size, pre, post);
         break;
      case T_OTHER:
         sep->d.OTHER.types = PolyTypeListSubst(sep->d.OTHER.types, pre, post);
         sep->d.OTHER.exprs = ExprValListSubstPolyType(sep->d.OTHER.exprs, pre, post);
         break;
   }
   return sep;
}

struct SepList * SepListSubst(struct SepList * sep_list, struct ExprVal * pre, struct ExprVal * post) {
   for (struct SepList * iter = sep_list; iter != NULL; iter = iter->next) {
      iter->head = SepSubst(iter->head, pre, post);
   }
   return sep_list;
}

struct SepList * SepListSubstPolyType(struct SepList * sep_list, struct PolyType * pre, struct PolyType * post) {
   for (struct SepList * iter = sep_list; iter != NULL; iter = iter->next) {
      iter->head = SepSubstPolyType(iter->head, pre, post);
   }
   return sep_list;
}

struct SepList * FindPosOfAddr(struct SepList * sep_list, struct ExprVal * addr) {
   if (sep_list == NULL) return NULL;
   switch (sep_list->head->t) {
      case T_DATA_AT:
         if (ExprValCheckEqual(sep_list->head->d.DATA_AT.left, addr)) return sep_list;
         break;
      case T_UNDEF_DATA_AT:
         if (ExprValCheckEqual(sep_list->head->d.UNDEF_DATA_AT.left, addr)) return sep_list;
         break;
      case T_ARR:
         if (ExprValCheckEqual(sep_list->head->d.ARR.addr, addr)) return sep_list;
         break;
   }
   return FindPosOfAddr(sep_list->next, addr);
}

void SepFree(struct Separation * sep) {
   if (sep == NULL) return;
#ifdef DEBUG_MEMORY
   printf("Free sep : %p\n", sep);
#endif
   switch (sep->t) {
      case T_DATA_AT:
         ExprValFree(sep->d.DATA_AT.left);
         SimpleCtypeFree(sep->d.DATA_AT.ty);
         ExprValFree(sep->d.DATA_AT.right);
         break;
      case T_UNDEF_DATA_AT:
         ExprValFree(sep->d.UNDEF_DATA_AT.left);
         SimpleCtypeFree(sep->d.UNDEF_DATA_AT.ty);
         break;
      case T_ARR:
         ExprValFree(sep->d.ARR.addr);
         SimpleCtypeFree(sep->d.ARR.ty);
         ExprValFree(sep->d.ARR.value);
         ExprValFree(sep->d.ARR.size);
         break;
      case T_OTHER:
         PolyTypeListFree(sep->d.OTHER.types);
         ExprValListFree(sep->d.OTHER.exprs);
         break;
   }
   free(sep);
}

void SepListFree(struct SepList * sep_list) {
   if (sep_list == NULL) return;
   SepFree(sep_list->head);
   SepListFree(sep_list->next);
   free(sep_list);
}
