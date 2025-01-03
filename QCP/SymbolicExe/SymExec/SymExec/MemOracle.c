#include <assert.h>
#include "MemOracle.h"
#include "../Utility/InnerAsrtPrinter.h"

int InMemChunk(struct ExprVal * addr, struct ExprVal * base, struct ExprVal * size) {
   if (addr == NULL) return 0;
   if (ExprValCheckEqual(addr, base)) return 1;
   switch (addr->t) {
      case EZ_VAL:
         return 0;
      case VFIELD_ADDRESS:
         return 0;
      case VUOP:
         return InMemChunk(addr->d.VUOP.expr, base, size);
      case VBOP:
         return InMemChunk(addr->d.VBOP.expr1, base, size) || InMemChunk(addr->d.VBOP.expr2, base, size);
      case FUNCAPP:
         return 0;
   }
   return 0;
}

struct ExprVal * ExprValNaiveDivSimplify(struct ExprVal * expr, int divisor) {
   if (expr == NULL) return NULL;
   assert(expr->t == VBOP && expr->d.VBOP.op == Omul);
   assert(expr->d.VBOP.expr2->t == EZ_VAL && expr->d.VBOP.expr2->d.EZ_VAL.number == divisor);
   return expr->d.VBOP.expr1;
}

struct ExprVal * AsrtReadMem(struct Assertion * asrt, struct ExprVal * addr, int chunk_size) {
   struct ExprVal * ret;
   ret = GetDataAtValue(asrt, addr);
   if (ret != NULL) return ret;
   struct SepList * sep_list = asrt->sep_list;
   while (sep_list != NULL) {
      struct Separation * sep = sep_list->head;
      if (sep->t == T_ARR) {
         if (InMemChunk(addr, sep->d.ARR.addr, sep->d.ARR.size)) {
            struct ExprVal * index;
            // index = ExprVal_VBOP(Odiv, ExprVal_VBOP(Osub, addr, ExprValDeepCopy(sep->d.ARR.addr)), ExprVal_EZ_VAL(chunk_size));
            index = ExprValDeepCopy(addr->d.VBOP.expr2);
            index = ExprValNaiveDivSimplify(index, chunk_size);
            return ExprVal_LINDEX(ExprValDeepCopy(sep->d.ARR.value), index);
         }
      }
      sep_list = sep_list->next;
   }
   return NULL;
}

// 0 if success, 1 if fail
// int AsrtWriteMem(struct Assertion * asrt, struct ExprVal * addr, struct ExprVal * val, int chunk_size) {
//    if (ReplaceDataAtValue(asrt, addr, val) == 0) return 0;
//    struct SepList * sep_list = asrt->sep_list;
//    while (sep_list != NULL) {
//       struct Separation * sep = sep_list->head;
//       if (sep->t == T_ARR) {
//          if (InMemChunk(addr, sep->d.ARR.addr, sep->d.ARR.size)) {
//             struct ExprVal * index;
//             // index = ExprVal_VBOP(Odiv, ExprVal_VBOP(Osub, addr, ExprValDeepCopy(sep->d.ARR.addr)), ExprVal_EZ_VAL(chunk_size));
//             index = ExprValDeepCopy(addr->d.VBOP.expr2);
//             index = ExprValNaiveDivSimplify(index, chunk_size);
//             struct ExprVal * new_value;
//             struct ExprValList * args = ExprValListNil();
//             args = ExprValListSnoc(ExprValDeepCopy(sep->d.ARR.value), args);
//             args = ExprValListSnoc(index, args);
//             args = ExprValListSnoc(val, args);
//             new_value = ExprVal_FUNCAPP("replace", PolyTypeListNil(), args);
//             sep->d.ARR.value = new_value;
//             return 0;
//          }
//       }
//       sep_list = sep_list->next;
//    }
//    return 1;
// }