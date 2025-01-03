#include "OperatorTranser.h"

enum InnerBinaryOperation AriBinOpTrans(enum BinOpType op) {
   enum InnerBinaryOperation res;
   switch (op) {
   case T_PLUS: res = Oadd; break;
   case T_MINUS: res = Osub; break;
   case T_MUL: res = Omul; break;
   case T_DIV: res = Odiv; break;
   case T_MOD: res = Omod; break;
   case T_BAND: res = Oand; break;
   case T_BOR: res = Oor; break;
   case T_XOR: res = Oxor; break;
   case T_SHL: res = Oshl; break;
   case T_SHR: res = Oshr; break;
   default:
      fprintf(stderr, "not binary expr operator.\n");
      exit(1);
      break;
   }
   return res;
}

enum BinOpType InnerBinOpToUserBinOp(enum InnerBinaryOperation op) {
   enum BinOpType res;
   switch (op) {
   case Oadd: res = T_PLUS; break;
   case Osub: res = T_MINUS; break;
   case Omul: res = T_MUL; break;
   case Odiv: res = T_DIV; break;
   case Omod: res = T_MOD; break;
   case Oand: res = T_BAND; break;
   case Oor: res = T_BOR; break;
   case Oxor: res = T_XOR; break;
   case Oshl: res = T_SHL; break;
   case Oshr: res = T_SHR; break;
   default:
      fprintf(stderr, "not binary expr operator.\n");
      exit(1);
      break;
   }
   return res;
}

int IsCmpBinOp(enum BinOpType op) {
   switch (op) {
   case T_LT: return 1; break;
   case T_GT: return 1; break;
   case T_LE: return 1; break;
   case T_GE: return 1; break;
   case T_EQ: return 1; break;
   case T_NE: return 1; break;
   default: return 0; break;
   }
}

enum PropCompOp BinCompareOpToPropComp(enum BinOpType op) {
   switch (op) {
   case T_LT: return PROP_LT; break;
   case T_GT: return PROP_GT; break;
   case T_LE: return PROP_LE; break;
   case T_GE: return PROP_GE; break;
   case T_EQ: return PROP_EQ; break;
   case T_NE: return PROP_NEQ; break;
   default: 
      fprintf(stderr, "not binary comp operator.\n");
      exit(1);
      break;
   }
}

enum InnerUnaryOperation UserUnaryToInnerUnary(enum UnOpType op) {
   enum InnerUnaryOperation res;
   switch (op) {
   case T_UMINUS: res = Oneg; break; // -
   case T_NOTBOOL: res = Onot; break; // !
   case T_NOTINT: res = Onint; break; // ~
   default:
      fprintf(stderr, "not unary expr operator.\n");
      exit(0);
      break;
   }
   return res; 
}

enum UnOpType InnerUnaryToUserUnary(enum InnerUnaryOperation op) {
   enum UnOpType res;
   switch (op) {
   case Oneg: res = T_UMINUS; break; // -
   case Onot: res = T_NOTBOOL; break; // !
   case Onint: res = T_NOTINT; break; // ~
   default:
      fprintf(stderr, "not unary expr operator.\n");
      exit(0);
      break;
   }
   return res; 
}

// LT -> GE, LE -> GT, GT -> LE, GE -> LT, EQ -> NE, NE -> EQ
enum PropCompOp PropCompareOpReverse(enum PropCompOp op) {
   switch (op) {
      case PROP_LT:
         return PROP_GE;
         break;
      case PROP_GT:
         return PROP_LE;
         break;
      case PROP_LE:
         return PROP_GT;
         break;
      case PROP_GE:
         return PROP_LT;
         break;
      case PROP_EQ:
         return PROP_NEQ;
         break;
      case PROP_NEQ:
         return PROP_EQ;
         break;
      default:
         fprintf(stderr, "PropCompareOpReverse: not a compare op\n");
         exit(-1);
         break;
   }
}


/*
enum AssignType {
  T_ASSIGN,      // =
  T_ADD_ASSIGN,  // +=
  T_SUB_ASSIGN,  // -=
  T_MUL_ASSIGN,  // *=
  T_DIV_ASSIGN,  // /=
  T_MOD_ASSIGN,  // %=
  T_BAND_ASSIGN, // &=
  T_BOR_ASSIGN,  // |=
  T_XOR_ASSIGN,  // ^=
  T_SHL_ASSIGN,  // <<=
  T_SHR_ASSIGN   // >>=
};
*/
enum InnerBinaryOperation AriAsignOpTrans(enum AssignType op) {
   enum InnerBinaryOperation res;
   switch (op) {
   case T_ASSIGN: fprintf(stderr, "Unexpected op %s %d", __FILE__, __LINE__); exit(1);
   case T_ADD_ASSIGN: res = Oadd; break;
   case T_SUB_ASSIGN: res = Osub; break;
   case T_MUL_ASSIGN: res = Omul; break;
   case T_DIV_ASSIGN: res = Odiv; break;
   case T_MOD_ASSIGN: res = Omod; break;
   case T_BAND_ASSIGN: res = Oand; break;
   case T_BOR_ASSIGN: res = Oor; break;
   case T_XOR_ASSIGN: res = Oxor; break;
   case T_SHL_ASSIGN: res = Oshl; break;
   case T_SHR_ASSIGN: res = Oshr; break;
   default:
      fprintf(stderr, "not assign expr operator.\n");
      exit(1);
      break;
   }
   return res;
}

enum BinOpType InnerToUserPropCompOpTrans(enum PropCompOp op) {
   enum BinOpType res;
   switch (op) {
   case PROP_LT: res = T_LT; break;
   case PROP_GT: res = T_GT; break;
   case PROP_LE: res = T_LE; break;
   case PROP_GE: res = T_GE; break;
   case PROP_EQ: res = T_EQ; break;
   case PROP_NEQ: res = T_NE; break;
   default:
      fprintf(stderr, "not binary comp operator.\n");
      exit(1);
      break;
   }
   return res;
}