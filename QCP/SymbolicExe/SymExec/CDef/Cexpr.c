#include <stddef.h>
#include <stdlib.h>
#include "Cexpr.h"

DEFINE_LIST2(TypeArgList, char *, name, struct PolyType *, type)
DEFINE_LIST3(VirtArgList, char*, name, struct ExprVal *, val, struct PolyType *, type)

struct TypeArgListNode * TypeArgListNodeDeepCopy(struct TypeArgListNode * node) {
   if (node == NULL) return NULL;
   struct TypeArgListNode * res = (struct TypeArgListNode *) malloc(sizeof(struct TypeArgListNode));
   res->name = malloc(sizeof(char) * (strlen(node->name) + 1));
   strcpy(res->name, node->name);
   res->type = PolyTypeDeepCopy(node->type);
   res->next = TypeArgListNodeDeepCopy(node->next);
   return res;
}

struct VirtArgListNode * VirtArgListNodeDeepCopy(struct VirtArgListNode * node) {
   if (node == NULL) return NULL;
   struct VirtArgListNode * res = (struct VirtArgListNode *) malloc(sizeof(struct VirtArgListNode));
   res->name = malloc(sizeof(char) * (strlen(node->name) + 1));
   strcpy(res->name, node->name);
   res->val = ExprValDeepCopy(node->val);
   res->type = PolyTypeDeepCopy(node->type);
   res->next = VirtArgListNodeDeepCopy(node->next);
   return res;
}

struct VirtArg * VirtArgDeepCopy(struct VirtArg * vargs) {
   if (vargs == NULL) return NULL;
   struct VirtArg * res = (struct VirtArg *) malloc(sizeof(struct VirtArg));
   res->ctx = func_spec_deep_copy(vargs->ctx);
   res->type_args = TypeArgListDeepCopy(vargs->type_args);
   res->args = VirtArgListDeepCopy(vargs->args);
   return res;
}

void TypeArgListNodeFree(struct TypeArgListNode * node) {
   if (node == NULL) return;
   free(node->name);
   PolyTypeFree(node->type);
   free(node);
}

void VirtArgListNodeFree(struct VirtArgListNode * node) {
   if (node == NULL) return;
   free(node->name);
   ExprValFree(node->val);
   PolyTypeFree(node->type);
   free(node);
}

void VirtArgFree(struct VirtArg * vargs) {
   if (vargs == NULL) return;
   func_spec_free(vargs->ctx);
   VirtArgListFree(vargs->args);
   free(vargs);
}

struct VirtArg * CreateVirtArg(struct func_spec * ctx, struct TypeArgList * type_args, struct VirtArgList * args) {
   struct VirtArg * res = (struct VirtArg *) malloc(sizeof(struct VirtArg));
   res->ctx = ctx;
   res->type_args = type_args;
   res->args = args;
   return res;
}

struct Cexpr * CexprConst(unsigned long long number, struct SimpleCtype * type) {
   struct Cexpr * expr = (struct Cexpr *) malloc(sizeof(struct Cexpr));
   expr->t = C_CONST;
   expr->d.C_CONST.number = number;
   expr->type = type;
   return expr;
}

struct Cexpr * CexprVar(int id, struct SimpleCtype * type) {
   struct Cexpr * expr = (struct Cexpr *) malloc(sizeof(struct Cexpr));
   expr->t = C_VAR;
   expr->d.C_VAR.id = id;
   expr->type = type;
   return expr;
}

struct Cexpr * CexprDeref(struct Cexpr * expr, struct SimpleCtype * type) {
   struct Cexpr * res = (struct Cexpr *) malloc(sizeof(struct Cexpr));
   res->t = C_DEREF;
   res->d.C_DEREF.expr = expr;
   res->type = type;
   return res;
}

struct Cexpr * CexprAddrof(struct Cexpr * expr, struct SimpleCtype * type) {
   struct Cexpr * res = (struct Cexpr *) malloc(sizeof(struct Cexpr));
   res->t = C_ADDROF;
   res->d.C_ADDROF.expr = expr;
   res->type = type;
   return res;
}

struct Cexpr * CexprUnop(enum UnOpType op, struct Cexpr * expr, struct SimpleCtype * type) {
   struct Cexpr * res = (struct Cexpr *) malloc(sizeof(struct Cexpr));
   res->t = C_UNOP;
   res->d.C_UNOP.op = op;
   res->d.C_UNOP.expr = expr;
   res->type = type;
   return res;
}

struct Cexpr * CexprBinop(enum BinOpType op, struct Cexpr * expr1, struct Cexpr * expr2, struct SimpleCtype * type) {
   struct Cexpr * res = (struct Cexpr *) malloc(sizeof(struct Cexpr));
   res->t = C_BINOP;
   res->d.C_BINOP.op = op;
   res->d.C_BINOP.expr1 = expr1;
   res->d.C_BINOP.expr2 = expr2;
   res->type = type;
   return res;
}

struct Cexpr * CexprCast(struct Cexpr * expr, struct SimpleCtype * type) {
   struct Cexpr * res = (struct Cexpr *) malloc(sizeof(struct Cexpr));
   res->t = C_CAST;
   res->d.C_CAST.expr = expr;
   res->type = type;
   return res;
}

struct Cexpr * CexprStructfield(struct Cexpr * expr, int field_id, struct SimpleCtype * type) {
   struct Cexpr * res = (struct Cexpr *) malloc(sizeof(struct Cexpr));
   res->t = C_STRUCTFIELD;
   res->d.C_STRUCTFIELD.expr = expr;
   res->d.C_STRUCTFIELD.field_id = field_id;
   res->type = type;
   return res;
}

struct Cexpr * CexprUnionfield(struct Cexpr * expr, int field_id, struct SimpleCtype * type) {
   struct Cexpr * res = (struct Cexpr *) malloc(sizeof(struct Cexpr));
   res->t = C_UNIONFIELD;
   res->d.C_UNIONFIELD.expr = expr;
   res->d.C_UNIONFIELD.field_id = field_id;
   res->type = type;
   return res;
}

struct Cexpr * CexprSizeof(struct SimpleCtype * inner_type, struct SimpleCtype * type) {
   struct Cexpr * res = (struct Cexpr *) malloc(sizeof(struct Cexpr));
   res->t = C_SIZEOF;
   res->d.C_SIZEOF.inner_type = inner_type;
   res->type = type;
   return res;
}

struct Cexpr * CexprIndex(struct Cexpr * arr_expr, struct Cexpr * inner_expr, struct SimpleCtype * type) {
   struct Cexpr * res = (struct Cexpr *) malloc(sizeof(struct Cexpr));
   res->t = C_INDEX;
   res->d.C_INDEX.arr_expr = arr_expr;
   res->d.C_INDEX.inner_expr = inner_expr;
   res->type = type;
   return res;
}

struct Cexpr * CexprCall(struct Cexpr * func, struct CexprList * args_exprs, struct SimpleCtype * type, struct VirtArg * vargs, char *spec_name, struct StringList * scopes) {
   struct Cexpr * res = (struct Cexpr *) malloc(sizeof(struct Cexpr));
   res->t = C_CALL;
   res->d.C_CALL.func = func;
   res->d.C_CALL.args_exprs = args_exprs;
   res->d.C_CALL.vargs = vargs;
   res->d.C_CALL.spec_name = spec_name;
   res->type = type;
   res->d.C_CALL.scopes = scopes;
   return res;
}

struct Cexpr * CexprTernary(struct Cexpr * cond, struct Cexpr * true_expr, struct Cexpr * false_expr, struct SimpleCtype * type) {
   struct Cexpr * res = (struct Cexpr *) malloc(sizeof(struct Cexpr));
   res->t = C_TERNARY;
   res->d.C_TERNARY.cond = cond;
   res->d.C_TERNARY.true_expr = true_expr;
   res->d.C_TERNARY.false_expr = false_expr;
   res->type = type;
   return res;
}

struct Cexpr * CexprDeepCopy(struct Cexpr * expr) {
   switch (expr->t) {
      case C_CONST:
         return CexprConst(expr->d.C_CONST.number, SimpleCtypeDeepCopy(expr->type));
      case C_VAR:
         return CexprVar(expr->d.C_VAR.id, SimpleCtypeDeepCopy(expr->type));
      case C_DEREF:
         return CexprDeref(CexprDeepCopy(expr->d.C_DEREF.expr), SimpleCtypeDeepCopy(expr->type));
      case C_ADDROF:
         return CexprAddrof(CexprDeepCopy(expr->d.C_ADDROF.expr), SimpleCtypeDeepCopy(expr->type));
      case C_UNOP:
         return CexprUnop(expr->d.C_UNOP.op, CexprDeepCopy(expr->d.C_UNOP.expr), SimpleCtypeDeepCopy(expr->type));
      case C_BINOP:
         return CexprBinop(expr->d.C_BINOP.op, CexprDeepCopy(expr->d.C_BINOP.expr1), CexprDeepCopy(expr->d.C_BINOP.expr2), SimpleCtypeDeepCopy(expr->type));
      case C_CAST:
         return CexprCast(CexprDeepCopy(expr->d.C_CAST.expr), SimpleCtypeDeepCopy(expr->type));
      case C_STRUCTFIELD:
         return CexprStructfield(CexprDeepCopy(expr->d.C_STRUCTFIELD.expr), expr->d.C_STRUCTFIELD.field_id, SimpleCtypeDeepCopy(expr->type));
      case C_UNIONFIELD:
         return CexprUnionfield(CexprDeepCopy(expr->d.C_UNIONFIELD.expr), expr->d.C_UNIONFIELD.field_id, SimpleCtypeDeepCopy(expr->type));
      case C_SIZEOF:
         return CexprSizeof(SimpleCtypeDeepCopy(expr->d.C_SIZEOF.inner_type), SimpleCtypeDeepCopy(expr->type));
      case C_INDEX:
         return CexprIndex(CexprDeepCopy(expr->d.C_INDEX.arr_expr), CexprDeepCopy(expr->d.C_INDEX.inner_expr), SimpleCtypeDeepCopy(expr->type));
      case C_CALL:
         return CexprCall(CexprDeepCopy(expr->d.C_CALL.func), CexprListDeepCopy(expr->d.C_CALL.args_exprs), SimpleCtypeDeepCopy(expr->type), VirtArgDeepCopy(expr->d.C_CALL.vargs), expr->d.C_CALL.spec_name, expr->d.C_CALL.scopes);
      case C_TERNARY:
         return CexprTernary(CexprDeepCopy(expr->d.C_TERNARY.cond), CexprDeepCopy(expr->d.C_TERNARY.true_expr), CexprDeepCopy(expr->d.C_TERNARY.false_expr), SimpleCtypeDeepCopy(expr->type));
      default:
         fprintf(stderr, "Error: unknown Cexpr type %d\n", expr->t);
         exit(1);
   }
}

void CexprFree(struct Cexpr *expr) {
   if (expr == NULL) return;
   switch (expr->t) {
      case C_CONST:
         break;
      case C_VAR:
         break;
      case C_DEREF:
         CexprFree(expr->d.C_DEREF.expr);
         break;
      case C_ADDROF:
         CexprFree(expr->d.C_ADDROF.expr);
         break;
      case C_UNOP:
         CexprFree(expr->d.C_UNOP.expr);
         break;
      case C_BINOP:
         CexprFree(expr->d.C_BINOP.expr1);
         CexprFree(expr->d.C_BINOP.expr2);
         break;
      case C_CAST:
         CexprFree(expr->d.C_CAST.expr);
         break;
      case C_STRUCTFIELD:
         CexprFree(expr->d.C_STRUCTFIELD.expr);
         break;
      case C_UNIONFIELD:
         CexprFree(expr->d.C_UNIONFIELD.expr);
         break;
      case C_SIZEOF:
         break;
      case C_INDEX:
         CexprFree(expr->d.C_INDEX.arr_expr);
         CexprFree(expr->d.C_INDEX.inner_expr);
         break;
      case C_CALL:
         CexprFree(expr->d.C_CALL.func);
         CexprListFree(expr->d.C_CALL.args_exprs);
         break;
      case C_TERNARY:
         CexprFree(expr->d.C_TERNARY.cond);
         CexprFree(expr->d.C_TERNARY.true_expr);
         CexprFree(expr->d.C_TERNARY.false_expr);
         break;
   }
   SimpleCtypeFree(expr->type);
   free(expr);
}

DEFINE_LIST(CexprList, struct Cexpr *, data)

void CexprListNodeFree(struct CexprListNode *node) {
   CexprFree(node->data);
   free(node);
}

struct CexprListNode *CexprListNodeDeepCopy(struct CexprListNode *node) {
   if (node == NULL) return NULL;
   struct CexprListNode *res = (struct CexprListNode *) malloc(sizeof(struct CexprListNode));
   res->data = CexprDeepCopy(node->data);
   res->next = node->next;
   return res;
}