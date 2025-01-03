#ifndef CEXPR_INCLUDED
#define CEXPR_INCLUDED
#include "../Utility/List.h"
#include "../../compiler/lang.h"
#include "../AsrtDef/ExprValDef.h"

enum CexprType {
   C_CONST,
   C_VAR,
   C_DEREF,
   C_ADDROF,
   C_UNOP,
   C_BINOP,
   C_CAST,
   C_STRUCTFIELD,
   C_UNIONFIELD,
   C_SIZEOF,
   C_INDEX,
   C_CALL,
   C_TERNARY
};

struct CexprList;

DECLARE_LIST2(TypeArgList, char *, name, struct PolyType *, type)
DECLARE_LIST3(VirtArgList, char *, name, struct ExprVal *, val, struct PolyType *, type)

struct VirtArg {
   struct func_spec *ctx;
   struct TypeArgList * type_args;
   struct VirtArgList * args;
};

struct Cexpr {
   enum CexprType t;
   struct SimpleCtype * type;
   union {
      struct { unsigned long long number;  } C_CONST;
      struct { int id; } C_VAR;
      struct { struct Cexpr * expr; } C_DEREF;
      struct { struct Cexpr * expr; } C_ADDROF;
      struct { enum UnOpType op; struct Cexpr * expr; } C_UNOP;
      struct { enum BinOpType op; struct Cexpr * expr1; struct Cexpr * expr2; } C_BINOP;
      struct { struct Cexpr * expr; } C_CAST;
      struct { struct Cexpr * expr; int field_id; } C_STRUCTFIELD;
      struct { struct Cexpr * expr; int field_id; } C_UNIONFIELD;
      struct { struct SimpleCtype * inner_type; } C_SIZEOF;
      struct { struct Cexpr * arr_expr; struct Cexpr * inner_expr; } C_INDEX;
      struct { struct Cexpr * func; struct CexprList * args_exprs; 
               struct VirtArg * vargs; char *spec_name; struct StringList * scopes; } C_CALL;
      struct { struct Cexpr * cond; struct Cexpr * true_expr; struct Cexpr * false_expr; } C_TERNARY;
   }d;
};

struct VirtArg * CreateVirtArg(struct func_spec * ctx, struct TypeArgList * type_args, struct VirtArgList * args);
struct VirtArg * VirtArgDeepCopy(struct VirtArg * vargs);
void VirtArgFree(struct VirtArg * vargs);
struct Cexpr * CexprConst(unsigned long long number, struct SimpleCtype * type);
struct Cexpr * CexprVar(int id, struct SimpleCtype * type);
struct Cexpr * CexprDeref(struct Cexpr * expr, struct SimpleCtype * type);
struct Cexpr * CexprAddrof(struct Cexpr * expr, struct SimpleCtype * type);
struct Cexpr * CexprUnop(enum UnOpType op, struct Cexpr * expr, struct SimpleCtype * type);
struct Cexpr * CexprBinop(enum BinOpType op, struct Cexpr * expr1, struct Cexpr * expr2, struct SimpleCtype * type);
struct Cexpr * CexprCast(struct Cexpr * expr, struct SimpleCtype * type);
struct Cexpr * CexprStructfield(struct Cexpr * expr, int field_id, struct SimpleCtype * type);
struct Cexpr * CexprUnionfield(struct Cexpr * expr, int field_id, struct SimpleCtype * type);
struct Cexpr * CexprSizeof(struct SimpleCtype * inner_type, struct SimpleCtype * type);
struct Cexpr * CexprIndex(struct Cexpr * arr_expr, struct Cexpr * inner_expr, struct SimpleCtype * type);
struct Cexpr * CexprCall(struct Cexpr * func, struct CexprList * args_exprs, struct SimpleCtype * type, 
                         struct VirtArg * vargs, char *spec_name, struct StringList * scopes);
struct Cexpr * CexprTernary(struct Cexpr * cond, struct Cexpr * true_expr, struct Cexpr * false_expr, struct SimpleCtype * type);
struct Cexpr * CexprDeepCopy(struct Cexpr * expr);
void CexprFree(struct Cexpr *expr);

DECLARE_LIST(CexprList, struct Cexpr *, data)

#endif
