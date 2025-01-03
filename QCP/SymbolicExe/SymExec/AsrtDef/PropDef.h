#ifndef PROPDEF_INCLUDED
#define PROPDEF_INCLUDED

#include <stdlib.h>
#include "ExprValDef.h"

enum PropUOP { // unary op
   PROP_NOT,
};

enum PropBinOP { // binary op
   PROP_AND,  // P && Q
   PROP_OR,   // P || Q
   PROP_IMPLY, // P -> Q
   PROP_IFF,   // P <-> Q
};

enum PropPtrOP {  // Unary_expr_op in Annotated_SimpleC
   PROP_NOT_NULL,
   PROP_MAYBE_NULL,
   PROP_IS_NULL,
};

enum PropCompOp { // Binary_expr_op in Annotated_SimpleC
   PROP_LE,
   PROP_GE,
   PROP_LT,
   PROP_GT,
   PROP_EQ,
   PROP_NEQ,
};

enum PropQuantifier {
   PROP_FORALL,
   PROP_EXISTS,
};

enum PropType {
   T_PROP_TRUE,
   T_PROP_FALSE,
   T_PROP_UNARY,
   T_PROP_BINARY,
   T_PROP_PTR,
   T_PROP_COMPARE,
   T_PROP_QUANTIFIER,
   T_PROP_OTHER,
};

struct Proposition {
   enum PropType t;
   union {
      struct {} PROP_TRUE;
      struct {} PROP_FALSE;
      struct { enum PropUOP op; struct Proposition *prop; } UNARY;
      struct { enum PropBinOP op; struct Proposition *prop1, *prop2; } BINARY;
      struct { enum PropPtrOP op; struct ExprVal *expr; } PTR;
      struct { enum PropCompOp op; struct ExprVal *expr1, *expr2;} COMPARE;
      struct { enum PropQuantifier op; int ident; struct Proposition * prop; } QUANTIFIER;
      struct { int predicate; struct PolyTypeList *types; struct ExprValList * args; } OTHER;
   }d; 
};

struct PropList {
   struct Proposition * head;
   struct PropList *next;
};

struct Proposition * PropTrue();
struct Proposition * PropFalse();
struct Proposition * PropUnary(enum PropUOP op, struct Proposition * prop);
struct Proposition * PropBinary(enum PropBinOP op, struct Proposition * prop1, struct Proposition * prop2);
struct Proposition * PropPtr(enum PropPtrOP op, struct ExprVal * expr);
struct Proposition * PropCompare(enum PropCompOp op, struct ExprVal * expr1, struct ExprVal * expr2);
struct Proposition * PropQuantifier(enum PropQuantifier op, int ident, struct Proposition * prop);
struct Proposition * PropOther(int predicate, struct PolyTypeList *types, struct ExprValList * args);

struct PropList* PropListNil();
struct PropList* PropListCons(struct Proposition * prop, struct PropList * next);
struct PropList* PropListLink(struct PropList * list1, struct PropList * list2);
struct PropList* PropListRemove(struct PropList * pos, struct PropList * list);

int PropositionCheckEqual(struct Proposition * prop1, struct Proposition * prop2);
int PropListCheckEqual(struct PropList * list1, struct PropList * list2);

struct Proposition * PropSubst(struct Proposition * prop, struct ExprVal * pre, struct ExprVal * post);
struct Proposition * PropSubstPolyType(struct Proposition * prop, struct PolyType * pre, struct PolyType * post);
struct PropList * PropListSubst(struct PropList * prop_list, struct ExprVal * pre, struct ExprVal * post);
struct PropList * PropListSubstPolyType(struct PropList * prop_list, struct PolyType * pre, struct PolyType * post);

int Used_ExprVal_in_Prop(struct Proposition *expr, struct ExprVal *goal);

struct Proposition * PropDeepCopy(struct Proposition * prop);
struct PropList * PropListDeepCopy(struct PropList * prop_list);

void PropFree(struct Proposition * prop);
void PropListFree(struct PropList * prop_list);

#endif
