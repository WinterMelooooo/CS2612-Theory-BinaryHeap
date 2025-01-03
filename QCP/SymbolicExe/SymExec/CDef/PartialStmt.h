#ifndef PartialStmt_INCLUDED
#define PartialStmt_INCLUDED
#include "../../compiler/env.h"
#include "../AsrtDef/ExprValDef.h"
#include "Cexpr.h"

enum CSimpleCommandType {
   C_Skip, C_Assign, C_Incdec, C_Compute
};

struct CSimpleCommand {
   enum CSimpleCommandType t;
   union {
      struct {} C_SKIP;
      struct { enum AssignType assign_type; struct Cexpr * expr1, *expr2;  } C_Assign;
      struct { enum IncDecType incdec_type; struct Cexpr * expr; } C_Incdec;
      struct { struct Cexpr * expr; } C_Compute;
   }d;
};

struct CSimpleCommand * CSimpleCommandSkip();
struct CSimpleCommand * CSimpleCommandAssign(enum AssignType assign_type, struct Cexpr * expr1, struct Cexpr * expr2);
struct CSimpleCommand * CSimpleCommandIncdec(enum IncDecType incdec_type, struct Cexpr * expr);
struct CSimpleCommand * CSimpleCommandCompute(struct Cexpr * expr);
struct CSimpleCommand * CSimpleCommandDeepCopy(struct CSimpleCommand * comd);
void CSimpleCommandFree(struct CSimpleCommand * comd);

struct PSVarDef {
   int id;
   struct Cexpr * expr;
   struct SimpleCtype * type;
};

struct PSVarDef * PSVarDefNew(int id, struct Cexpr * expr, struct SimpleCtype * type);
void PSVarDefFree(struct PSVarDef * vardef);

struct PSVarDefList {
   struct PSVarDef * data;
   struct PSVarDefList * next;
};

struct PSVarDefList * PSVarDefListNil();
struct PSVarDefList * PSVarDefListCons(struct PSVarDef * data, struct PSVarDefList * list);
struct PSVarDefList * PSVarDefListLink(struct PSVarDefList * left, struct PSVarDefList * right);
void PSVarDefListFree(struct PSVarDefList * list);

enum PartialStmtType {
   PS_simple,
   PS_break,
   PS_continue,
   PS_return,
   PS_while_condition,
   PS_if_condition,
   PS_else,
   PS_do_while_condition,
   PS_block_begin,
   PS_block_end,
   PS_do,
   PS_for,
   PS_switch,
   PS_fst_case,
   PS_other_case,
   PS_default,
   PS_inv,
   PS_assert,
   PS_wi,
   PS_do_strategy,
   PS_vardef
};

struct PartialStmt {
   enum PartialStmtType t;
   union {
      struct { struct CSimpleCommand * comd; } PS_simple;
      struct {} PS_break;
      struct {} PS_continue;
      struct { struct Cexpr * ret_expr; struct StringList *scopes; } PS_return;
      struct { struct Cexpr * condition;
               struct StringList *scopes;  } PS_while_condition;  // while (b) {
      struct { struct Cexpr * condition; } PS_if_condition;       // if (b) {
      struct {} PS_else;                                          // } else {
      struct { struct Cexpr * condition;
               struct AsrtList *inv;
               int inv_is_partial;
               struct StringList *scopes; } PS_do_while_condition;       // } while(b)
      struct {} PS_block_begin;
      struct {} PS_block_end;
      struct {} PS_do;                                            // do {
      struct { struct CSimpleCommand * c1;
               struct Cexpr * c2;
               struct CSimpleCommand * c3;
               struct AsrtList *inv;
               int inv_is_partial;
               struct StringList *scopes; } PS_for;                      // for (c1; c2; c3) {
      struct { struct Cexpr * expr; } PS_switch;                  // switch (b) {
      struct { struct Cexpr * expr;  } PS_fst_case;               // case b : {
      struct { struct Cexpr * expr;  } PS_other_case;             // } case b : {
      struct {} PS_default;                                       // } default : {
      struct { struct AsrtList * asrt; int is_partial; struct StringList *scopes; } PS_inv;
      struct { struct AsrtList * asrt; int is_partial; struct StringList *scopes; } PS_assert;
      struct { struct func_spec * specs; struct StringList *pre_scopes, *post_scopes; } PS_wi;   // which implies
      struct { char *name; } PS_do_strategy;
      struct { struct PSVarDefList * vars; } PS_vardef;
   }d;
   struct PartialStmt * next;
};

struct PartialStmt* PartialStmtSimple(struct CSimpleCommand * comd);
struct PartialStmt* PartialStmtBreak();
struct PartialStmt* PartialStmtContinue();
struct PartialStmt* PartialStmtReturn(struct Cexpr * ret_expr, struct StringList *scopes);
struct PartialStmt* PartialStmtWhileCondition(struct Cexpr * condition, struct StringList *scopes);
struct PartialStmt* PartialStmtIfCondition(struct Cexpr * condition);
struct PartialStmt* PartialStmtElse();
struct PartialStmt* PartialStmtDoWhileCondition(struct Cexpr * condition,
                                                struct AsrtList *inv,
                                                int inv_is_partial,
                                                struct StringList *scopes);
struct PartialStmt* PartialStmtBlockBegin();
struct PartialStmt* PartialStmtBlockEnd();
struct PartialStmt* PartialStmtDo();
struct PartialStmt* PartialStmtFor(struct CSimpleCommand * c1,
                                   struct Cexpr * c2,
                                   struct CSimpleCommand * c3,
                                   struct AsrtList *inv,
                                   int inv_is_partial,
                                   struct StringList *scopes);
struct PartialStmt* PartialStmtSwitch(struct Cexpr * expr);
struct PartialStmt* PartialStmtFstCase(struct Cexpr * expr);
struct PartialStmt* PartialStmtOtherCase(struct Cexpr * expr);
struct PartialStmt* PartialStmtDefault();
struct PartialStmt* PartialStmtInv(struct AsrtList * asrt, int is_partial, struct StringList *scopes);
struct PartialStmt* PartialStmtAssert(struct AsrtList * asrt, int is_partial, struct StringList *scopes);
struct PartialStmt* PartialStmtWi(struct func_spec * specs, struct StringList *pre_scopes, struct StringList *post_scopes);
struct PartialStmt* PartialStmtDoStrategy(char *name);
struct PartialStmt* PartialStmtVarDef(struct PSVarDefList * vars);
struct PartialStmt* PartialStmtSetnext(struct PartialStmt * ps, struct PartialStmt * next);
int IsRepeatHeader(struct PartialStmt * ps);
void PartialStmtFree(struct PartialStmt *ps);

DECLARE_LIST(PartialStmtList, struct PartialStmt *, data)

#endif
