#include <stddef.h>
#include <stdlib.h>
#include "PartialStmt.h"

struct CSimpleCommand * CSimpleCommandSkip() {
   struct CSimpleCommand * comd = (struct CSimpleCommand *) malloc(sizeof(struct CSimpleCommand));
   comd->t = C_Skip;
   return comd;
}

struct CSimpleCommand * CSimpleCommandAssign(enum AssignType assign_type, struct Cexpr * expr1, struct Cexpr * expr2) {
   struct CSimpleCommand * comd = (struct CSimpleCommand *) malloc(sizeof(struct CSimpleCommand));
   comd->t = C_Assign;
   comd->d.C_Assign.assign_type = assign_type;
   comd->d.C_Assign.expr1 = expr1;
   comd->d.C_Assign.expr2 = expr2;
   return comd;
}

struct CSimpleCommand * CSimpleCommandIncdec(enum IncDecType incdec_type, struct Cexpr * expr) {
   struct CSimpleCommand * comd = (struct CSimpleCommand *) malloc(sizeof(struct CSimpleCommand));
   comd->t = C_Incdec;
   comd->d.C_Incdec.incdec_type = incdec_type;
   comd->d.C_Incdec.expr = expr;
   return comd;
}

struct CSimpleCommand * CSimpleCommandCompute(struct Cexpr * expr) {
   struct CSimpleCommand * comd = (struct CSimpleCommand *) malloc(sizeof(struct CSimpleCommand));
   comd->t = C_Compute;
   comd->d.C_Compute.expr = expr;
   return comd;
}

struct CSimpleCommand * CSimpleCommandDeepCopy(struct CSimpleCommand * comd) {
   switch (comd->t) {
      case C_Skip:
         return CSimpleCommandSkip();
      case C_Assign:
         return CSimpleCommandAssign(comd->d.C_Assign.assign_type, CexprDeepCopy(comd->d.C_Assign.expr1), CexprDeepCopy(comd->d.C_Assign.expr2));
      case C_Incdec:
         return CSimpleCommandIncdec(comd->d.C_Incdec.incdec_type, CexprDeepCopy(comd->d.C_Incdec.expr));
      case C_Compute:
         return CSimpleCommandCompute(CexprDeepCopy(comd->d.C_Compute.expr));
      default:
         fprintf(stderr, "Error: unknown CSimpleCommand type %d\n", comd->t);
         exit(1);
   }
   return NULL;
}

void CSimpleCommandFree(struct CSimpleCommand * comd) {
   if (comd == NULL) return;
   switch (comd->t) {
      case C_Skip:
         break;
      case C_Assign:
         CexprFree(comd->d.C_Assign.expr1);
         CexprFree(comd->d.C_Assign.expr2);
         break;
      case C_Incdec:
         CexprFree(comd->d.C_Incdec.expr);
         break;
      case C_Compute:
         CexprFree(comd->d.C_Compute.expr);
         break;
   }
   free(comd);
}

struct PSVarDef * PSVarDefNew(int id, struct Cexpr * expr, struct SimpleCtype * type) {
   struct PSVarDef * vardef = (struct PSVarDef *) malloc(sizeof(struct PSVarDef));
   vardef->id = id;
   vardef->expr = expr;
   vardef->type = type;
   return vardef;
}

void PSVarDefFree(struct PSVarDef * vardef) {
   if (vardef == NULL) return;
   CexprFree(vardef->expr);
   free(vardef);
}

struct PartialStmt* PartialStmtSimple(struct CSimpleCommand * comd) {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_simple;
   ps->d.PS_simple.comd = comd;
   return ps;
}

struct PartialStmt* PartialStmtBreak() {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_break;
   return ps;
}

struct PartialStmt* PartialStmtContinue() {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_continue;
   return ps;
}

struct PartialStmt* PartialStmtReturn(struct Cexpr * ret_expr, struct StringList *scopes) {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_return;
   ps->d.PS_return.ret_expr = ret_expr;
   ps->d.PS_return.scopes = scopes;
   return ps;
}

struct PartialStmt* PartialStmtWhileCondition(struct Cexpr * condition, struct StringList *scopes) {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_while_condition;
   ps->d.PS_while_condition.condition = condition;
   ps->d.PS_while_condition.scopes = scopes;
   return ps;
}

struct PartialStmt* PartialStmtIfCondition(struct Cexpr * condition) {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_if_condition;
   ps->d.PS_if_condition.condition = condition;
   return ps;
}

struct PartialStmt* PartialStmtElse() {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_else;
   return ps;
}

struct PartialStmt* PartialStmtDoWhileCondition(struct Cexpr * condition,
                                                struct AsrtList *inv,
                                                int inv_is_partial,
                                                struct StringList *scopes) {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_do_while_condition;
   ps->d.PS_do_while_condition.condition = condition;
   ps->d.PS_do_while_condition.inv = inv;
   ps->d.PS_do_while_condition.inv_is_partial = inv_is_partial;
   ps->d.PS_do_while_condition.scopes = scopes;
   return ps;
}

struct PartialStmt* PartialStmtBlockBegin() {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_block_begin;
   return ps;
}

struct PartialStmt* PartialStmtBlockEnd() {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_block_end;
   return ps;
}

struct PartialStmt* PartialStmtDo() {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_do;
   return ps;
}

struct PartialStmt* PartialStmtFor(struct CSimpleCommand * c1,
                                   struct Cexpr * c2,
                                   struct CSimpleCommand * c3,
                                   struct AsrtList *inv,
                                   int inv_is_partial,
                                   struct StringList *scopes) {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_for;
   ps->d.PS_for.c1 = c1;
   ps->d.PS_for.c2 = c2;
   ps->d.PS_for.c3 = c3;
   ps->d.PS_for.inv = inv;
   ps->d.PS_for.inv_is_partial = inv_is_partial;
   ps->d.PS_for.scopes = scopes;
   return ps;
}

struct PartialStmt* PartialStmtSwitch(struct Cexpr * expr) {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_switch;
   ps->d.PS_switch.expr = expr;
   return ps;
}

struct PartialStmt* PartialStmtFstCase(struct Cexpr * expr) {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_fst_case;
   ps->d.PS_fst_case.expr = expr;
   return ps;
}

struct PartialStmt* PartialStmtOtherCase(struct Cexpr * expr) {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_other_case;
   ps->d.PS_other_case.expr = expr;
   return ps;
}

struct PartialStmt* PartialStmtDefault() {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_default;
   return ps;
}

struct PartialStmt* PartialStmtInv(struct AsrtList * asrt, int is_partial, struct StringList *scopes) {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_inv;
   ps->d.PS_inv.is_partial = is_partial;
   ps->d.PS_inv.asrt = asrt;
   ps->d.PS_inv.scopes = scopes;
   return ps;
}

struct PartialStmt* PartialStmtAssert(struct AsrtList * asrt, int is_partial, struct StringList *scopes) {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_assert;
   ps->d.PS_assert.asrt = asrt;
   ps->d.PS_assert.is_partial = is_partial;
   ps->d.PS_assert.scopes = scopes;
   return ps;
}

struct PartialStmt* PartialStmtWi(struct func_spec * specs, struct StringList *pre_scopes, struct StringList *post_scopes) {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_wi;
   ps->d.PS_wi.specs = specs;
   ps->d.PS_wi.pre_scopes = pre_scopes;
   ps->d.PS_wi.post_scopes = post_scopes;
   return ps;
}

struct PartialStmt* PartialStmtDoStrategy(char *name) {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_do_strategy;
   ps->d.PS_do_strategy.name = name;
   return ps;
}

struct PartialStmt* PartialStmtVarDef(struct PSVarDefList * vars) {
   struct PartialStmt * ps = (struct PartialStmt *) malloc(sizeof(struct PartialStmt));
   ps->t = PS_vardef;
   ps->d.PS_vardef.vars = vars;
   return ps;
}

struct PartialStmt* PartialStmtSetnext(struct PartialStmt * ps, struct PartialStmt * next) {
   ps->next = next;
   return ps;
}

int IsRepeatHeader(struct PartialStmt * ps) {
   if (ps->t == PS_do || ps->t == PS_for || ps->t == PS_while_condition) {
      return 1;
   } else {
      return 0;
   }
}

struct PSVarDefList * PSVarDefListNil() {
   return NULL;
}

struct PSVarDefList * PSVarDefListCons(struct PSVarDef * data, struct PSVarDefList * list) {
   struct PSVarDefList * res = (struct PSVarDefList *) malloc(sizeof(struct PSVarDefList));
   res->data = data;
   res->next = NULL;
   if (list == NULL) {
      return res;
   } else {
      res->next = list;
      return res;
   }
}

struct PSVarDefList * PSVarDefListLink(struct PSVarDefList * left, struct PSVarDefList * right) {
   if (left == NULL) return right;
   if (right == NULL) return left;
   struct PSVarDefList * tmp = left;
   while (tmp->next != NULL) {
      tmp = tmp->next;
   }
   tmp->next = right;
   return left;
}

void PSVarDefListFree(struct PSVarDefList * list) {
   if (list == NULL) return;
   PSVarDefListFree(list->next);
   PSVarDefFree(list->data);
   free(list);
}

DEFINE_LIST(PartialStmtList, struct PartialStmt *, data)

struct PartialStmtListNode* PartialStmtListNodeDeepCopy(struct PartialStmtListNode *node) {
   fprintf(stderr, "PartialStmtListNodeDeepCopy not implemented yet\n");
   exit(1);
}

void PartialStmtFree(struct PartialStmt *ps) {
   if (ps == NULL) return;
   switch(ps->t) {
      case PS_simple:
         CSimpleCommandFree(ps->d.PS_simple.comd);
         break;
      case PS_return:
         CexprFree(ps->d.PS_return.ret_expr);
         break;
      case PS_while_condition:
         CexprFree(ps->d.PS_while_condition.condition);
         break;
      case PS_if_condition:
         CexprFree(ps->d.PS_if_condition.condition);
         break;
      case PS_do_while_condition:
         CexprFree(ps->d.PS_do_while_condition.condition);
         break;
      case PS_for:
         CSimpleCommandFree(ps->d.PS_for.c1);
         CexprFree(ps->d.PS_for.c2);
         CSimpleCommandFree(ps->d.PS_for.c3);
         break;
      case PS_switch:
         CexprFree(ps->d.PS_switch.expr);
         break;
      case PS_fst_case:
         CexprFree(ps->d.PS_fst_case.expr);
         break;
      case PS_other_case:
         CexprFree(ps->d.PS_other_case.expr);
         break;
      case PS_inv:
         AsrtListFree(ps->d.PS_inv.asrt);
         break;
      case PS_assert:
         AsrtListFree(ps->d.PS_assert.asrt);
         break;
      case PS_wi:
         break;
      case PS_vardef:
         PSVarDefListFree(ps->d.PS_vardef.vars);
         break;
      default:
         break;
   }
   free(ps);
}

void PartialStmtListNodeFree(struct PartialStmtListNode *node) {
   if (node == NULL) return;
   PartialStmtFree(node->data);
   free(node);
}
