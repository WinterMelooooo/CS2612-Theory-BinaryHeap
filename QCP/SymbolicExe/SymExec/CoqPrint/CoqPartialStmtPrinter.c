#include "CoqPrintTools.h"
#include "CoqCexprPrinter.h"
#include "CoqInnerAsrtPrinter.h"
#include "CoqPartialStmtPrinter.h"
#include "../Trans/StmtTrans.h"

void CoqCAssignTypePrinter(enum AssignType ty, FILE * fp) {
   switch (ty) {
      case T_ASSIGN:
         fprintf(fp, "O_ASSIGN");
         break;
      case T_ADD_ASSIGN:
         fprintf(fp, "O_PLUS_ASSIGN");
         break;
      case T_SUB_ASSIGN:
         fprintf(fp, "O_MINUS_ASSIGN");
         break;
      case T_MUL_ASSIGN:
         fprintf(fp, "O_MUL_ASSIGN");
         break;
      case T_DIV_ASSIGN:
         fprintf(fp, "O_DIV_ASSIGN");
         break;
      case T_MOD_ASSIGN:
         fprintf(fp, "O_MOD_ASSIGN");
         break;
      case T_BAND_ASSIGN:
         fprintf(fp, "O_AND_ASSIGN");
         break;
      case T_BOR_ASSIGN:
         fprintf(fp, "O_OR_ASSIGN");
         break;
      case T_XOR_ASSIGN:
         fprintf(fp, "O_XOR_ASSIGN");
         break;
      case T_SHL_ASSIGN:
         fprintf(fp, "O_SHL_ASSIGN");
         break;
      case T_SHR_ASSIGN:
         fprintf(fp, "O_SHR_ASSIGN");
         break;
   }
}

void CoqCIncDecTypePrinter (enum IncDecType ty, FILE * fp) {
   switch (ty) {
      case T_INC_F:
         fprintf(fp, "O_INCPRE");
         break;
      case T_INC_B:
         fprintf(fp, "O_INCPOST");
         break;
      case T_DEC_F:
         fprintf(fp, "O_DECPRE");
         break;
      case T_DEC_B:
         fprintf(fp, "O_DECPOST");
         break;
   }
}

void CoqCSimpleCommandPrinter(struct CSimpleCommand * comd, struct environment * env, FILE * fp) {
   fprintf(fp, "(");
   switch (comd->t) {
      case C_Skip:
         fprintf(fp, "C_skip");
         break;
      case C_Assign:
         fprintf(fp, "C_assign ");
         CoqCAssignTypePrinter(comd->d.C_Assign.assign_type, fp);
         fprintf(fp, " ");
         CoqCexprPrinter(comd->d.C_Assign.expr1, env, fp);
         fprintf(fp, " ");
         CoqCexprPrinter(comd->d.C_Assign.expr2, env, fp);
         break;
      case C_Incdec:
         fprintf(fp, "C_incdec ");
         CoqCIncDecTypePrinter(comd->d.C_Incdec.incdec_type, fp);
         fprintf(fp, " ");
         CoqCexprPrinter(comd->d.C_Incdec.expr, env, fp);
         break;
      case C_Compute:
         fprintf(fp, "C_compute ");
         CoqCexprPrinter(comd->d.C_Compute.expr, env, fp);
         break;
      default:
         fprintf(stderr, "CoqCSimpleCommandPrinter: unknown CSimpleCommand type\n");
         exit(1);
         break;
   }
   fprintf(fp, ")");
}

void CoqPartialStmtPrinter(struct PartialStmt* stmt, struct environment * env, FILE * fp) {
   fprintf(fp, "(");
   switch (stmt->t) {
      case PS_simple:
         fprintf(fp, "PS_simple ");
         CoqCSimpleCommandPrinter(stmt->d.PS_simple.comd, env, fp);
         break;
      case PS_break:
         fprintf(fp, "PS_break");
         break;
      case PS_continue:
         fprintf(fp, "PS_continue");
         break;
      case PS_return:
         if (stmt->d.PS_return.ret_expr == NULL) {
            fprintf(fp, "PS_return None");
         } else {
            fprintf(fp, "PS_return (Some ");
            CoqCexprPrinter(stmt->d.PS_return.ret_expr, env, fp);
            fprintf(fp, ")");
         }
         break;
      case PS_while_condition:
         fprintf(fp, "PS_while ");
         CoqCexprPrinter(stmt->d.PS_while_condition.condition, env, fp);
         break;
      case PS_if_condition:
         fprintf(fp, "PS_if ");
         CoqCexprPrinter(stmt->d.PS_if_condition.condition, env, fp);
         break;
      case PS_else:
         fprintf(fp, "PS_else");
         break;
      case PS_do_while_condition:
         fprintf(fp, "PS_do_while ");
         CoqCexprPrinter(stmt->d.PS_do_while_condition.condition, env, fp);
         break;
      case PS_block_begin:
         fprintf(fp, "PS_block_begin");
         break;
      case PS_block_end:
         fprintf(fp, "PS_block_end");
         break;
      case PS_do:
         fprintf(fp, "PS_do");
         break;
      case PS_for:
         fprintf(fp, "PS_for ");
         CoqCSimpleCommandPrinter(stmt->d.PS_for.c1, env, fp);
         fprintf(fp, " ");
         CoqCexprPrinter(stmt->d.PS_for.c2, env, fp);
         fprintf(fp, " ");
         CoqCSimpleCommandPrinter(stmt->d.PS_for.c3, env, fp);
         break;
      case PS_switch:
         fprintf(fp, "PS_switch ");
         CoqCexprPrinter(stmt->d.PS_switch.expr, env, fp);
         break;
      case PS_fst_case:
         fprintf(fp, "PS_fst_case ");
         CoqCexprPrinter(stmt->d.PS_fst_case.expr, env, fp);
         break;
      case PS_other_case:
         fprintf(fp, "PS_other_case ");
         CoqCexprPrinter(stmt->d.PS_other_case.expr, env, fp);
         break;
      case PS_default:
         fprintf(fp, "PS_default");
         break;
      case PS_inv:
         fprintf(fp, "PS_inv ");
         CoqInnerAsrtListPrinter(stmt->d.PS_inv.asrt, env, fp);
         break;
      case PS_assert:
         fprintf(fp, "PS_assert ");
         CoqInnerAsrtListPrinter(stmt->d.PS_assert.asrt, env, fp);
         break;
      case PS_vardef: {
         fprintf(fp, "PS_vardef ");
         struct PSVarDefList * vars = stmt->d.PS_vardef.vars;
         if (vars == NULL) {
            fprintf(fp, "nil");
         } else {
            fprintf(fp, "(");
            while (vars != NULL) {
               struct prog_var_info * var = find_prog_var_by_id(vars->data->id, &env->persist);
               fprintf(fp, "(");
               CoqPrintVarName(var->name, var->id, fp);
               fprintf(fp, ", ");
               if (vars->data->expr == NULL) {
                  fprintf(fp, "None");
               } else {
                  fprintf(fp, "Some ");
                  CoqCexprPrinter(vars->data->expr, env, fp);
               }
               fprintf(fp, ", ");
               CoqSimpleCtypePrinter(vars->data->type, env, fp);
               fprintf(fp, ")");
               vars = vars->next;
               if (vars != NULL) {
                  fprintf(fp, "::");
               } else {
                  fprintf(fp, "::nil)");
               }
            }
         }
         break;
      }
   }
   fprintf(fp, ")");
}

void CoqPartialStmtListPrinter(int id, struct PartialStmtList * stmt_list, struct environment * env, FILE * fp) {
   fprintf(fp, "Definition ps_stmt%d := ", id);
   if (stmt_list == NULL) {
      fprintf(fp, "nil");
      return;
   } else {
      fprintf(fp, "(");
      struct PartialStmtListNode * tmp = stmt_list->head;
      while (tmp != NULL) {
         CoqPartialStmtPrinter(tmp->data, env, fp);
         tmp = tmp->next;
         if (tmp != NULL) {
            fprintf(fp, "::");
         } else {
            fprintf(fp, "::nil)");
         }
      }
   }
}

void CoqPreConditionPrinter(int id, struct AsrtList * precond, struct environment * env, FILE * fp) {
   fprintf(fp, "Definition Pre%d := ", id);
   // CoqInnerAsrtListPrinter(precond, fp);
   CoqInnerAsrtPrinter(precond->head, env, fp);
   fprintf(fp, ".\n\n");
}

void CoqPostConditionPrinter(int id, struct AsrtList * postcond, struct environment * env, FILE * fp) {
   fprintf(fp, "Definition Post%d := ", id);
   CoqInnerAsrtListPrinter(postcond, env, fp);
}

void PSStmtPrint(struct environment *env, FILE *fp) {
   struct blist *it;
   int func_count = 0;
   for (it = env->persist.func.top; it != NULL; it = it->down) {
      struct func_info *info;
      info = it->val;
      if (info->defined == 0) continue;
      struct PartialStmtList * ps_stmt;
      ps_stmt = StmtTrans(info->body, env, 0);
      ++func_count;
      CoqPartialStmtListPrinter(func_count, ps_stmt, env, fp);
      fprintf(fp, ".\n\n");
   }
}