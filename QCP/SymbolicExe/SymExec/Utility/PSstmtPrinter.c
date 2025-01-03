#include "PSstmtPrinter.h"
#include "InnerAsrtPrinter.h"

void PrintAsgnOp(enum AssignType op) {
   switch (op) {
   case T_ASSIGN:
      printf("=");
      break;
   case T_ADD_ASSIGN:
      printf("+=");
      break;
   case T_SUB_ASSIGN:
      printf("-=");
      break;
   case T_MUL_ASSIGN:
      printf("*=");
      break;
   case T_DIV_ASSIGN:
      printf("/=");
      break;
   case T_MOD_ASSIGN:
      printf("%%=");
      break;
   case T_BAND_ASSIGN:
      printf("&=");
      break;
   case T_BOR_ASSIGN:
      printf("|=");
      break;
   case T_XOR_ASSIGN:
      printf("^=");
      break;
   case T_SHL_ASSIGN:
      printf("<<=");
      break;
   case T_SHR_ASSIGN:
      printf(">>=");
      break;
   default:
      break;
   }
}

void PrintPartialSimple(struct CSimpleCommand *comd, int end_of_line, struct environment * env) {
   switch(comd->t) {
      case C_Skip:
         break;
      case C_Assign:
         PrintCexpr(comd->d.C_Assign.expr1, env);
         printf(" ");
         PrintAsgnOp(comd->d.C_Assign.assign_type);
         printf(" ");
         PrintCexpr(comd->d.C_Assign.expr2, env);
         break;
      case C_Incdec:
         switch (comd->d.C_Incdec.incdec_type) {
            case T_INC_F:
               printf("++");
               PrintCexpr(comd->d.C_Incdec.expr, env);
               break;
            case T_INC_B:
               PrintCexpr(comd->d.C_Incdec.expr, env);
               printf("++");
               break;
            case T_DEC_F:
               printf("--");
               PrintCexpr(comd->d.C_Incdec.expr, env);
               break;
            case T_DEC_B:
               PrintCexpr(comd->d.C_Incdec.expr, env);
               printf("--");
               break;
         }
         break;
      case C_Compute:
         PrintCexpr(comd->d.C_Compute.expr, env);
         break;
   }
   if (end_of_line) puts(";");
}

void PrintPartialStmt(struct PartialStmt * stmt, struct environment * env) {
   switch (stmt->t) {
      case PS_simple:
         PrintPartialSimple(stmt->d.PS_simple.comd, 1, env);
         break;
      case PS_break:
         puts("break;");
         break;
      case PS_continue:
         puts("continue;");
         break;
      case PS_return:
         if (stmt->d.PS_return.ret_expr == NULL) {
            puts("return");
         } else {
            printf("return ");
            PrintCexpr(stmt->d.PS_return.ret_expr, env);
            puts(";");
         }
         break;
      case PS_while_condition:
         printf("while (");
         PrintCexpr(stmt->d.PS_while_condition.condition, env);
         printf(") {\n");
         break;
      case PS_if_condition:
         printf("if (");
         PrintCexpr(stmt->d.PS_if_condition.condition, env);
         printf(") {\n");
         break;
      case PS_else:
         puts("} else {");
         break;
      case PS_do_while_condition:
         printf("} while (");
         PrintCexpr(stmt->d.PS_do_while_condition.condition, env);
         printf(");\n");
         break;
      case PS_block_begin:
         puts("{");
         break;
      case PS_block_end:
         puts("}");
         break;
      case PS_do:
         puts("do {");
         break;
      case PS_for:
         printf("for (");
         PrintPartialSimple(stmt->d.PS_for.c1, 0, env);
         printf("; ");
         PrintCexpr(stmt->d.PS_for.c2, env);
         printf("; ");
         PrintPartialSimple(stmt->d.PS_for.c3, 0, env);
         printf(") {\n");
         break;
      case PS_switch:
         printf("switch (");
         PrintCexpr(stmt->d.PS_switch.expr, env);
         printf(") {\n");
         break;
      case PS_fst_case:
         printf("case ");
         PrintCexpr(stmt->d.PS_fst_case.expr, env);
         printf(": {\n");
         break;
      case PS_other_case:
         printf("} case ");
         PrintCexpr(stmt->d.PS_other_case.expr, env);
         printf(": {\n");
         break;
      case PS_default:
         puts("} default: {\n");
         break;
      case PS_inv:
         puts("Get Inv:");
         PrintAsrtList(stmt->d.PS_inv.asrt, env);
         break;
      case PS_assert:
         puts("Get Assertion:");
         PrintAsrtList(stmt->d.PS_assert.asrt, env);
         break;
      case PS_wi:
         for (struct func_spec * i = stmt->d.PS_wi.specs; i != NULL; i = i->next) {
            printf("With: ");
            PrintExistList(i->with, env);
            PrintAsrtList(i->pre, env);
            puts("Which implies:");
            PrintAsrtList(i->post, env);
         }
         break;
      case PS_vardef: {
         struct PSVarDefList * i;
         i = stmt->d.PS_vardef.vars;
         while (i != NULL) {
            struct prog_var_info * info = find_prog_var_by_id(i->data->id, &env->persist);
            PrintSimpleCtype(i->data->type, env);
            printf(" %s(id = %d)", info->name, info->id);
            if (i->data->expr != NULL) {
               printf("= ");
               PrintCexpr(i->data->expr, env);
            }
            if (i->next != NULL) printf(", ");
            else printf(";\n");
            i = i->next;
         }
         break;
      }
      case PS_do_strategy:
         printf("/*@ do %s */\n", stmt->d.PS_do_strategy.name);
   }
}

void PrintPartialStmtList(struct PartialStmtList * stmts, struct environment * env) {
   struct PartialStmtListNode * i;
   for (i = stmts->head; i != NULL; i = i->next) {
      PrintPartialStmt(i->data, env);
   }
}
