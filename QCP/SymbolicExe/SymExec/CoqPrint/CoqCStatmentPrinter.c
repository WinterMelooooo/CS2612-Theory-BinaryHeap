#include "CoqCStatmentPrinter.h"
#include "../AsrtDef/AssDef.h"
#include "../Trans/TypeTrans.h"
#include "../Utility/InnerAsrtCollector.h"
#include "CoqInnerAsrtPrinter.h"
#include "CoqPrintTools.h"
#include "CoqCexprPrinter.h"
#include <assert.h>

void CoqCSimpleStatementPrinter(struct simple_cmd * cmd, struct environment * env, FILE * fp) {
   fprintf(fp, "(");
   switch (cmd->t) {
   case T_COMPUTATION:
      fprintf(fp, "C_compute ");
      CoqASTExprPrinter(cmd->d.COMPUTATION.arg, env, fp);
      break;
   case T_ASGN:
      fprintf(fp, "C_assign ");
      switch (cmd->d.ASGN.op) {
         case T_ASSIGN:
            fprintf(fp, "O_ASSIGN ");
            break;
         case T_ADD_ASSIGN:
            fprintf(fp, "O_PLUS_ASSIGN ");
            break;
         case T_SUB_ASSIGN:
            fprintf(fp, "O_MINUS_ASSIGN ");
            break;
         case T_MUL_ASSIGN:
            fprintf(fp, "O_MUL_ASSIGN ");
            break;
         case T_DIV_ASSIGN:
            fprintf(fp, "O_DIV_ASSIGN ");
            break;
         case T_MOD_ASSIGN:
            fprintf(fp, "O_MOD_ASSIGN ");
            break;
         case T_BAND_ASSIGN:
            fprintf(fp, "O_AND_ASSIGN ");
            break;
         case T_BOR_ASSIGN:
            fprintf(fp, "O_OR_ASSIGN ");
            break;
         case T_XOR_ASSIGN:
            fprintf(fp, "O_XOR_ASSIGN ");
            break;
         case T_SHL_ASSIGN:
            fprintf(fp, "O_SHL_ASSIGN ");
            break;
         case T_SHR_ASSIGN:
            fprintf(fp, "O_SHR_ASSIGN ");
            break;
         default:
            fprintf(stderr, "Unknown assign type %s %d\n", __FILE__, __LINE__);
            break;
      }
      CoqASTExprPrinter(cmd->d.ASGN.left, env, fp);
      fprintf(fp, " ");
      CoqASTExprPrinter(cmd->d.ASGN.right, env, fp);
      break;
   case T_INCDEC:
      fprintf(fp, "C_incdec ");
      switch (cmd->d.INCDEC.op) {
         case T_INC_F:
            fprintf(fp, "O_INCPRE ");
            break;
         case T_INC_B:
            fprintf(fp, "O_INCPOST ");
            break;
         case T_DEC_F:
            fprintf(fp, "O_DECPRE ");
            break;
         case T_DEC_B:
            fprintf(fp, "O_DECPOST ");
            break;
         default:
            fprintf(stderr, "Unknown incdec type %s %d\n", __FILE__, __LINE__);
            break;
      }
      CoqASTExprPrinter(cmd->d.INCDEC.arg, env, fp);
      break;
      }
   fprintf(fp, ")");
}

void CoqCStatementPrinter(struct cmd * cmd, int print_annotation, struct environment * env, FILE * fp) {
   fprintf(fp, "(");
   if (cmd == NULL) {
      if (print_annotation) {
         fprintf(fp, "AC_simple ");
      } else {
         fprintf(fp, "C_simple ");
      }
      fprintf(fp, "C_skip");
      fprintf(fp, ")"); 
      return;
   }
   switch (cmd->t) {
      case T_VARDECL: {
         if (print_annotation) {
            fprintf(fp, "AC_vardef ");
         } else {
            fprintf(fp, "C_vardef ");
         }
         fprintf(fp, "((");
         struct prog_var_info * var = find_prog_var_by_id(cmd->d.VARDECL.info->id, &env->persist);
         CoqPrintVarName(var->name, var->id, fp);
         fprintf(fp, ", None, "); 
         struct SimpleCtype * type = TransType(cmd->d.VARDECL.info->type);
         CoqSimpleCtypePrinter(type, env, fp);
         fprintf(fp, ")::nil)");
         break;
      }
      case T_SIMPLE:
         if (print_annotation) {
            fprintf(fp, "AC_simple ");
         } else {
            fprintf(fp, "C_simple ");
         }
         CoqCSimpleStatementPrinter(cmd->d.SIMPLE.scmd, env, fp);
         break;
      case T_SEQ:
         if (print_annotation) {
            fprintf(fp, "AC_seq ");
         } else {
            fprintf(fp, "C_seq ");
         }
         CoqCStatementPrinter(cmd->d.SEQ.left, print_annotation, env, fp);
         fprintf(fp, " ");
         CoqCStatementPrinter(cmd->d.SEQ.right, print_annotation, env, fp);
         break;
      case T_IF:
         if (print_annotation) {
            fprintf(fp, "AC_if ");
         } else {
            fprintf(fp, "C_if ");
         }
         CoqASTExprPrinter(cmd->d.IF.cond, env, fp);
         fprintf(fp, " ");
         CoqCStatementPrinter(cmd->d.IF.left, print_annotation, env, fp);
         fprintf(fp, " ");
         if (cmd->d.IF.right != NULL) {
            CoqCStatementPrinter(cmd->d.IF.right, print_annotation, env, fp);
         } else {
            if (print_annotation) {
               fprintf(fp, "(AC_simple C_skip)");
            } else {
               fprintf(fp, "(C_simple C_skip)");
            }
         }
         break;
      case T_SWITCH: {
         if (print_annotation) {
            fprintf(fp, "AC_switch ");
         } else {
            fprintf(fp, "C_switch ");
         }
         CoqASTExprPrinter(cmd->d.SWITCH.cond, env, fp);
         struct Case_list * list;
         list = cmd->d.SWITCH.body;
         if (list != NULL) {
            int has_default;
            has_default = 0;
            int case_count;
            case_count = 0;
            while (list != NULL) {
               if (list->head->t == T_CASE) {
                  if (case_count == 0) fprintf(fp, "(");
                  ++case_count;
                  fprintf(fp, "(");
                  CoqASTExprPrinter(list->head->d.CASE.cond, env, fp);
                  fprintf(fp, ", ");
                  CoqCStatementPrinter(list->head->d.CASE.body, print_annotation, env, fp);
                  fprintf(fp, ")");
                  list = list->tail;
                  if (list == NULL || list->head->t == T_DEFAULT) {
                     fprintf(fp, "::nil) ");
                  } else {
                     fprintf(fp, "::");   
                  }
               } else {
                  if (case_count == 0) fprintf(fp, "nil");
                  fprintf(fp, " ");
                  CoqCStatementPrinter(list->head->d.DEFAULT.body, print_annotation, env, fp);
                  has_default = 1;
                  list = list->tail;
               }
            }
            if (!has_default) {
               if (print_annotation) {
                  fprintf(fp, "(AC_simple C_skip)");
               } else {
                  fprintf(fp, "(C_simple C_skip)");
               }
            }
         } else {
            if (print_annotation) {
               fprintf(fp, "nil (AC_simple C_skip)");
            } else {
               fprintf(fp, "nil (C_simple C_skip)");
            }
         }
         break;
      }
      case T_WHILE:
         if (print_annotation && cmd->d.WHILE.inv != NULL) {
            fprintf(fp, " AC_seq ");
            fprintf(fp, "(AC_inv ");
            struct AsrtList * inner_asrt = cmd->d.WHILE.inv;
            CoqInnerAsrtListPrinter(inner_asrt, env, fp);
            fprintf(fp, ")");
         }
         if (print_annotation) {
            fprintf(fp, "(AC_while ");
         } else {
            fprintf(fp, "C_seq (C_simple C_skip)");
            fprintf(fp, "(C_while ");
         }
         CoqASTExprPrinter(cmd->d.WHILE.cond, env, fp);
         fprintf(fp, " ");
         CoqCStatementPrinter(cmd->d.WHILE.body, print_annotation, env, fp);
         fprintf(fp, ")");
         break;
      case T_DOWHILE:
         if (print_annotation && cmd->d.DOWHILE.inv != NULL) {
            fprintf(fp, "AC_inv ");
            struct AsrtList * inner_asrt = cmd->d.DOWHILE.inv;
            CoqInnerAsrtListPrinter(inner_asrt, env, fp);
         }
         if (print_annotation) {
            fprintf(fp, "AC_dowhile ");
         } else {
            fprintf(fp, "C_dowhile ");
         }
         CoqASTExprPrinter(cmd->d.DOWHILE.cond, env, fp);
         fprintf(fp, " ");
         CoqCStatementPrinter(cmd->d.DOWHILE.body, print_annotation, env, fp);
         break;
      case T_FOR:
         if (print_annotation && cmd->d.FOR.inv != NULL) {
            fprintf(fp, "AC_inv ");
            struct AsrtList * inner_asrt = cmd->d.FOR.inv;
            CoqInnerAsrtListPrinter(inner_asrt, env, fp);
         }
         if (print_annotation) {
            fprintf(fp, "AC_for ");
         } else {
            fprintf(fp, "C_for ");
         }
         CoqCSimpleStatementPrinter(cmd->d.FOR.init, env, fp);
         fprintf(fp, " ");
         CoqASTExprPrinter(cmd->d.FOR.cond, env, fp);
         fprintf(fp, " ");
         CoqCSimpleStatementPrinter(cmd->d.FOR.incr, env, fp);
         fprintf(fp, " ");
         CoqCStatementPrinter(cmd->d.FOR.body, print_annotation, env, fp);
         break;
      case T_BREAK:
         if (print_annotation) {
            fprintf(fp, "AC_break");
         } else {
            fprintf(fp, "C_break");
         }
         break;
      case T_CONTINUE:
         if (print_annotation) {
            fprintf(fp, "AC_continue");
         } else {
            fprintf(fp, "C_continue");
         }
         break;
      case T_RETURN:
         if (cmd->d.RETURN.arg != NULL) {
            if (print_annotation) {
               fprintf(fp, "AC_return (Some ");
            } else {
               fprintf(fp, "C_return (Some ");
            }
            CoqASTExprPrinter(cmd->d.RETURN.arg, env, fp);
            fprintf(fp, ")");
         } else {
            if (print_annotation) {
               fprintf(fp, "AC_return None");
            } else {
               fprintf(fp, "C_return None");
            }
         }
         break;
      case T_SKIP:
         if (print_annotation) {
            fprintf(fp, "AC_simple C_skip");
         } else {
            fprintf(fp, "C_simple C_skip");
         }
         break;
      case T_BLOCK:
         if (print_annotation) {
            fprintf(fp, "AC_block ");
         } else {
            fprintf(fp, "C_block ");
         }
         CoqCStatementPrinter(cmd->d.BLOCK.cmd, print_annotation, env, fp);
         break;
      case T_COMMENT:
         if (print_annotation) {
            fprintf(fp, "AC_assert ");
            struct AsrtList * inner_asrt = cmd->d.COMMENT.asrt;
            CoqInnerAsrtListPrinter(inner_asrt, env, fp);
         } else {
            fprintf(fp, "C_simple C_skip");
         }
         break;
      default:
         break;
   }
   fprintf(fp, ")");
}

void ACStmtPrint(struct environment *env, FILE *fp) {
   struct blist *it;
   int func_count = 0;
   for (it = env->persist.func.top; it != NULL; it = it->down) {
      struct func_info *info;
      info = it->val;      
      if (info->defined == 0) continue;
      fprintf(fp, "Definition ACStatement%d := ", ++func_count);
      CoqCStatementPrinter(info->body, 1, env, fp);
      fprintf(fp, ".\n\n");
   }
}

void CStmtPrint(struct environment *env, FILE *fp) {
   struct blist *it;
   int func_count = 0;
   for (it = env->persist.func.top; it != NULL; it = it->down) {
      struct func_info *info;
      info = it->val;
      if (info->defined == 0) continue;
      fprintf(fp, "Definition CStatement%d := ", ++func_count);
      CoqCStatementPrinter(info->body, 0, env, fp);
      fprintf(fp, ".\n\n");
   }
}