#include "CoqPrintTools.h"
#include "CoqCexprPrinter.h"
#include "../Trans/TypeTrans.h"
#include "../Trans/PS_ExprTrans.h"
#include "../AsrtDef/SimpleCtypeDef.h"
#include <stdio.h>
#include <assert.h>

void CoqUnOpTypePrinter(enum UnOpType op, FILE * fp) {
   switch (op) {
      case T_UMINUS:
         fprintf(fp, "O_UMINUS");
         break;
      case T_UPLUS:
         fprintf(fp, "O_UPLUS");
         break;
      case T_NOTBOOL:
         fprintf(fp, "O_NOTBOOL");
         break;
      case T_NOTINT:
         fprintf(fp, "O_NOTINT");
         break;
      default:
         fprintf(stderr, "Error: CoqCexprPrinter: unknown unary operator %s %d\n", __FILE__, __LINE__);
         break;
   }
}

void CoqBinOpTypePrinter(enum BinOpType op, FILE * fp) {
   switch (op) {
      case T_PLUS:
         fprintf(fp, "O_PLUS");
         break;
      case T_MINUS:
         fprintf(fp, "O_MINUS");
         break;
      case T_MUL:
         fprintf(fp, "O_MUL");
         break;
      case T_DIV:
         fprintf(fp, "O_DIV");
         break;
      case T_MOD:
         fprintf(fp, "O_MOD");
         break;
      case T_LT:
         fprintf(fp, "O_LT");
         break;
      case T_GT:
         fprintf(fp, "O_GT");
         break;
      case T_LE:
         fprintf(fp, "O_LE");
         break;
      case T_GE:
         fprintf(fp, "O_GE");
         break;
      case T_EQ:
         fprintf(fp, "O_EQ");
         break;
      case T_NE:
         fprintf(fp, "O_NE");
         break;
      case T_AND:
         fprintf(fp, "O_AND");
         break;
      case T_OR:
         fprintf(fp, "O_OR");
         break;
      case T_XOR:
         fprintf(fp, "O_XOR");
         break;
      case T_SHL:
         fprintf(fp, "O_SHL");
         break;
      case T_SHR:
         fprintf(fp, "O_SHR");
         break;
      case T_BAND:
         fprintf(fp, "O_BAND");
         break;
      case T_BOR:
         fprintf(fp, "O_BOR");
         break;
      default:
         fprintf(stderr, "Error: CoqCexprPrinter: unknown binary operator %s %d\n", __FILE__, __LINE__);
         break;
   }
}

void CoqCexprPrinter(struct Cexpr * expr, struct environment * env, FILE * fp) {
   fprintf(fp, "(");
   switch (expr->t) {
      case C_CONST:
         fprintf(fp, "C_const ");
         enum Signedness signedness;
         switch (expr->type->t) {
            case C_int8:
               signedness = expr->type->d.CINT8.s;
               break;
            case C_int16:
               signedness = expr->type->d.CINT16.s;
               break;
            case C_int32:
               signedness = expr->type->d.CINT32.s;
               break;
            case C_int64:
               signedness = expr->type->d.CINT64.s;
               break;
            default:
               fprintf(stderr, "unexpected type %s %d\n", __FILE__, __LINE__);
               exit(1);
         }
         if (signedness == Signed) {
            fprintf(fp, "%lld ", (long long) expr->d.C_CONST.number);
         } else {
            fprintf(fp, "%llu ", (unsigned long long) expr->d.C_CONST.number);
         }
         CoqSimpleCtypePrinter(expr->type, env, fp);
         break;
      case C_VAR: {
         struct prog_var_info  * var;
         var = find_prog_var_by_id(expr->d.C_VAR.id, &env->persist);
         fprintf(fp, "C_var ");
         CoqPrintVarName(var->name, var->id, fp);
         fprintf(fp, " ");
         CoqSimpleCtypePrinter(expr->type, env, fp);
         break;
      }
      case C_DEREF:
         fprintf(fp, "C_deref ");
         CoqCexprPrinter(expr->d.C_DEREF.expr, env, fp);
         fprintf(fp, " ");
         CoqSimpleCtypePrinter(expr->type, env, fp);
         break;
      case C_ADDROF:
         fprintf(fp, "C_addrof ");
         CoqCexprPrinter(expr->d.C_ADDROF.expr, env, fp);
         fprintf(fp, " ");
         CoqSimpleCtypePrinter(expr->type, env, fp);
         break;
      case C_UNOP:
         fprintf(fp, "C_unop ");
         CoqUnOpTypePrinter(expr->d.C_UNOP.op, fp);
         fprintf(fp, " ");
         CoqCexprPrinter(expr->d.C_UNOP.expr, env, fp);
         fprintf(fp, " ");
         CoqSimpleCtypePrinter(expr->type, env, fp);
         break;
      case C_BINOP:
         fprintf(fp, "C_binop ");
         CoqBinOpTypePrinter(expr->d.C_BINOP.op, fp);
         fprintf(fp, " ");
         CoqCexprPrinter(expr->d.C_BINOP.expr1, env, fp);
         fprintf(fp, " ");
         CoqCexprPrinter(expr->d.C_BINOP.expr2, env, fp);
         fprintf(fp, " ");
         CoqSimpleCtypePrinter(expr->type, env, fp);
         break;
      case C_CAST:
         fprintf(fp, "C_cast ");
         CoqCexprPrinter(expr->d.C_CAST.expr, env, fp);
         fprintf(fp, " ");
         CoqSimpleCtypePrinter(expr->type, env, fp);
         break;
      case C_STRUCTFIELD: {
         fprintf(fp, "C_structfield ");
         CoqCexprPrinter(expr->d.C_STRUCTFIELD.expr, env, fp);
         fprintf(fp, " ");
         struct field_info * field = find_field_by_id(expr->d.C_STRUCTFIELD.field_id, &env->persist);
         CoqPrintRawAnnots(field->parent->name, field->parent->id, 0, fp);
         fprintf(fp, " ");
         CoqPrintRawAnnots(field->name, field->id, 0, fp);
         fprintf(fp, " ");
         CoqSimpleCtypePrinter(expr->type, env, fp);
         break;
      }
      case C_UNIONFIELD:
         fprintf(fp, "C_unionfield ");
         CoqCexprPrinter(expr->d.C_UNIONFIELD.expr, env, fp);
         fprintf(fp, " ");
         struct field_info * field = find_field_by_id(expr->d.C_UNIONFIELD.field_id, &env->persist);
         CoqPrintRawAnnots(field->parent->name, field->parent->id, 0, fp);
         fprintf(fp, " ");
         CoqPrintRawAnnots(field->name, field->id, 0, fp);
         fprintf(fp, " ");
         CoqSimpleCtypePrinter(expr->type, env, fp);
         break;
      case C_SIZEOF:
         fprintf(fp, "C_sizeof ");
         CoqSimpleCtypePrinter(expr->d.C_SIZEOF.inner_type, env, fp);
         fprintf(fp, " ");
         CoqSimpleCtypePrinter(expr->type, env, fp);
         break;
      case C_INDEX:
         fprintf(fp, "C_index ");
         CoqCexprPrinter(expr->d.C_INDEX.arr_expr, env, fp);
         fprintf(fp, " ");
         CoqCexprPrinter(expr->d.C_INDEX.inner_expr, env, fp);
         fprintf(fp, " ");
         CoqSimpleCtypePrinter(expr->type, env, fp);
         break;
      case C_CALL: {
         fprintf(fp, "C_call ");
         CoqCexprPrinter(expr->d.C_CALL.func, env, fp);
         if (expr->d.C_CALL.args_exprs == NULL) {
            fprintf(fp, "nil ");
         } else {
            struct CexprListNode * args = expr->d.C_CALL.args_exprs->head;
            fprintf(fp, "(");
            while (args != NULL) {
               CoqCexprPrinter(args->data, env, fp);
               fprintf(fp, " ");
               args = args->next;
               if (args == NULL) {
                  fprintf(fp, "::nil) ");
               } else {
                  fprintf(fp, "::");
               }
            }
         }
         CoqSimpleCtypePrinter(expr->type, env, fp);
         break;
      }
      default:
         fprintf(stderr, "unexpected type %s %d\n", __FILE__, __LINE__);
         exit(1);
   }
   fprintf(fp, ")");
}

void CoqASTExprPrinter(struct expr * expr, struct environment * env, FILE * fp) {
   struct Cexpr * cexpr = PS_ExprTrans(expr, env);
   CoqCexprPrinter(cexpr, env, fp);
   CexprFree(cexpr);
}