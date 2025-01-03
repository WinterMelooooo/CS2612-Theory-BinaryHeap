#include <assert.h>
#include "../../compiler/env.h"
#include "CoqInnerAsrtPrinter.h"
#include "CoqPrintTools.h"
#include "string.h"

void CoqInnerUnOpPrinter(enum InnerUnaryOperation op, FILE * fp) {
   switch (op) {
      case Oneg:
         fprintf(fp, "Oneg");
         break;
      case Onint:
         fprintf(fp, "Onint");
         break;
      case Onot:
         fprintf(fp, "Onot");
         break;
   }
}

void CoqInnerBinOpPrinter(enum InnerBinaryOperation op, FILE * fp) {
   switch (op) {
      case Oadd: 
         fprintf(fp, "Oadd");
         break;
      case Osub:
         fprintf(fp, "Osub");
         break;
      case Omul:
         fprintf(fp, "Omul");
         break;
      case Odiv:
         fprintf(fp, "Odiv");
         break;
      case Omod:
         fprintf(fp, "Omod");
         break;
      case Oand:
         fprintf(fp, "Oand");
         break;
      case Oor:
         fprintf(fp, "Oor");
         break;
      case Oxor:
         fprintf(fp, "Oxor");
         break;
      case Oshl:
         fprintf(fp, "Oshl");
         break;
      case Oshr:
         fprintf(fp, "Oshr");
         break;
   }
}

void CoqExprValPrinter(struct ExprVal * expr, struct environment * env, FILE * fp) {
   fprintf(fp, "(");
   switch (expr->t) {
      case EZ_VAL:
         fprintf(fp, "Ez_val (%llu)", expr->d.EZ_VAL.number);
         break;
      case VFIELD_ADDRESS:
         fprintf(fp, "Vfield_address ");
         struct field_info * field;
         field = find_field_by_id(expr->d.VFIELD_ADDRESS.field_id, &env->persist);
         CoqExprValPrinter(expr->d.VFIELD_ADDRESS.expr, env, fp);
         fprintf(fp, " ");
         CoqPrintRawAnnots(field->parent->name, field->parent->id, 0, fp);
         fprintf(fp, " ");
         CoqPrintRawAnnots(field->name, field->id, 0, fp);
         break;
      case VUOP:
         fprintf(fp, "Vuop ");
         CoqInnerUnOpPrinter(expr->d.VUOP.op, fp);
         fprintf(fp, " ");
         CoqExprValPrinter(expr->d.VUOP.expr, env, fp);
         break;
      case VBOP:
         fprintf(fp, "Vbop ");
         CoqInnerBinOpPrinter(expr->d.VBOP.op, fp);
         fprintf(fp, " ");
         CoqExprValPrinter(expr->d.VBOP.expr1, env, fp);
         fprintf(fp, " ");
         CoqExprValPrinter(expr->d.VBOP.expr2, env, fp);
         break;
      case FUNCAPP: {
         struct logic_var_info * func = find_logic_var_by_id(expr->d.FUNCAPP.id, &env->persist);
         fprintf(fp, "Funcapp ");
         CoqPrintRawAnnots(func->name, func->id, 0, fp);
         fprintf(fp, " ");
         struct ExprValListNode * expr_list = expr->d.FUNCAPP.args->head;
         if (expr_list != NULL) {
            fprintf(fp, "(");
            while (expr_list != NULL) {
               CoqExprValPrinter(expr_list->data, env, fp);
               expr_list = expr_list->next;
               if (expr_list != NULL) {
                  fprintf(fp, "::");
               } else {
                  fprintf(fp, "::nil)");
               }
            }
         } else {
            fprintf(fp, "nil");
         }
         break;
      }
   }
   fprintf(fp, ")");
}

void CoqExprValListPrinter(struct ExprValList * list, struct environment * env, FILE * fp) {
   struct ExprValListNode * node = list->head;
   if (node != NULL) {
      fprintf(fp, "(");
      while (node != NULL) {
         CoqExprValPrinter(node->data, env, fp);
         node = node->next;
         if (node != NULL) {
            fprintf(fp, "::");
         } else {
            fprintf(fp, "::nil)");
         }
      }
   } else {
      fprintf(fp, "nil");
   }
}

void CoqPropUOPPrinter(enum PropUOP op, FILE * fp) {
   switch (op) {
      case PROP_NOT:
         fprintf(fp, "Pnot");
         break;
      default:
         fprintf(stderr, "Error: CoqPropUOPPrinter: unknown PropUOP\n");
         exit(1);
   }
}

void CoqPropBinOpPrinter(enum PropBinOP op, FILE * fp) {
   switch (op) {
      case PROP_AND:
         fprintf(fp, "Pand");
         break;
      case PROP_OR:
         fprintf(fp, "Por");
         break;
      case PROP_IMPLY:
         fprintf(fp, "Pimply");
         break;
      case PROP_IFF:
         fprintf(fp, "Piff");
         break;
      default:
         fprintf(stderr, "Error: CoqPropBinOpPrinter: unknown PropBinOP\n");
         exit(1);
   }
}

void CoqPropPtrOpPrinter(enum PropPtrOP op, FILE * fp) {
   fprintf(stderr, "Error: CoqPropPtrOpPrinter: not implemented\n");
   exit(1);
}

void CoqPropCompareOpPrinter(enum PropCompOp op, FILE * fp) {
   switch (op) {
      case PROP_LE:
         fprintf(fp, "Pvle");
         break;
      case PROP_GE:
         fprintf(fp, "Pvge");
         break;
      case PROP_LT:
         fprintf(fp, "Pvlt");
         break;
      case PROP_GT:
         fprintf(fp, "Pvgt");
         break;
      case PROP_EQ:
         fprintf(fp, "Pvequal");
         break;
      case PROP_NEQ:
         fprintf(stderr, "CoqPropCompareOpPrinter: PROP_NEQ should be eliminated before.");
   }
}

void CoqQuantifierPrinter(enum PropQuantifier op, FILE * fp) {
   switch (op) {
      case PROP_FORALL:
         fprintf(fp, "PForall");
         break;
      case PROP_EXISTS:
         fprintf(fp, "PExists");
         break;
      default:
         fprintf(stderr, "Error: CoqQuantifierPrinter: unknown PropQuantifier\n");
         exit(1);
   }
}

void CoqPropositionPrinter(struct Proposition * prop, struct environment * env, FILE * fp) {
   fprintf(fp, "(");
   switch (prop->t) {
      case T_PROP_TRUE:
         fprintf(fp, "TT");
         break;
      case T_PROP_FALSE:
         fprintf(fp, "FF");
         break;
      case T_PROP_UNARY:
         fprintf(fp, "Up ");
         CoqPropUOPPrinter(prop->d.UNARY.op, fp);
         fprintf(fp, " ");
         CoqPropositionPrinter(prop->d.UNARY.prop, env, fp);
         break;
      case T_PROP_BINARY:
         fprintf(fp, "Bp ");
         CoqPropBinOpPrinter(prop->d.BINARY.op, fp);
         fprintf(fp, " ");
         CoqPropositionPrinter(prop->d.BINARY.prop1, env, fp);
         fprintf(fp, " ");
         CoqPropositionPrinter(prop->d.BINARY.prop2, env, fp);
         break;
      case T_PROP_PTR:
         fprintf(fp, "Ue ");
         CoqPropPtrOpPrinter(prop->d.PTR.op, fp);
         fprintf(fp, " ");
         CoqExprValPrinter(prop->d.PTR.expr, env, fp);
         break;
      case T_PROP_COMPARE:
         if (prop->d.COMPARE.op == PROP_NEQ) {
            struct Proposition * new_prop = (struct Proposition *)malloc(sizeof(struct Proposition));
            new_prop->t = T_PROP_UNARY;
            new_prop->d.UNARY.op = PROP_NOT;
            new_prop->d.UNARY.prop = (struct Proposition *)malloc(sizeof(struct Proposition));
            new_prop->d.UNARY.prop->t = T_PROP_COMPARE;
            new_prop->d.UNARY.prop->d.COMPARE.op = PROP_EQ;
            new_prop->d.UNARY.prop->d.COMPARE.expr1 = prop->d.COMPARE.expr1;
            new_prop->d.UNARY.prop->d.COMPARE.expr2 = prop->d.COMPARE.expr2;
            CoqPropositionPrinter(new_prop, env, fp);
            free(new_prop->d.UNARY.prop);
            free(new_prop);
            break;
         } else {
            fprintf(fp, "Be ");
            CoqPropCompareOpPrinter(prop->d.COMPARE.op, fp);
            fprintf(fp, " ");
            CoqExprValPrinter(prop->d.COMPARE.expr1, env, fp);
            fprintf(fp, " ");
            CoqExprValPrinter(prop->d.COMPARE.expr2, env, fp);
            break;
         }
      case T_PROP_QUANTIFIER: {
         struct logic_var_info * var = find_logic_var_by_id(prop->d.QUANTIFIER.ident, &env->persist);
         fprintf(fp, "Qp ");
         CoqQuantifierPrinter(prop->d.QUANTIFIER.op, fp);
         fprintf(fp, " ");
         fprintf(fp, "_%s", var->name + strlen("V_vari"));
         int id = var->id;
         CoqCollectAnnots(var->name, id, 0);
         fprintf(fp, " ");
         CoqPropositionPrinter(prop->d.QUANTIFIER.prop, env, fp);
         break;
      }
   }
   fprintf(fp, ")");
}

void CoqSeparationPrinter(struct Separation * sep, struct environment * env, FILE * fp) {
   fprintf(fp, "(");
   switch (sep->t) {
      case T_DATA_AT:
         fprintf(fp, "Data_at ");
         CoqExprValPrinter(sep->d.DATA_AT.left, env, fp);
         fprintf(fp, " ");
         CoqSimpleCtypePrinter(sep->d.DATA_AT.ty, env, fp);
         fprintf(fp, " ");
         CoqExprValPrinter(sep->d.DATA_AT.right, env, fp);
         break;
      case T_UNDEF_DATA_AT:
         fprintf(fp, "Undef_Data_at ");
         CoqExprValPrinter(sep->d.UNDEF_DATA_AT.left, env, fp);
         fprintf(fp, " ");
         CoqSimpleCtypePrinter(sep->d.UNDEF_DATA_AT.ty, env, fp);
         break;
      case T_OTHER:
         fprintf(fp, "Other ");
         struct logic_var_info * info = find_logic_var_by_id(sep->d.OTHER.sep_id, &env->persist);
         assert(info->category == LOGIC_SEPDEF ||
                info->category == LOGIC_EXTERN);
         struct sepdef_info * sep_def = info->sep;
         CoqPrintRawAnnots(sep_def->name, sep_def->id, 0, fp);
         fprintf(fp, " ");
         CoqExprValListPrinter(sep->d.OTHER.exprs, env, fp);
         break;
   }
   fprintf(fp, ")");
}

void CoqPropListPrinter(struct PropList * prop_list, struct environment * env, FILE * fp) {
   struct PropList * list;
   list = prop_list;
   if (list != NULL) {
      fprintf(fp, "(");
      while (list != NULL) {
         CoqPropositionPrinter(list->head, env, fp);
         list = list->next;
         if (list == NULL) {
            fprintf(fp, "::nil)");
         } else {
            fprintf(fp, "::");
         }
      }
   } else {
      fprintf(fp, "nil");
   }
}

void CoqLocalListPrinter(struct LocalLinkedHashMap * local_list, struct environment * env, FILE * fp) {
   struct LocalLinkedHashMapNode * node;
   node = local_list->head;
   if (node != NULL) {
      fprintf(fp, "(");
      while (node != NULL) {
         fprintf(fp, "(");
         fprintf(fp, "Avar ");
         struct prog_var_info * var = find_prog_var_by_id(node->id, &env->persist);
         CoqPrintVarName(var->name, var->id, fp);
         fprintf(fp, " ");
         CoqExprValPrinter(node->value, env, fp);
         fprintf(fp, ")");
         fprintf(fp, "::");
         node = node->next;
         if (node == NULL) {
            fprintf(fp, "nil)");
         }
      }
   } else {
      fprintf(fp, "nil");
   }
}

void CoqSepListPrinter(struct SepList * sep_list, struct environment * env, FILE * fp) {
   struct SepList * list;
   list = sep_list;
   if (list != NULL) {
      fprintf(fp, "(");
      while (list != NULL) {
         CoqSeparationPrinter(list->head, env, fp);
         list = list->next;
         if (list != NULL) {
            fprintf(fp, "::");
         } else {
            fprintf(fp, "::nil)");
         }
      }
   } else {
      fprintf(fp, "nil");
   }
}

void CoqExistListPrinter(struct ExistList * exist_list, struct environment * env, FILE * fp) {
   struct ExistList * list;
   list = exist_list;
   if (list != NULL) {
      fprintf(fp, "(");
      while (list != NULL) {
         struct logic_var_info * var_info = find_logic_var_by_id(list->id, &env->persist);
         if (var_info != NULL && var_info->name != NULL) {
            char * new_name = malloc(sizeof(char) * (strlen(var_info->name) + 3));
            sprintf(new_name, "_%s_", var_info->name);
            fprintf(fp, "%s", new_name);
            CoqCollectAnnots(new_name, list->id, 0);
         } else {
            fprintf(fp, "_%d", list->id);
         }
         list = list->next;
         if (list != NULL) {
            fprintf(fp, "::");
         } else {
            fprintf(fp, "::nil)");
         }
      }
   } else {
      fprintf(fp, "nil");
   }
}

void CoqInnerAsrtPrinter(struct Assertion * asrt, struct environment * env, FILE * fp) {
   fprintf(fp, "{| ");
   fprintf(fp, "Prop_list := ");
   CoqPropListPrinter(asrt->prop_list, env, fp);
   fprintf(fp, "; Local_list := ");
   CoqLocalListPrinter(asrt->local_list, env, fp);
   fprintf(fp, "; Sep_list := ");
   CoqSepListPrinter(asrt->sep_list, env, fp);
   fprintf(fp, "; Exist_list := ");
   CoqExistListPrinter(asrt->exist_list, env, fp);
   fprintf(fp, "; |}");
}

void CoqInnerAsrtListPrinter(struct AsrtList * asrt, struct environment * env, FILE * fp) {
   if (asrt != NULL) {
      fprintf(fp, "(");
      while (asrt != NULL) {
         CoqInnerAsrtPrinter(asrt->head, env, fp);
         asrt = asrt->next;
         if (asrt == NULL) {
            fprintf(fp, "::nil)");
         } else {
            fprintf(fp, "::");
         }
      }
   } else {
      fprintf(fp, "nil");
   }
}

void CoqFuncRetTypePrinter(struct FuncRetType * ret, struct environment * env, FILE * fp) {
   if (ret != NULL) {
      fprintf(fp, "(");
      while (ret != NULL) {
         fprintf(fp, "{|");
         fprintf(fp, " Assert_r := ");
         CoqInnerAsrtPrinter(ret->asrt, env, fp);
         fprintf(fp, "; ");
         fprintf(fp, "Return := ");
         if (ret->val == NULL) {
            fprintf(fp, "None");
         } else {
            fprintf(fp, "Some ");
            CoqExprValPrinter(ret->val, env, fp);
         }
         fprintf(fp, "|}");
         ret = ret->next;
         if (ret == NULL) {
            fprintf(fp, "::nil)");
         } else {
            fprintf(fp, "::");
         }
      }
   } else {
      fprintf(fp, "nil");
   }
}

void CoqExecPostPrinter(int id, struct FuncRetType * ret, struct environment * env, FILE * fp) {
   fprintf(fp, "Definition execPost%d := \n", id);
   fprintf(fp, "{|\n");
   fprintf(fp, "  Normal_ret := ");
   CoqInnerAsrtListPrinter(NULL, env, fp);
   fprintf(fp, ";\n");
   fprintf(fp, "  Break_ret := ");
   CoqInnerAsrtListPrinter(NULL, env, fp);
   fprintf(fp, ";\n");
   fprintf(fp, "  Continue_ret := ");
   CoqInnerAsrtListPrinter(NULL, env, fp);
   fprintf(fp, ";\n");
   fprintf(fp, "  Return_ret := ");
   CoqFuncRetTypePrinter(ret, env, fp);
   fprintf(fp, ";\n");
   fprintf(fp, "|}.\n\n");
}
