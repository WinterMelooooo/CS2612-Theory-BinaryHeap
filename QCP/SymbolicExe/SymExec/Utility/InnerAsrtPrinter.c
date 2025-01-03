#include <assert.h>
#include <string.h>
#include "InnerAsrtPrinter.h"
#include "../../compiler/lang.h"
#include "CexprPrinter.h"
#include "Debugger.h"
#include "../../compiler/cp.h"

#define PRINT_PRECISE_ID

#ifdef PRINT_PRECISE_ID
#define PRINT_NAME(fp, name, id)\
   do {\
      if ((id != -1)) {\
         fprintf(fp, "%s_%d", (name), (id));\
      } else {\
         fprintf(fp, "%s", (name));\
      }\
   } while(0)
#else 
#define PRINT_NAME(fp, name, id)\
   do {\
      fprintf(fp, "%s", (name));\
   } while(0)
#endif

extern struct PolyType *cpa_type_of(struct atype *ty);

char* PrintUnOp_str(enum InnerUnaryOperation op) {
   switch (op) {
   case Oneg:
      return "Oneg";
      break;
   case Onint:
      return "Onint";
   case Onot:
      return "Onot";
   }
   return NULL;
}

void InnerPrintUnOp(enum InnerUnaryOperation op, FILE * fp) {
   switch (op) {
   case Oneg:
      fprintf(fp, "-");
      break;
   case Onint:
      fprintf(fp, "~");
      break;
   case Onot:
      fprintf(fp, "!");
      break;
   }
}

char* PrintBinOp_str(enum InnerBinaryOperation op) {
   switch (op) {
      case Oadd: 
         return "Oadd";
         break;
      case Osub:
         return "Osub";
         break;
      case Omul:
         return "Omul";
         break;
      case Odiv:
         return "Odiv";
         break;
      case Omod:
         return "Omod";
         break;
      case Oand:
         return "Oand";
         break;
      case Oor:
         return "Oor";
         break;
      case Oxor:
         return "Oxor";
         break;
      case Oshl:
         return "Oshl";
         break;
      case Oshr:
         return "Oshr";
         break;
   }
   return NULL;
}

void InnerPrintBinOp(enum InnerBinaryOperation op, FILE * fp) {
   switch (op) {
      case Oadd: 
         fprintf(fp, "+");
         break;
      case Osub:
         fprintf(fp, "-");
         break;
      case Omul:
         fprintf(fp, "*");
         break;
      case Odiv:
         fprintf(fp, "/");
         break;
      case Omod:
         fprintf(fp, "%%");
         break;
      case Oand:
         fprintf(fp, "&");
         break;
      case Oor:
         fprintf(fp, "|");
         break;
      case Oxor:
         fprintf(fp, "^");
         break;
      case Oshl:
         fprintf(fp, "<<");
         break;
      case Oshr:
         fprintf(fp, ">>");
         break;
   }
}

void PrintPolyTypeFile(struct PolyType * type, struct environment * env, FILE * fp) {
   if (type == NULL) {
        fprintf(fp, " !NULL! ");
        return;
   }
   switch (type->t) {
      case POLY_VAR: {
         struct atype_info * info = find_atype_by_id(type->d.VAR.id, &env->persist);
         PRINT_NAME(fp, info->name, type->d.VAR.id);
         break;
      }
      case POLY_FUNCAPP: {
         struct atype_info * info = find_atype_by_id(type->d.FUNCAPP.func, &env->persist);
         if (strncmp(info->name, "prod", 4) == 0) {
            assert(PolyTypeListLength(type->d.FUNCAPP.args) == 2);
            fprintf(fp, "(");
            PrintPolyTypeFile(type->d.FUNCAPP.args->head->data, env, fp);
            fprintf(fp, " * ");
            PrintPolyTypeFile(type->d.FUNCAPP.args->head->next->data, env, fp);
            fprintf(fp, ")");
            break;
         }
         PRINT_NAME(fp, info->name, type->d.FUNCAPP.func);
         if (!PolyTypeListIsEmpty(type->d.FUNCAPP.args)) {
            fprintf(fp, "(");
            struct PolyTypeListNode * list = type->d.FUNCAPP.args->head;
            while (list != NULL) {
               PrintPolyTypeFile(list->data, env, fp);
               fprintf(fp, " ");
               list = list->next;
            }
            fprintf(fp, ")");
         }
         break;
      }
      case POLY_ARROW:
         fprintf(fp, "(");
         PrintPolyTypeFile(type->d.ARROW.left, env, fp);
         fprintf(fp, " -> ");
         PrintPolyTypeFile(type->d.ARROW.right, env, fp);
         fprintf(fp, ")");
         break;
   }
}

void PrintPolyType(struct PolyType * type, struct environment * env) {
   PrintPolyTypeFile(type, env, stdout);
}

void PrintPolyArgList(struct PolyTypeList * types, struct ExprValList * args, struct environment * env, FILE * fp) {
   if (PolyTypeListIsEmpty(types) && ExprValListIsEmpty(args)) return;
   fprintf(fp, "(");
   struct PolyTypeListNode * tmp = types->head;
   while (tmp != NULL) {
      PrintPolyTypeFile(tmp->data, env, fp);
      if (tmp->next != NULL || !ExprValListIsEmpty(args)) fprintf(fp, ", ");
      tmp = tmp->next;
   }
   struct ExprValListNode * tmp2 = args->head;
   while (tmp2 != NULL) {
      PrintExprValFile(tmp2->data, env, fp);
      if (tmp2->next != NULL) fprintf(fp, ", ");
      tmp2 = tmp2->next;
   }
   fprintf(fp, ")");
}

/*
enum renaming_info_type {
   RENAME_VAR_PRE_VALUE,
   RENAME_VAR_VALUE,
   RENAME_VAR_ADDR,
   RENAME_DEREF,
   RENAME_FIELD,
   RENAME_FALLBACK,
   RENAME_POST_INTROED,      // existential variable in postcondition will be introduced by func-call
   RENAME_RETURN_VALUE,
   RENAME_FORALL_VAR,
   RENAME_EXISTS_VAR,
   RENAME_FREE_VAR,          // contains free variable, such as the variables in with_list
};
*/
void PrintVarRenaming(int id, struct renaming_info * renaming, FILE * fp) {
   if (renaming == NULL) return;
   switch (renaming->t) {
      case RENAME_VAR_PRE_VALUE:
         PRINT_NAME(fp, renaming->d.var_pre_value.var_name, id);
         fprintf(fp, "_pre");
         break;
      case RENAME_VAR_ADDR:
         PRINT_NAME(fp, renaming->d.var_addr.var_name, id);
         fprintf(fp, "_addr");
         break;
      case RENAME_VAR_VALUE:
         PRINT_NAME(fp, renaming->d.var_value.var_name, id);
         fprintf(fp, "_value");
         break;
      case RENAME_DEREF:
         PrintVarRenaming(-1, renaming->d.deref.info, fp);
         #ifdef PRINT_PRECISE_ID
            fprintf(fp, "_%d_v", id);
         #else
            fprintf(fp, "_v");
         #endif
         break;
      case RENAME_FIELD:
         PrintVarRenaming(-1, renaming->d.field.info, fp);
         #ifdef PRINT_PRECISE_ID
            fprintf(fp, "_%s_%d", renaming->d.field.name, id);
         #else
            fprintf(fp, "_%s", renaming->d.field.name);
         #endif
         break;
      case RENAME_FALLBACK:
         PRINT_NAME(fp, renaming->d.fallback.name, id);
         break;
      case RENAME_POST_INTROED:
         PRINT_NAME(fp, renaming->d.post_introed.var_name, id);
         fprintf(fp, "_post");
         break;
      case RENAME_RETURN_VALUE:
         PRINT_NAME(fp, "retval", id);
         break;
      case RENAME_FORALL_VAR:
         PRINT_NAME(fp, renaming->d.forall_var.var_name, id);
         break;
      case RENAME_EXISTS_VAR:
         PRINT_NAME(fp, renaming->d.exists_var.var_name, id);
         break;
      case RENAME_FREE_VAR:
         PRINT_NAME(fp, renaming->d.free_var.var_name, id);
         fprintf(fp, "_free");
         break;
   }
}

void PrintLogicVarFile(int id, struct environment * env, FILE * fp) {
   struct atype_info * atype_info = find_atype_by_id(id, &env->persist);
   if (atype_info != NULL) {
      PRINT_NAME(fp, atype_info->name, id);
      return;
   }
   struct func_info * func_info = find_func_by_id(id, &env->persist);
   if (func_info != NULL) {
      PRINT_NAME(fp, func_info->name, id);
      return;
   }
   struct logic_var_info * var_info = find_logic_var_by_id(id, &env->persist);
   if (var_info == NULL) {
      fprintf(stderr, "ident %d : not find in env.\n", id);
      exit(1);
   }
   assert(var_info != NULL);
   if (var_info->category == LOGIC_EXTERN) {
      fprintf(fp, "%s", var_info->name);
      return;
   }
   if (var_info->renaming == NULL) {
      fprintf(fp, "(_%d)", id);
   } else {
      PrintVarRenaming(id, var_info->renaming, fp);
   }
}

void PrintLogicVar(int id, struct environment * env) {
   PrintLogicVarFile(id, env, stdout);
}

void PrintLogicVarFileType(int id, struct environment * env, FILE * fp) {
   struct logic_var_info * var_info = find_logic_var_by_id(id, &env->persist);
   assert(var_info != NULL);
   fprintf(fp, " : ");
   PrintPolyTypeFile(cpa_type_of(var_info->atype), env, fp);
}

void PrintExprValFile(struct ExprVal *expr, struct environment * env, FILE * fp) {
   if (expr == NULL) {
      fprintf(fp, "NULL");
      return;
   }
   switch (expr->t) {
      case EZ_VAL:
         fprintf(fp, "(Ez_val %llu)", expr->d.EZ_VAL.number);
         break;
      case SIZE_OF:
         fprintf(fp, "(Size_of ");
         PrintSimpleCtypeFile(expr->d.SIZE_OF.type, env, fp);
         fprintf(fp, ")");
         break;
      case VFIELD_ADDRESS: {
         struct field_info * info;
         info = find_field_by_id(expr->d.VFIELD_ADDRESS.field_id, &env->persist);
         fprintf(fp, "&(");
         PrintExprValFile(expr->d.VFIELD_ADDRESS.expr, env, fp);
         fprintf(fp, "->%s)", info->name);
         break;
      }
      case VUOP:
         fprintf(fp, "(");
         InnerPrintUnOp(expr->d.VUOP.op, fp);
         PrintExprValFile(expr->d.VUOP.expr, env, fp);
         fprintf(fp, ")");
         break;
      case VBOP:
         fprintf(fp, "(");
         PrintExprValFile(expr->d.VBOP.expr1, env, fp);
         fprintf(fp, " ");
         InnerPrintBinOp(expr->d.VBOP.op, fp);
         fprintf(fp, " ");
         PrintExprValFile(expr->d.VBOP.expr2, env, fp);
         fprintf(fp, ")");
         break;
      case FUNCAPP: {
         PrintLogicVarFile(expr->d.FUNCAPP.id, env, fp);
         PrintPolyArgList(expr->d.FUNCAPP.types, expr->d.FUNCAPP.args, env, fp);
         break;
      }
      case LINDEX:
         fprintf(fp, "(");
         PrintExprValFile(expr->d.LINDEX.list, env, fp);
         fprintf(fp, "[");
         PrintExprValFile(expr->d.LINDEX.index, env, fp);
         fprintf(fp, "])");
         break;
      default:
         break;
   }  
}

void PrintExprVal(struct ExprVal *expr, struct environment * env) {
   PrintExprValFile(expr, env, stdout);
}

void PrintExprValListFile(struct ExprValList * list, struct environment * env, FILE * fp) {
   fprintf(fp, "(");
   struct ExprValListNode * tmp = list->head;
   while (tmp != NULL) {
      PrintExprValFile(tmp->data, env, fp);
      if (tmp->next != NULL) fprintf(fp, ", ");
      tmp = tmp->next;
   }
   putchar(')');
}

void PrintExprValList(struct ExprValList * list, struct environment * env) {
   PrintExprValListFile(list, env, stdout);
}

void PrintExistListFile(struct ExistList * list, struct environment * env, FILE * fp) {
   fprintf(fp, "EX ");
   struct ExistList * tmp = list;
   while (tmp != NULL) {
      PrintLogicVarFile(tmp->id, env, fp);
      // PrintLogicVarFileType(tmp->id, env, fp);
      putchar(' ');
      tmp = tmp->next;
   }
   puts("");
}

void PrintExistList(struct ExistList * list, struct environment * env) {
   PrintExistListFile(list, env, stdout);
}

char* PrintPropUOp_str(enum PropUOP op) {
   switch (op) {
   case PROP_NOT:
      return "PROP_NOT";
      break;
   default:
      break;
   }
   return NULL;
}

void PrintPropUOp(enum PropUOP op, FILE *fp) {
   switch (op) {
   case PROP_NOT:
      fprintf(fp, "!");
      break;
   default:
      break;
   }
}

char* PrintPropBinOp_str(enum PropBinOP op) {
   switch (op) {
   case PROP_AND:
      return "PROP_AND";
      break;
   case PROP_OR:
      return "PROP_OR";
      break;
   case PROP_IMPLY:
      return "PROP_IMPLY";
   case PROP_IFF:
      return "PROP_IFF";
   default:
      break;
   }
   return NULL;
}

void PrintPropBinOp(enum PropBinOP op, FILE *fp) {
   switch (op) {
   case PROP_AND:
      fprintf(fp, "&&");
      break;
   case PROP_OR:
      fprintf(fp, "||");
      break;
   case PROP_IMPLY:
      fprintf(fp, "->");
      break;
   case PROP_IFF:
      fprintf(fp, "<->");
      break;
   default:
      break;
   }
}

char* PrintPropPtrOp_str(enum PropPtrOP op) {
   switch (op) {
   case PROP_NOT_NULL:
      return "PROP_NOT_NULL";
      break;
   case PROP_MAYBE_NULL:
      return "PROP_MAYBE_NULL";
      break;
   case PROP_IS_NULL:
      return "PROP_IS_NULL";
      break;
   default:
      break;
   }
   return NULL;
}

char *PrintPropCmpOp_str(enum PropCompOp op) {
   switch (op) {
   case PROP_LE:
      return "PROP_LE";
      break;
   case PROP_LT:
      return "PROP_LT";
      break;
   case PROP_GT:
      return "PROP_GT";
      break;
   case PROP_GE:
      return "PROP_GE";
      break;      
   case PROP_EQ:
      return "PROP_EQ";
      break;
   case PROP_NEQ:
      return "PROP_NEQ";
      break;
   default:
      break;
   }
   return NULL;
}

void PrintPropCmpOp(enum PropCompOp op, FILE *fp) {
   switch (op) {
   case PROP_LE:
      fprintf(fp, "<=");
      break;
   case PROP_LT:
      fprintf(fp, "<");
      break;
   case PROP_GT:
      fprintf(fp, ">");
      break;
   case PROP_GE:
      fprintf(fp, ">=");
      break;      
   case PROP_EQ:
      fprintf(fp, "==");
      break;
   case PROP_NEQ:
      fprintf(fp, "!=");
      break;
   default:
      break;
   }
}

void PrintPropFile(struct Proposition * prop, struct environment * env, FILE * fp) {
   if (prop == NULL) {
      fprintf(fp, "NULL");
      return;
   }
   switch (prop->t) {
      case T_PROP_TRUE:
         fprintf(fp, "prop_true");
         break;
      case T_PROP_FALSE:
         fprintf(fp, "prop_false");
         break;
      case T_PROP_UNARY:
         PrintPropUOp(prop->d.UNARY.op, fp);
         fprintf(fp, "(");
         PrintPropFile(prop->d.UNARY.prop, env, fp);
         fprintf(fp, ")");
         break;
      case T_PROP_BINARY:
         PrintPropFile(prop->d.BINARY.prop1, env, fp);
         fprintf(fp, " ");
         PrintPropBinOp(prop->d.BINARY.op, fp);
         fprintf(fp, " ");
         PrintPropFile(prop->d.BINARY.prop2, env, fp);
         break;
      case T_PROP_PTR:
         fprintf(fp, "%s ", PrintPropPtrOp_str(prop->d.PTR.op));
         PrintExprValFile(prop->d.PTR.expr, env, fp);
         break;
      case T_PROP_COMPARE:
         PrintExprValFile(prop->d.COMPARE.expr1, env, fp);
         fprintf(fp, " ");
         PrintPropCmpOp(prop->d.COMPARE.op, fp);
         fprintf(fp, " ");
         PrintExprValFile(prop->d.COMPARE.expr2, env, fp);
         break;
      case T_PROP_QUANTIFIER:
         if (prop->d.QUANTIFIER.op == PROP_FORALL) {
            fprintf(fp, "forall ");
         } else {
            fprintf(fp, "exists ");
         }
         fprintf(fp, "%d ", prop->d.QUANTIFIER.ident);
         fprintf(fp, ", ");
         PrintPropFile(prop->d.QUANTIFIER.prop, env, fp);
         break;
      case T_PROP_OTHER: {
         struct logic_var_info * info = find_logic_var_by_id(prop->d.OTHER.predicate, &env->persist);
         PRINT_NAME(fp, info->name, prop->d.OTHER.predicate);
         PrintPolyArgList(prop->d.OTHER.types, prop->d.OTHER.args, env, fp);
      }
      default:
         break;
   }
}

void PrintProp(struct Proposition * prop, struct environment * env) {
   PrintPropFile(prop, env, stdout);
}

void PrintPropListFile(struct PropList * list, struct environment * env, FILE * fp) {
   fprintf(fp, "PROP[");
   struct PropList * tmp = list;
   while (tmp != NULL) {
      fprintf(fp," ");
      PrintPropFile(tmp->head, env, fp);
      fprintf(fp, "%s", tmp->next == NULL ? " " : ";\n");
      tmp = tmp->next;
   }
   fprintf(fp,"]\n");
}

void PrintPropList(struct PropList * list, struct environment * env) {
   PrintPropListFile(list, env, stdout);
}

void PrintLocal(struct LocalLinkedHashMapNode * node, struct environment * env, FILE * fp) {
   struct prog_var_info * var = find_prog_var_by_id(node->id, &env->persist);
   fprintf(fp, " Temp ");
   fprintf(fp, "%s ", var->name);
   PrintExprValFile(node->value, env, fp);
}

void PrintLocalListFile(struct LocalLinkedHashMap * list, struct environment * env, FILE * fp) {
   fprintf(fp, "LOCAL[");
   struct LocalLinkedHashMapNode *tmp = list->head;
   while (tmp != NULL) {
      fprintf(fp," ");
      PrintLocal(tmp, env, fp);
      fprintf(fp, "%s", tmp->next == NULL ? " " : ";\n");
      tmp = tmp->next;
   }
   fprintf(fp,"]\n");
}

void PrintLocalList(struct LocalLinkedHashMap * list, struct environment * env) {
   PrintLocalListFile(list, env, stdout);
}

void PrintSepFile(struct Separation *sep, struct environment * env, FILE * fp) {
   if (sep == NULL) return;
   if (sep->t == T_DATA_AT) {
      fprintf(fp, "Data_at ");
      PrintExprValFile(sep->d.DATA_AT.left, env, fp);
      putchar(' ');
      PrintExprValFile(sep->d.DATA_AT.right, env, fp);
      fprintf(fp, " ");
      PrintSimpleCtypeFile(sep->d.DATA_AT.ty, env, fp);
   } else if (sep->t == T_UNDEF_DATA_AT) {
      fprintf(fp, "Undef_Data_at ");
      PrintExprValFile(sep->d.UNDEF_DATA_AT.left, env, fp);
      fprintf(fp, " ");
      PrintSimpleCtypeFile(sep->d.UNDEF_DATA_AT.ty, env, fp);
   } else if (sep->t == T_ARR) {
      fprintf(fp, "Arr ");
      PrintExprValFile(sep->d.ARR.addr, env, fp);
      fprintf(fp, " ");
      PrintExprValFile(sep->d.ARR.size, env, fp);
      fprintf(fp, " ");
      PrintExprValFile(sep->d.ARR.value, env, fp);
      fprintf(fp, " ");
      PrintSimpleCtypeFile(sep->d.ARR.ty, env, fp);
   } else {
      struct logic_var_info * info = find_logic_var_by_id(sep->d.OTHER.sep_id, &env->persist);
      fprintf(fp, "%s ", info->name);
      PrintPolyArgList(sep->d.OTHER.types, sep->d.OTHER.exprs, env, fp);
   }
}

void PrintSep(struct Separation *sep, struct environment * env) {
   PrintSepFile(sep, env, stdout);
}

void PrintSepListFile(struct SepList * list, struct environment * env, FILE * fp) {
   fprintf(fp, "SEP[");
   struct SepList * tmp = list;
   while (tmp != NULL) {
      fprintf(fp, " ");
      PrintSepFile(tmp->head, env, fp);
      fprintf(fp, "%s", tmp->next == NULL ? " " : ";\n");
      tmp = tmp->next;
   }
   fprintf(fp, "]\n");
}

void PrintSepList(struct SepList * list, struct environment * env) {
   PrintSepListFile(list, env, stdout);
}

void PrintFuncSpecFile(struct func_spec * spec, struct environment * env, FILE * fp) {
   if (spec == NULL) {
      fprintf(fp, "NULL");
      return;
   }
   fprintf(fp, "WithT: ");
   PrintExistListFile(spec->witht, env, fp);
   fprintf(fp, "With: ");
   PrintExistListFile(spec->with, env, fp);
   fprintf(fp, "Require: \n");
   PrintAsrtListFile(spec->pre, env, fp);
   fprintf(fp, "Ensure: \n");
   PrintAsrtListFile(spec->post, env, fp);
   fprintf(fp, "ret_value: ");
   PrintExprValFile(spec->__return, env, fp);
   fprintf(fp, "\n");
}

void PrintFuncSpec(struct func_spec * spec, struct environment * env) {
   PrintFuncSpecFile(spec, env, stdout);
}

void PrintFPSpecFile(struct FPSpec * fp_spec, struct environment * env, FILE * fp) {
   fprintf(fp, "\n");
   PrintExprValFile(fp_spec->fp_addr, env, fp);
   fprintf(fp, "|= ");
}

void PrintFPSpec(struct FPSpec * fp_spec, struct environment * env) {
   PrintFPSpecFile(fp_spec, env, stdout);
}

void PrintFpSpecSimpleFile(struct FPSpec * fp_spec, struct environment * env, FILE * fp) {
   PrintExprValFile(fp_spec->fp_addr, env, fp);
   fprintf(fp, "|= ...  ");
}

void PrintFpSpecSimple(struct FPSpec * fp_spec, struct environment * env) {
   PrintFpSpecSimpleFile(fp_spec, env, stdout);
}

void PrintFPSpecList(struct FPSpecList * fp_specs, struct environment * env, FILE * fp) {
   fprintf(fp, "FP_SPEC[");
   struct FPSpecListNode * it;
   for (it = fp_specs->head; it != NULL; it = it->next) {
      PrintFPSpecFile(it->data, env, fp);
      puts("");
   }
   putchar(']');
   puts("");
}

void PrintFPSpecListSimple(struct FPSpecList * fp_specs, struct environment * env, FILE * fp) {
   fprintf(fp, "FP_SPEC[");
   struct FPSpecListNode * it;
   for (it = fp_specs->head; it != NULL; it = it->next) {
      PrintFpSpecSimpleFile(it->data, env, fp);
   }
   putchar(']');
   puts("");
}

void PrintAsrtFile(struct Assertion * asrt, struct environment * env, FILE * fp) {
#ifdef DEBUG_MEMORY
   PrintAsrtAllMemInfo(asrt);
#endif
   PrintExistListFile(asrt->exist_list, env, fp);
   PrintPropListFile(asrt->prop_list, env, fp);
   PrintLocalListFile(asrt->local_list, env, fp);
   PrintSepListFile(asrt->sep_list, env, fp);
   PrintFPSpecListSimple(asrt->fp_spec_list, env, fp);
}

void PrintAsrt(struct Assertion * asrt, struct environment * env) {
   PrintAsrtFile(asrt, env, stdout);
}

void PrintAsrtFPFile(struct Assertion * asrt, struct environment * env, FILE * fp) {
   PrintExistListFile(asrt->exist_list, env, fp);
   PrintPropListFile(asrt->prop_list, env, fp);
   PrintLocalListFile(asrt->local_list, env, fp);
   PrintSepListFile(asrt->sep_list, env, fp);
   PrintFPSpecList(asrt->fp_spec_list, env, fp);
}

void PrintAsrtFP(struct Assertion * asrt, struct environment * env) {
   PrintAsrtFPFile(asrt, env, stdout);
}

void PrintAsrtListFile(struct AsrtList * list, struct environment * env, FILE * fp) {
   struct AsrtList * tmp;
   for (tmp = list; tmp != NULL; tmp = tmp->next) {
      puts("-------Assertion begin---------");
      PrintAsrtFile(tmp->head, env, fp);
      puts("-------Assertion end ----------");
   }
}

void PrintAsrtList(struct AsrtList * list, struct environment * env) {
   PrintAsrtListFile(list, env, stdout);
}

void PrintAsrtListFileFP(struct AsrtList * list, struct environment * env, FILE * fp) {
   struct AsrtList * tmp;
   for (tmp = list; tmp != NULL; tmp = tmp->next) {
      puts("-------Assertion begin---------");
      PrintAsrtFPFile(tmp->head, env, fp);
      puts("-------Assertion end ----------");
   }
}

void PrintFuncRetTypeFile(struct FuncRetType * ret, struct environment * env, FILE * fp) {
   if (ret == NULL) return;
   PrintFuncRetTypeFile(ret->next, env, fp);
   fprintf(fp, "Return Value: ");
   PrintExprValFile(ret->val, env, fp);
   puts("");
   PrintAsrtFile(ret->asrt, env, fp);
}

void PrintFuncRetType(struct FuncRetType * ret, struct environment * env) {
   PrintFuncRetTypeFile(ret, env, stdout);
}

void PrintAsrtTupleFile(struct AsrtTuple * asrt_nbcr, struct environment * env, FILE * fp) {
   puts("----------------------------------------------------");
   puts("---------Assertion normal---------------");
   PrintAsrtListFile(asrt_nbcr->nrm, env, fp);
   puts("---------Assertion break----------------");
   PrintAsrtListFile(asrt_nbcr->brk, env, fp);
   puts("---------Assertion continue-------------");
   PrintAsrtListFile(asrt_nbcr->cnt, env, fp);
   // puts("---------Assertion return---------------");
   // struct FuncRetTypeList * i;
   // int cnt = 0;
   // i = asrt_nbcr->ret;
   // while (i != NULL) {
   //    ++cnt;
   //    fprintf(fp, "Return Position %d\n", cnt);
   //    struct FuncRetType * j;
   //    j = i->head;
   //    while (j != NULL) {
   //       puts("-------Assertion begin---------");
   //       fprintf(fp, "Return Value: ");
   //       PrintExprValFile(j->val, env, fp);
   //       puts("");
   //       PrintAsrtFile(j->asrt, env, fp);
   //       puts("-------Assertion end ----------");
   //       j = j->next;
   //    }
   //    i = i->next;
   // }
   puts("----------------------------------------------------");
}

void PrintAsrtTuple(struct AsrtTuple * asrt_nbcr, struct environment * env) {
   PrintAsrtTupleFile(asrt_nbcr, env, stdout);
}

void PrintPolyTypeNoEnv(struct PolyType * type, FILE *fp) {
   switch (type->t) {
      case POLY_VAR: {
         fprintf(fp, "PolyVar %d", type->d.VAR.id);
         break;
      }
      case POLY_FUNCAPP: {
         fprintf(fp, "PolyFunc %d", type->d.FUNCAPP.func);
         if (!PolyTypeListIsEmpty(type->d.FUNCAPP.args)) {
            fprintf(fp, "(");
            struct PolyTypeListNode * list = type->d.FUNCAPP.args->head;
            while (list != NULL) {
               PrintPolyTypeNoEnv(list->data, fp);
               fprintf(fp, " ");
               list = list->next;
            }
            fprintf(fp, ")");
         }
         break;
      }
      case POLY_ARROW:
         fprintf(fp, "(");
         PrintPolyTypeNoEnv(type->d.ARROW.left, fp);
         fprintf(fp, " -> ");
         PrintPolyTypeNoEnv(type->d.ARROW.right, fp);
         fprintf(fp, ")");
         break;
   }
}

void PrintExprValFileNoEnv(struct ExprVal *expr, FILE *fp) {
   if (expr == NULL) {
      fprintf(fp, "NULL");
      return;
   }
   switch (expr->t) {
      case EZ_VAL:
         fprintf(fp, "(Ez_val %llu)", expr->d.EZ_VAL.number);
         break;
      case SIZE_OF:
         fprintf(fp, "(Size_of ");
         PrintSimpleCtypeNoEnvFile(expr->d.SIZE_OF.type, fp);
         fprintf(fp, ")");
         break;
      case VFIELD_ADDRESS: {
         fprintf(fp, "&(");
         PrintExprValFileNoEnv(expr->d.VFIELD_ADDRESS.expr, fp);
         fprintf(fp, "-> field_%d)", expr->d.VFIELD_ADDRESS.field_id);
         break;
      }
      case VUOP:
         fprintf(fp, "(");
         InnerPrintUnOp(expr->d.VUOP.op, fp);
         PrintExprValFileNoEnv(expr->d.VUOP.expr, fp);
         fprintf(fp, ")");
         break;
      case VBOP:
         fprintf(fp, "(");
         PrintExprValFileNoEnv(expr->d.VBOP.expr1, fp);
         fprintf(fp, " ");
         InnerPrintBinOp(expr->d.VBOP.op, fp);
         fprintf(fp, " ");
         PrintExprValFileNoEnv(expr->d.VBOP.expr2, fp);
         fprintf(fp, ")");
         break;
      case FUNCAPP: {
         fprintf(fp, "Func %d", expr->d.FUNCAPP.id);
         PrintPolyArgListNoEnv(expr->d.FUNCAPP.types, expr->d.FUNCAPP.args, fp);
         break;
      }
      case LINDEX:
         fprintf(fp, "(");
         PrintExprValFileNoEnv(expr->d.LINDEX.list, fp);
         fprintf(fp, "[");
         PrintExprValFileNoEnv(expr->d.LINDEX.index, fp);
         fprintf(fp, "])");
         break;
      default:
         break;
   }  
}

void PrintExprValFileListNoEnv(struct ExprValList * list, FILE *fp) {
   fprintf(fp, "(");
   struct ExprValListNode * tmp = list->head;
   while (tmp != NULL) {
      PrintExprValFileNoEnv(tmp->data, fp);
      if (tmp->next != NULL) fprintf(fp, ", ");
      tmp = tmp->next;
   }
   putchar(')');
}

void PrintPolyArgListNoEnv(struct PolyTypeList * types, struct ExprValList * args, FILE *fp) {
   if (PolyTypeListIsEmpty(types) && ExprValListIsEmpty(args)) return;
   fprintf(fp, "(");
   struct PolyTypeListNode * tmp = types->head;
   while (tmp != NULL) {
      PrintPolyTypeNoEnv(tmp->data, fp);
      if (tmp->next != NULL || !ExprValListIsEmpty(args)) fprintf(fp, ", ");
      tmp = tmp->next;
   }
   struct ExprValListNode * tmp2 = args->head;
   while (tmp2 != NULL) {
      PrintExprValFileNoEnv(tmp2->data, fp);
      if (tmp2->next != NULL) fprintf(fp, ", ");
      tmp2 = tmp2->next;
   }
   fprintf(fp, ")");
}

void PrintExistListNoEnv(struct ExistList * list, FILE *fp) {
   fprintf(fp, "EX ");
   struct ExistList * tmp = list;
   while (tmp != NULL) {
      fprintf(fp, "%d", tmp->id);
      putchar(' ');
      tmp = tmp->next;
   }
   puts("");
}

void PrintPropNoEnv(struct Proposition * prop, FILE *fp) {
   if (prop == NULL) {
      fprintf(fp, "NULL");
      return;
   }
   switch (prop->t) {
      case T_PROP_TRUE:
         fprintf(fp, "prop_true");
         break;
      case T_PROP_FALSE:
         fprintf(fp, "prop_false");
         break;
      case T_PROP_UNARY:
         PrintPropUOp(prop->d.UNARY.op, fp);
         fprintf(fp, "(");
         PrintPropNoEnv(prop->d.UNARY.prop, fp);
         fprintf(fp, ")");
         break;
      case T_PROP_BINARY:
         PrintPropNoEnv(prop->d.BINARY.prop1, fp);
         fprintf(fp, " ");
         PrintPropBinOp(prop->d.BINARY.op, fp);
         fprintf(fp, " ");
         PrintPropNoEnv(prop->d.BINARY.prop2, fp);
         break;
      case T_PROP_PTR:
         fprintf(fp, "%s ", PrintPropPtrOp_str(prop->d.PTR.op));
         PrintExprValFileNoEnv(prop->d.PTR.expr, fp);
         break;
      case T_PROP_COMPARE:
         PrintExprValFileNoEnv(prop->d.COMPARE.expr1, fp);
         fprintf(fp, " ");
         PrintPropCmpOp(prop->d.COMPARE.op, fp);
         fprintf(fp, " ");
         PrintExprValFileNoEnv(prop->d.COMPARE.expr2, fp);
         break;
      case T_PROP_QUANTIFIER:
         if (prop->d.QUANTIFIER.op == PROP_FORALL) {
            fprintf(fp, "forall ");
         } else {
            fprintf(fp, "exists ");
         }
         fprintf(fp, "%d ", prop->d.QUANTIFIER.ident);
         fprintf(fp, ", ");
         PrintPropNoEnv(prop->d.QUANTIFIER.prop, fp);
         break;
      case T_PROP_OTHER: {
         fprintf(fp, "PROP_OTHER%d ", prop->d.OTHER.predicate);
         PrintPolyArgListNoEnv(prop->d.OTHER.types, prop->d.OTHER.args, fp);
      }
      default:
         break;
   }
}

void PrintPropListNoEnv(struct PropList * list, FILE *fp) {
   fprintf(fp, "PROP[");
   struct PropList * tmp = list;
   while (tmp != NULL) {
      putchar(' ');
      PrintPropNoEnv(tmp->head, fp);
      putchar(tmp->next == NULL ? ' ' : ';');
      tmp = tmp->next;
   }
   putchar(']');
   puts("");
}

void PrintLocalListNoEnv(struct LocalLinkedHashMap * list, FILE *fp) {
   fprintf(fp, "LOCAL[");
   struct LocalLinkedHashMapNode *tmp = list->head;
   while (tmp != NULL) {
      putchar(' ');
      fprintf(fp, "Temp %d ", tmp->id);
      PrintExprValFileNoEnv(tmp->value, fp);
      putchar(tmp->next == NULL ? ' ' : ';');
      tmp = tmp->next;
   }
   putchar(']');
   puts("");
}

void PrintSepNoEnv(struct Separation *sep, FILE *fp) {
   if (sep == NULL) return;
   if (sep->t == T_DATA_AT) {
      fprintf(fp, "Data_at ");
      PrintExprValFileNoEnv(sep->d.DATA_AT.left, fp);
      putchar(' ');
      PrintExprValFileNoEnv(sep->d.DATA_AT.right, fp);
      fprintf(fp, " ");
      PrintSimpleCtypeNoEnvFile(sep->d.DATA_AT.ty, fp);
   } else if (sep->t == T_UNDEF_DATA_AT) {
      fprintf(fp, "Undef_Data_at ");
      PrintExprValFileNoEnv(sep->d.UNDEF_DATA_AT.left, fp);
      fprintf(fp, " ");
      PrintSimpleCtypeNoEnvFile(sep->d.UNDEF_DATA_AT.ty, fp);
   } else if (sep->t == T_ARR) {
      fprintf(fp, "Arr ");
      PrintExprValFileNoEnv(sep->d.ARR.addr, fp);
      fprintf(fp, " ");
      PrintExprValFileNoEnv(sep->d.ARR.size, fp);
      fprintf(fp, " ");
      PrintExprValFileNoEnv(sep->d.ARR.value, fp);
      fprintf(fp, " ");
      PrintSimpleCtypeNoEnvFile(sep->d.ARR.ty, fp);
   } else {
      fprintf(fp, "Sep Other %d ", sep->d.OTHER.sep_id);
      PrintPolyArgListNoEnv(sep->d.OTHER.types, sep->d.OTHER.exprs, fp);
   }
}

void PrintSepListNoEnv(struct SepList * list, FILE *fp) {
   fprintf(fp, "SEP[");
   struct SepList * tmp = list;
   while (tmp != NULL) {
      putchar(' ');
      PrintSepNoEnv(tmp->head, fp);
      putchar(tmp->next == NULL ? ' ' : ';');
      tmp = tmp->next;
   }
   putchar(']');
   puts("");
}

void PrintAsrtNoEnv(struct Assertion * asrt, FILE *fp) {
   PrintExistListNoEnv(asrt->exist_list, fp);
   PrintPropListNoEnv(asrt->prop_list, fp);
   PrintLocalListNoEnv(asrt->local_list, fp);
   PrintSepListNoEnv(asrt->sep_list, fp);
}

void PrintAsrtListNoEnv(struct AsrtList * list, FILE *fp) {
   struct AsrtList * tmp;
   for (tmp = list; tmp != NULL; tmp = tmp->next) {
      puts("-------Assertion begin---------");
      PrintAsrtNoEnv(tmp->head, fp);
      puts("-------Assertion end ----------");
   }
}

void PrintExprValFileAllMemInfo(struct ExprVal * expr, FILE *fp) {
   fprintf(fp, "ExprVal : %p\n", expr);
   if (expr == NULL) return;
   switch (expr->t) {
      case TIME_COST:
      case EZ_VAL:
         break;
      case VFIELD_ADDRESS:
         PrintExprValFileAllMemInfo(expr->d.VFIELD_ADDRESS.expr, fp);
         break;
      case VUOP:
         PrintExprValFileAllMemInfo(expr->d.VUOP.expr, fp);
         break;
      case VBOP:
         PrintExprValFileAllMemInfo(expr->d.VBOP.expr1, fp);
         PrintExprValFileAllMemInfo(expr->d.VBOP.expr2, fp);
         break;
      case FUNCAPP: {
         struct ExprValListNode * list = expr->d.FUNCAPP.args->head;
         while (list != NULL) {
            PrintExprValFileAllMemInfo(list->data, fp);
            list = list->next;
         }
         break;
      }
      case LINDEX:
         PrintExprValFileAllMemInfo(expr->d.LINDEX.list, fp);
         PrintExprValFileAllMemInfo(expr->d.LINDEX.index, fp);
         break;
      case SIZE_OF:
         break;
   }
}

void PrintPropAllMemInfo(struct Proposition * prop, FILE *fp) {
   fprintf(fp, "Proposition : %p\n", prop);
   if (prop == NULL) return;
   switch (prop->t) {
      case T_PROP_TRUE:
         break;
      case T_PROP_FALSE:
         break;
      case T_PROP_UNARY:
         PrintPropAllMemInfo(prop->d.UNARY.prop, fp);
         break;
      case T_PROP_BINARY:
         PrintPropAllMemInfo(prop->d.BINARY.prop1, fp);
         PrintPropAllMemInfo(prop->d.BINARY.prop2, fp);
         break;
      case T_PROP_PTR:
         PrintExprValFileAllMemInfo(prop->d.PTR.expr, fp);
         break;
      case T_PROP_COMPARE:
         PrintExprValFileAllMemInfo(prop->d.COMPARE.expr1, fp);
         PrintExprValFileAllMemInfo(prop->d.COMPARE.expr2, fp);
         break;
      case T_PROP_QUANTIFIER:
         PrintPropAllMemInfo(prop->d.QUANTIFIER.prop, fp);
         break;
      default:
         break;
   }
}

void PrintSepAllMemInfo(struct Separation * sep, FILE *fp) {
   fprintf(fp, "Separation : %p\n", sep);
   if (sep == NULL) return;
   if (sep->t == T_DATA_AT) {
      PrintExprValFileAllMemInfo(sep->d.DATA_AT.left, fp);
      PrintExprValFileAllMemInfo(sep->d.DATA_AT.right, fp);
   } else if (sep->t == T_UNDEF_DATA_AT) {
      PrintExprValFileAllMemInfo(sep->d.UNDEF_DATA_AT.left, fp);
   } else if (sep->t == T_ARR) {
      PrintExprValFileAllMemInfo(sep->d.ARR.addr, fp);
      PrintExprValFileAllMemInfo(sep->d.ARR.size, fp);
      PrintExprValFileAllMemInfo(sep->d.ARR.value, fp);
   } else {
      struct ExprValListNode * list = sep->d.OTHER.exprs->head;
      while (list != NULL) {
         PrintExprValFileAllMemInfo(list->data, fp);
         list = list->next;
      }
   }
}

void PrintAsrtAllMemInfoFile(struct Assertion * asrt, FILE *fp) {
   fprintf(fp, "Assertion : %p\n", asrt);
   struct PropList * prop_iter;
   for (prop_iter = asrt->prop_list; prop_iter != NULL; prop_iter = prop_iter->next) {
      PrintPropAllMemInfo(prop_iter->head, fp);
   }
   fprintf(fp, "Local : %p\n", asrt->local_list);
   struct SepList * sep_iter;
   for (sep_iter = asrt->sep_list; sep_iter != NULL; sep_iter = sep_iter->next) {
      PrintSepAllMemInfo(sep_iter->head, fp);
   }
}

void PrintAsrtAllMemInfo(struct Assertion * asrt) {
   PrintAsrtAllMemInfoFile(asrt, stdout);
}

struct atype * InnerExprInfer(struct ExprVal *val, struct environment *env){
  if (val == NULL) return NULL;
  switch (val->t) {
    case VUOP:{
      struct atype * type = InnerExprInfer(val->d.VUOP.expr, env);
      switch (val->d.VUOP.op) {
        case Oneg:
        case Onint: {
          if (atype_is_atom(type) && type->d.ATOM.info->id == BUILTINTYPE_Z) {
            return type;
          } else {
            fprintf(stderr, "unexpected unary operation type.\n");
            fprintf(stderr, "the expression is ");
            PrintExprValFile(val, env, stderr);
            fprintf(stderr, "the type is ");
            print_atype_File(stderr, type);
            fprintf(stderr, "\n");
            exit(1);
          }
        }
        case Onot: {
          if (atype_is_atom(type) && (type->d.ATOM.info->id == BUILTINTYPE_BOOL || type->d.ATOM.info->id == BUILTINTYPE_Z)) {
            return type;
          } else {
            fprintf(stderr, "unexpected unary operation type.\n");
            fprintf(stderr, "the expression is ");
            PrintExprValFile(val, env, stderr);
            fprintf(stderr, "the type is ");
            print_atype_File(stderr, type);
            fprintf(stderr, "\n");
            exit(1);
          }
        }
      }
      return type;
    }
    case VBOP: {
      struct atype * type1 = InnerExprInfer(val->d.VBOP.expr1, env);
      struct atype * type2 = InnerExprInfer(val->d.VBOP.expr2, env);
      if (atype_is_atom(type1) && atype_is_atom(type2) && type1->d.ATOM.info->id == BUILTINTYPE_Z && type2->d.ATOM.info->id == BUILTINTYPE_Z) {
        return type1;
      } else {
        fprintf(stderr, "unexpected binary operation type.\n");
        fprintf(stderr, "the expression is ");
        PrintExprValFile(val, env, stderr);
        fprintf(stderr, "the type is ");
        print_atype_File(stderr, type1);
        fprintf(stderr, " ");
        print_atype_File(stderr, type2);
        fprintf(stderr, "\n");
        exit(1);
      }
      return NULL;
    }
    case FUNCAPP: {
      struct logic_var_info * var_info = find_logic_var_by_id(val->d.FUNCAPP.id, &env->persist);
      if (var_info == NULL) {
        fprintf(stderr, "unexpected function id.\n");
        fprintf(stderr, "the expression is ");
        PrintExprValFile(val, env, stderr);
        fprintf(stderr, "the id is %d\n", val->d.FUNCAPP.id);
        exit(1);
      }
      struct atype * type = var_info->atype;
      if (type == NULL) {
        fprintf(stderr, "unexpected function type.\n");
        fprintf(stderr, "the expression is ");
        PrintExprValFile(val, env, stderr);
        fprintf(stderr, "the type is NULL\n");
        exit(1);
      }
      // printf("\n============================\n");
      // print_atype(type);
      // printf("\n============================\n");
      struct qvar_list *type_arg;
      type = cpat_instantiate(var_info->qv, type, &type_arg);
      for (struct PolyTypeListNode *i = val->d.FUNCAPP.types->head; i != NULL;
           i = i->next, type_arg = type_arg->next) {
        cpat_unify(type_arg->qv, atype_of_polytype(i->data, &env->persist));
      }
      // printf("\n============================\n");
      // print_atype(type);
      // printf("\n============================\n");
      struct ExprValListNode * node = val->d.FUNCAPP.args->head;
      while (node != NULL) {
        struct atype * type1 = InnerExprInfer(node->data, env);
        if (type1 == NULL) {
          fprintf(stderr, "unexpected function argument type.\n");
          fprintf(stderr, "the expression is ");
          PrintExprValFile(val, env, stderr);
          fprintf(stderr, "the type is NULL\n");
          exit(1);
        }
        if (type -> t == AT_ARROW && atype_equal(type->d.ARROW.from, type1)) {
          type = type->d.ARROW.to;
        } else {
          fprintf(stderr, "unexpected function argument type.\n");
          fprintf(stderr, "the function expression is ");
          PrintExprValFile(val, env, stderr);
          fprintf(stderr, "\n");
          fprintf(stderr, "the function type is ");
          print_atype_File(stderr, type);
          fprintf(stderr, "\n");
          fprintf(stderr, "the type of type is %d\n", type->t);
          fprintf(stderr, "the atype_equal result : %d\n", atype_equal(type->d.ARROW.from, type1));
          fprintf(stderr, "the argument expression is ");
          PrintExprValFile(node->data, env, stderr);
          fprintf(stderr, "\n");
          fprintf(stderr, "the argument type is ");
          print_atype_File(stderr, type1);
          fprintf(stderr, "\n");
          fprintf(stderr, "the argument type should be ");
          print_atype_File(stderr, type->d.ARROW.from);
          fprintf(stderr, "\n");
          exit(1);
        } 
        node = node->next;
      }
      return type;
    }
    case LINDEX: {
      struct atype * type = InnerExprInfer(val->d.LINDEX.index, env);
      if (type == NULL || !atype_is_atom(type) || type->d.ATOM.info->id != BUILTINTYPE_Z) {
        fprintf(stderr, "unexpected array index type.\n");
        fprintf(stderr, "the expression is ");
        PrintExprValFile(val, env, stderr);
        fprintf(stderr, "the type is ");
        print_atype_File(stderr, type);
        fprintf(stderr, "\n");
        exit(1);
      }
      type = InnerExprInfer(val->d.LINDEX.list, env);
      if (type == NULL) {
        fprintf(stderr, "unexpected array type.\n");
        fprintf(stderr, "the expression is ");
        PrintExprValFile(val, env, stderr);
        fprintf(stderr, "the type is NULL\n");
        exit(1);
      }
      if (type->t == AT_APP && atype_is_list(type->d.APP.tfn)) {
        return type->d.APP.rand;
      } else {
        fprintf(stderr, "unexpected array type.\n");
        fprintf(stderr, "the expression is ");
        PrintExprValFile(val, env, stderr);
        fprintf(stderr, "the type is ");
        print_atype_File(stderr, type);
        fprintf(stderr, "\n");
        exit(1);
      }
    }
    default : {
      struct atype_info *info = (struct atype_info *) malloc(sizeof(struct atype_info));
      info->id = BUILTINTYPE_Z;
      return ATAtom(info);
    }
  }
  return NULL;
}

#undef PRINT_NAME