#include "CexprPrinter.h"

void PrintSignednessFile(enum Signedness s, FILE *fp) {
   if (s == Signed) {
      fprintf(fp,"signed ");
   } else if (s == Unsigned) {
      fprintf(fp,"unsigned ");
   } else {
      fprintf(stderr, "error at %s %d\n", __FILE__, __LINE__);
      exit(1);
   }
}

void PrintSignedness(enum Signedness s) {
   PrintSignednessFile(s, stdout);
}

void PrintSimpleCtypeFile(struct SimpleCtype * ty, struct environment * env, FILE * fp) {
   switch (ty->t) {
   case C_void:
      fprintf(fp,"void");
      break;
   case C_int8:
      PrintSignednessFile(ty->d.CINT8.s, fp);
      fprintf(fp,"I8");
      break;
   case C_int16:
      PrintSignednessFile(ty->d.CINT16.s, fp);
      fprintf(fp,"int16");
      break;
   case C_int32:
      PrintSignednessFile(ty->d.CINT32.s, fp);
      fprintf(fp,"int");
      break;
   case C_int64:
      PrintSignednessFile(ty->d.CINT64.s, fp);
      fprintf(fp,"int64");
      break;
   case C_pointer:
      PrintSimpleCtypeFile(ty->d.CPOINTER.type, env, fp);
      fprintf(fp,"*");
      break;
   case C_array:
      PrintSimpleCtypeFile(ty->d.CARRAY.type, env, fp);
      fprintf(fp,"[%d]", ty->d.CARRAY.length);
      break;
   case C_function: {
      struct SimpleCtypeListNode *i;
      fprintf(fp,"func: ");
      PrintSimpleCtypeFile(ty->d.CFUNC.ret_type, env, fp);
      fprintf(fp,"(");
      for (i = ty->d.CFUNC.arg_list->head; i != NULL; i = i->next) {
         PrintSimpleCtypeFile(i->data, env, fp);
         if (i->next != NULL) {
            fprintf(fp,", ");
         }
      }
      fprintf(fp,")");
      break;
   }
   case C_struct: {
      struct struct_union_info * info;
      info = find_struct_by_id(ty->d.CSTRUCT.struct_id, &env->persist);
      fprintf(fp,"struct %s", info->name);
      break;
   }
   case C_union: {
      struct struct_union_info * info;
      info = find_union_by_id(ty->d.CUNION.union_id, &env->persist);
      fprintf(fp,"union %s", info->name);
      break;
   }
   case C_enum: {
      struct enum_info * info;
      info = find_enum_by_id(ty->d.CENUM.enum_id, &env->persist);
      fprintf(fp,"enum %s", info->name);
      break;
   }
   default:
      break;
   }
}

void PrintSimpleCtype(struct SimpleCtype * ty, struct environment * env) {
   PrintSimpleCtypeFile(ty, env, stdout);
}

void PrintSimpleCtypeListFile(struct SimpleCtypeList * list, struct environment * env, FILE *fp) {
   struct SimpleCtypeListNode * i;
   for (i = list->head; i != NULL; i = i->next) {
      PrintSimpleCtypeFile(i->data, env, fp);
      if (i->next != NULL) {
         fprintf(fp,", ");
      }
   }
}

void PrintSimpleCtypeList(struct SimpleCtypeList * list, struct environment * env) {
   PrintSimpleCtypeListFile(list, env, stdout);
}

void PrintSimpleCtypeNoEnvFile(struct SimpleCtype * ty, FILE *fp) {
   switch (ty->t) {
   case C_void:
      fprintf(fp,"void");
      break;
   case C_int8:
      PrintSignednessFile(ty->d.CINT8.s, fp);
      fprintf(fp,"I8");
      break;
   case C_int16:
      PrintSignednessFile(ty->d.CINT16.s, fp);
      fprintf(fp,"int16");
      break;
   case C_int32:
      PrintSignednessFile(ty->d.CINT32.s, fp);
      fprintf(fp,"int");
      break;
   case C_int64:
      PrintSignednessFile(ty->d.CINT64.s, fp);
      fprintf(fp,"int64");
      break;
   case C_pointer:
      PrintSimpleCtypeNoEnvFile(ty->d.CPOINTER.type, fp);
      fprintf(fp,"*");
      break;
   case C_array:
      PrintSimpleCtypeNoEnvFile(ty->d.CARRAY.type, fp);
      fprintf(fp,"[%d]", ty->d.CARRAY.length);
      break;
   case C_function: {
      struct SimpleCtypeListNode *i;
      fprintf(fp,"func: ");
      PrintSimpleCtypeNoEnvFile(ty->d.CFUNC.ret_type, fp);
      fprintf(fp,"(");
      for (i = ty->d.CFUNC.arg_list->head; i != NULL; i = i->next) {
         PrintSimpleCtypeNoEnvFile(i->data, fp);
         if (i->next != NULL) {
            fprintf(fp,", ");
         }
      }
      fprintf(fp,")");
      break;
   }
   case C_struct: {
      fprintf(fp,"struct %d", ty->d.CSTRUCT.struct_id);
      break;
   }
   case C_union: {
      fprintf(fp,"union %d", ty->d.CUNION.union_id);
      break;
   }
   case C_enum: {
      fprintf(fp,"enum %d", ty->d.CENUM.enum_id);
      break;
   }
   default:
      break;
   }
}

void PrintSimpleCtypeNoEnv(struct SimpleCtype * ty) {
   PrintSimpleCtypeNoEnvFile(ty, stdout);
}

void PrintSimpleCtypeListNoEnvFile(struct SimpleCtypeList * list, FILE *fp) {
   struct SimpleCtypeListNode * i;
   for (i = list->head; i != NULL; i = i->next) {
      PrintSimpleCtypeNoEnvFile(i->data, fp);
      if (i->next != NULL) {
         fprintf(fp,", ");
      }
   }
}

void PrintSimpleCtypeListNoEnv(struct SimpleCtypeList * list) {
   PrintSimpleCtypeListNoEnvFile(list, stdout);
}

void PrintUnOpFile(enum UnOpType op, FILE *fp) {
   switch (op) {
   case T_UMINUS:
      fprintf(fp,"-");
      break;
   case T_UPLUS:
      fprintf(fp,"+");
      break;
   case T_NOTBOOL:
      fprintf(fp,"!");
      break;
   case T_NOTINT:
      fprintf(fp,"~");
      break;      
   default:
      break;
   }
}

void PrintBinOpFile(enum BinOpType op, FILE *fp) {
   switch (op) {
   case T_PLUS:
      fprintf(fp,"+");
      break;
   case T_MINUS:
      fprintf(fp,"-");
      break;
   case T_MUL:
      fprintf(fp,"*");
      break;
   case T_DIV:
      fprintf(fp,"/");
      break;
   case T_MOD:
      fprintf(fp,"%%");
      break;
   case T_LT:
      fprintf(fp,"<");
      break;
   case T_GT:
      fprintf(fp,">");
      break;
   case T_LE:
      fprintf(fp,"<=");
      break;
   case T_GE:
      fprintf(fp,">=");
      break;
   case T_EQ:
      fprintf(fp,"==");
      break;
   case T_NE:
      fprintf(fp,"!=");
      break;
   case T_AND:
      fprintf(fp,"&&");
      break;
   case T_OR:
      fprintf(fp,"||");
      break;
   case T_BAND:
      fprintf(fp,"&");
      break;
   case T_BOR:
      fprintf(fp,"|");
      break;
   case T_XOR:
      fprintf(fp,"^");
      break;
   case T_SHL:
      fprintf(fp,"<<");
      break;
   case T_SHR:
      fprintf(fp,">>");
      break;
   default:
      break;
   }
}

void PrintCexprFile(struct Cexpr * expr, struct environment * env, FILE *fp) {
   switch (expr->t) {
   case C_CONST:
      PrintSimpleCtypeFile(expr->type, env, fp);
      fprintf(fp," %llu", expr->d.C_CONST.number);
      break;
   case C_VAR: {
      struct prog_var_info * var_info = find_prog_var_by_id(expr->d.C_VAR.id, &env->persist);
      fprintf(fp,"%s", var_info->name);
      break;
   }
   case C_DEREF:
      fprintf(fp,"*(");
      PrintCexprFile(expr->d.C_DEREF.expr, env, fp);
      fprintf(fp,")");
      break;
   case C_ADDROF:
      fprintf(fp,"&(");
      PrintCexprFile(expr->d.C_ADDROF.expr, env, fp);
      fprintf(fp,")");
      break;
   case C_UNOP:
      PrintUnOpFile(expr->d.C_UNOP.op, fp);
      PrintCexprFile(expr->d.C_UNOP.expr, env, fp);
      break;
   case C_BINOP:
      PrintCexprFile(expr->d.C_BINOP.expr1, env, fp);
      fprintf(fp," ");
      PrintBinOpFile(expr->d.C_BINOP.op, fp);
      fprintf(fp," ");
      PrintCexprFile(expr->d.C_BINOP.expr2, env, fp);
      break;
   case C_CAST:
      fprintf(fp,"(");
      PrintSimpleCtypeFile(expr->type, env, fp);
      fprintf(fp,")");
      PrintCexprFile(expr->d.C_CAST.expr, env, fp);
      break;
   case C_STRUCTFIELD: {
      struct field_info * info;
      info = find_field_by_id(expr->d.C_STRUCTFIELD.field_id, &env->persist);
      PrintCexprFile(expr->d.C_STRUCTFIELD.expr, env, fp);
      fprintf(fp,".%s", info->name);
      break;
   }
   case C_UNIONFIELD: {
      struct field_info * info;
      info = find_field_by_id(expr->d.C_UNIONFIELD.field_id, &env->persist);
      PrintCexprFile(expr->d.C_UNIONFIELD.expr, env, fp);
      fprintf(fp,".%s", info->name);
      break;
   }
   case C_SIZEOF:
      fprintf(fp,"sizeof(");
      PrintSimpleCtypeFile(expr->d.C_SIZEOF.inner_type, env, fp);
      fprintf(fp,")");
      break;
   case C_INDEX:
      PrintCexprFile(expr->d.C_INDEX.arr_expr, env, fp);
      fprintf(fp,"[");
      PrintCexprFile(expr->d.C_INDEX.inner_expr, env, fp);
      fprintf(fp,"]");
      break;
   case C_CALL: {
      PrintCexprFile(expr->d.C_CALL.func, env, fp);
      fprintf(fp,"(");
      struct CexprListNode * i;
      for (i = expr->d.C_CALL.args_exprs->head; i != NULL; i = i->next) {
         PrintCexprFile(i->data, env, fp);
         if (i->next != NULL) {
            fprintf(fp,", ");
         }
      }
      fprintf(fp,")");
      break;
   }
   case C_TERNARY: {
      PrintCexprFile(expr->d.C_TERNARY.cond, env, fp);
      fprintf(fp," ? ");
      PrintCexprFile(expr->d.C_TERNARY.true_expr, env, fp);
      fprintf(fp," : ");
      PrintCexprFile(expr->d.C_TERNARY.false_expr, env, fp);
      break;
   }
   default:
      break;
   }
}

void PrintCexpr(struct Cexpr * expr, struct environment * env) {
   PrintCexprFile(expr, env, stdout);
}