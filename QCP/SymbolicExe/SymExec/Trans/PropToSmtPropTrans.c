#include "PropToSmtPropTrans.h"
#include "../Utility/InnerAsrtPrinter.h"

extern int exec_info;

static int get_len(int x) {
    int ret = 0;
    if (x == 0) return 1;
    while (x) {
        x /= 10;
        ret++;
    }
    return ret;
}

struct SmtTerm * PolyTypeTransSmtTerm(struct PolyType * type, struct environment * env) {
  struct SmtTerm * res;
  if (type == NULL) {
    res = newSmtTerm(SMT_ConstNum, 0, 0, NULL, NULL, NULL, NULL);
    return res;    
  } else {
    switch (type->t) {
      case POLY_VAR: {
        struct atype_info * type_info = find_atype_by_id(type->d.VAR.id, &env->persist);
        struct UFunction *uf = (struct UFunction *)malloc(sizeof(struct UFunction));
        uf -> name = malloc(sizeof(char) * (strlen(type_info->name) + 2));
        sprintf(uf->name, "%s", type_info->name);
        uf -> numArgs = 0;
        uf -> args = NULL;
        res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, uf, NULL, NULL);
        break;
      }
      case POLY_ARROW: {
        struct UFunction *uf = (struct UFunction *)malloc(sizeof(struct UFunction));
        uf -> name = malloc(sizeof(char) * strlen("arrow_type") + 2);
        sprintf(uf->name, "%s", "arrow_type");
        uf -> numArgs = 2;
        uf -> args = (struct SmtTerm **)malloc(sizeof(struct SmtTerm *) * 2);
        uf -> args[0] = PolyTypeTransSmtTerm(type->d.ARROW.left, env);
        uf -> args[1] = PolyTypeTransSmtTerm(type->d.ARROW.right, env);
        res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, uf, NULL, NULL);
        break;
      }
      case POLY_FUNCAPP: {
        struct atype_info * type_info = find_atype_by_id(type->d.FUNCAPP.func, &env->persist);
        struct UFunction *uf = (struct UFunction *)malloc(sizeof(struct UFunction));
        uf -> name = malloc(sizeof(char) * (strlen(type_info->name) + 2));
        sprintf(uf->name, "%s", type_info->name);
        uf -> numArgs = PolyTypeListLength(type->d.FUNCAPP.args);
        uf -> args = (struct SmtTerm **)malloc(sizeof(struct SmtTerm *) * uf->numArgs);
        int cnt = 0;
        for (struct PolyTypeListNode * now = type->d.FUNCAPP.args->head; now != NULL; now = now->next) {
          uf -> args[cnt++] = PolyTypeTransSmtTerm(now->data, env);
        }
        res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, uf, NULL, NULL);
        break;
      }
    }
    return res;
  }
}

char * SimpleCtypeToStr(struct SimpleCtype * type, struct environment * env) {
  if (type == NULL) return NULL;
  switch (type->t) {
    case C_void:
      return "type_void";
    case C_int8:
      if (type->d.CINT8.s == Unsigned) return "type_u8";
      else return "type_i8";
    case C_int16:
      if (type->d.CINT16.s == Unsigned) return "type_u16";
      else return "type_i16";
    case C_int32:
      if (type->d.CINT32.s == Unsigned) return "type_uint";
      else return "type_int";
    case C_int64:
      if (type->d.CINT64.s == Unsigned) return "type_uint64";
      else return "type_int64";
    case C_pointer:
      return "type_pointer";
    case C_array: {
      char * type_name = SimpleCtypeToStr(type->d.CARRAY.type, env);
      char * res = malloc(sizeof(char) * (strlen(type_name) + 10));
      sprintf(res, "type_array_%s", type_name);
      return res;
    }
    case C_function: {
      return "type_function";
    }
    case C_struct: {
      int len = 13 + get_len(type->d.CSTRUCT.struct_id);
      char * type_name = malloc(sizeof(char) * len);
      sprintf(type_name, "type_struct_%d", type->d.CSTRUCT.struct_id);
      return type_name;
    }
    case C_union: {
      int len = 12 + get_len(type->d.CUNION.union_id);
      char * type_name = malloc(sizeof(char) * len);
      sprintf(type_name, "type_union_%d", type->d.CUNION.union_id);
      return type_name;
    }
    case C_enum: {
      int len = 11 + get_len(type->d.CENUM.enum_id);
      char * type_name = malloc(sizeof(char) * len);
      sprintf(type_name, "type_enum_%d", type->d.CENUM.enum_id);
      return type_name;
    }
  }
}

struct SmtTerm * ExprValTransSmtTerm(struct ExprVal *expr, struct environment * env) {
   struct SmtTerm *res;
   if (expr == NULL) {
      res = newSmtTerm(SMT_ConstNum, 0, 0, NULL, NULL, NULL, NULL);
      return res;
   }
   switch (expr->t) {
     case EZ_VAL: {
      if (expr->d.EZ_VAL.number == 127) {
        res = newSmtTerm(SMT_VarName, 0, 0, "SMT_INT8_MAX", NULL, NULL, NULL);
      } 
      // higher than signed max
        else if (expr->d.EZ_VAL.number >= 32767 && expr->d.EZ_VAL.number <= 32867) {
        res = newSmtTerm(SMT_VarName, 0, 0, "SMT_INT16_MAX", NULL, NULL, NULL);
        res = newSmtTerm(SMT_LiaBTerm, LIA_ADD, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, expr->d.EZ_VAL.number - 32767, NULL, NULL, NULL, NULL));
      } else if (expr->d.EZ_VAL.number >= 2147483647 && expr->d.EZ_VAL.number <= 2147483747u) {
        res = newSmtTerm(SMT_VarName, 0, 0, "SMT_INT32_MAX", NULL, NULL, NULL);
        res = newSmtTerm(SMT_LiaBTerm, LIA_ADD, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, expr->d.EZ_VAL.number - 2147483647, NULL, NULL, NULL, NULL));
      } else if (expr->d.EZ_VAL.number >= 9223372036854775807ll && expr->d.EZ_VAL.number <= 9223372036854775907ull) {
        res = newSmtTerm(SMT_VarName, 0, 0, "SMT_INT64_MAX", NULL, NULL, NULL);
        res = newSmtTerm(SMT_LiaBTerm, LIA_ADD, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, expr->d.EZ_VAL.number - 9223372036854775807ll, NULL, NULL, NULL, NULL));
      }
      // lower than signed max 
        else if (expr->d.EZ_VAL.number < 32767 && expr->d.EZ_VAL.number >= 32667) {
        res = newSmtTerm(SMT_VarName, 0, 0, "SMT_INT16_MAX", NULL, NULL, NULL);
        res = newSmtTerm(SMT_LiaBTerm, LIA_MINUS, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, 32767 - expr->d.EZ_VAL.number, NULL, NULL, NULL, NULL));
      } else if (expr->d.EZ_VAL.number < 2147483647 && expr->d.EZ_VAL.number >= 2147483547) {
        res = newSmtTerm(SMT_VarName, 0, 0, "SMT_INT32_MAX", NULL, NULL, NULL);
        res = newSmtTerm(SMT_LiaBTerm, LIA_MINUS, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, 2147483647 - expr->d.EZ_VAL.number, NULL, NULL, NULL, NULL));
      } else if (expr->d.EZ_VAL.number < 9223372036854775807ll && expr->d.EZ_VAL.number >= 9223372036854775707ll) {
        res = newSmtTerm(SMT_VarName, 0, 0, "SMT_INT64_MAX", NULL, NULL, NULL);
        res = newSmtTerm(SMT_LiaBTerm, LIA_MINUS, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, 9223372036854775807l - expr->d.EZ_VAL.number, NULL, NULL, NULL, NULL));
      } 
      // higher than unsigned max  
        else if (expr->d.EZ_VAL.number >= 65534 && expr->d.EZ_VAL.number <= 65634) {
        res = newSmtTerm(SMT_VarName, 0, 0, "SMT_INT16_MAX", NULL, NULL, NULL);
        res = newSmtTerm(SMT_LiaBTerm, LIA_MULT, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, 2, NULL, NULL, NULL, NULL));
        res = newSmtTerm(SMT_LiaBTerm, LIA_ADD, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, expr->d.EZ_VAL.number - 65534, NULL, NULL, NULL, NULL));
      } else if (expr->d.EZ_VAL.number >= 4294967294u && expr->d.EZ_VAL.number <= 4294967394ull) {
        res = newSmtTerm(SMT_VarName, 0, 0, "SMT_INT32_MAX", NULL, NULL, NULL);
        res = newSmtTerm(SMT_LiaBTerm, LIA_MULT, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, 2, NULL, NULL, NULL, NULL));
        res = newSmtTerm(SMT_LiaBTerm, LIA_ADD, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, expr->d.EZ_VAL.number - 4294967294u, NULL, NULL, NULL, NULL));
      } 
      // lower than unsigned max
      else if (expr->d.EZ_VAL.number < 65534 && expr->d.EZ_VAL.number >= 65434) {
        res = newSmtTerm(SMT_VarName, 0, 0, "SMT_INT16_MAX", NULL, NULL, NULL);
        res = newSmtTerm(SMT_LiaBTerm, LIA_MULT, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, 2, NULL, NULL, NULL, NULL));
        res = newSmtTerm(SMT_LiaBTerm, LIA_MINUS, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, 65534 - expr->d.EZ_VAL.number, NULL, NULL, NULL, NULL));
      } else if (expr->d.EZ_VAL.number < 4294967294u && expr->d.EZ_VAL.number >= 4294967194u) {
        res = newSmtTerm(SMT_VarName, 0, 0, "SMT_INT32_MAX", NULL, NULL, NULL);
        res = newSmtTerm(SMT_LiaBTerm, LIA_MULT, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, 2, NULL, NULL, NULL, NULL));
        res = newSmtTerm(SMT_LiaBTerm, LIA_MINUS, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, 4294967294u - expr->d.EZ_VAL.number, NULL, NULL, NULL, NULL));
      } else if (expr->d.EZ_VAL.number >= 18446744073709551515ull) {
        res = newSmtTerm(SMT_VarName, 0, 0, "SMT_INT64_MAX", NULL, NULL, NULL);
        res = newSmtTerm(SMT_LiaBTerm, LIA_MULT, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, 2, NULL, NULL, NULL, NULL));
        res = newSmtTerm(SMT_LiaBTerm, LIA_MINUS, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, 18446744073709551614ull - expr->d.EZ_VAL.number, NULL, NULL, NULL, NULL));
      } 
        else {
        res = newSmtTerm(SMT_ConstNum, 0, expr->d.EZ_VAL.number, NULL, NULL, NULL, NULL);
      }
       break;
     }
     case SIZE_OF: {
        char * type_name = SimpleCtypeToStr(expr->d.SIZE_OF.type, env);
        res = newSmtTerm(SMT_VarName, 0, 0, type_name, NULL, NULL, NULL);
        break;
     }
     case VFIELD_ADDRESS: {
       struct field_info * field = find_field_by_id(expr->d.VFIELD_ADDRESS.field_id, &env->persist); 

       res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, newUFunction("Vfield_address", 3, ExprValTransSmtTerm(expr->d.VFIELD_ADDRESS.expr, env), newSmtTerm(SMT_VarName, 0, 0, field->parent->name, NULL, NULL, NULL), newSmtTerm(SMT_VarName, 0, 0, field->name, NULL, NULL, NULL)), NULL, NULL);
       break;
     }
     case VUOP: {
       switch (expr->d.VUOP.op) {
          case Oneg :
            res = newSmtTerm(SMT_LiaUTerm, LIA_NEG, 0, NULL, NULL, ExprValTransSmtTerm(expr->d.VUOP.expr, env), NULL);
            break;
          case Onint :
            res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, newUFunction("Onint", 1, ExprValTransSmtTerm(expr->d.VUOP.expr, env), NULL, NULL), NULL, NULL);
            break;
          case Onot :
            res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, newUFunction("Onot", 1, ExprValTransSmtTerm(expr->d.VUOP.expr, env), NULL, NULL), NULL, NULL);
            break;
       }
       break;
     }
     case VBOP:
       switch (expr->d.VBOP.op) {
          case Oadd:
            res = newSmtTerm(SMT_LiaBTerm, LIA_ADD, 0, NULL, NULL, ExprValTransSmtTerm(expr->d.VBOP.expr1, env), ExprValTransSmtTerm(expr->d.VBOP.expr2, env));
            break;
          case Osub:
            res = newSmtTerm(SMT_LiaBTerm, LIA_MINUS, 0, NULL, NULL, ExprValTransSmtTerm(expr->d.VBOP.expr1, env), ExprValTransSmtTerm(expr->d.VBOP.expr2, env));
            break;
          case Omul: 
            res = newSmtTerm(SMT_LiaBTerm, LIA_MULT, 0, NULL, NULL,ExprValTransSmtTerm(expr->d.VBOP.expr1, env), ExprValTransSmtTerm(expr->d.VBOP.expr2, env));
            break;
          case Odiv:
            res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, newUFunction("Odiv", 2, ExprValTransSmtTerm(expr->d.VBOP.expr1, env), ExprValTransSmtTerm(expr->d.VBOP.expr2, env), NULL), NULL, NULL);
            break;
          case Omod:
            res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, newUFunction("Omod", 2, ExprValTransSmtTerm(expr->d.VBOP.expr1, env), ExprValTransSmtTerm(expr->d.VBOP.expr2, env), NULL), NULL, NULL);
            break;
          case Oand:
            res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, newUFunction("Oand", 2, ExprValTransSmtTerm(expr->d.VBOP.expr1, env), ExprValTransSmtTerm(expr->d.VBOP.expr2, env), NULL), NULL, NULL);
            break;
          case Oor:
            res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, newUFunction("Oor", 2, ExprValTransSmtTerm(expr->d.VBOP.expr1, env), ExprValTransSmtTerm(expr->d.VBOP.expr2, env), NULL), NULL, NULL);
            break;
          case Oxor: 
            res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, newUFunction("Oxor", 2, ExprValTransSmtTerm(expr->d.VBOP.expr1, env), ExprValTransSmtTerm(expr->d.VBOP.expr2, env), NULL), NULL, NULL);
            break;
          case Oshl:
            res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, newUFunction("Oshl", 2, ExprValTransSmtTerm(expr->d.VBOP.expr1, env), ExprValTransSmtTerm(expr->d.VBOP.expr2, env), NULL), NULL, NULL);
            break;
          case Oshr:
            res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, newUFunction("Oshr", 2, ExprValTransSmtTerm(expr->d.VBOP.expr1, env), ExprValTransSmtTerm(expr->d.VBOP.expr2, env), NULL), NULL, NULL);
            break;
       }
       break;
     case FUNCAPP: {
       struct UFunction *uf; 
       int num = ExprValListLength(expr->d.FUNCAPP.args) + PolyTypeListLength(expr->d.FUNCAPP.types);
       struct logic_var_info * info = find_logic_var_by_id(expr->d.FUNCAPP.id, &env->persist);
       if (strncmp(info->name, "INT_MAX", 7) == 0) {
          res = newSmtTerm(SMT_VarName, 0, 0, "SMT_INT32_MAX", NULL, NULL, NULL);
          break;
       } else if (strncmp(info->name, "INT_MIN", 7) == 0) {
          res = newSmtTerm(SMT_VarName, 0, 0, "SMT_INT32_MAX", NULL, NULL, NULL);
          res = newSmtTerm(SMT_LiaUTerm, LIA_NEG, 0, NULL, NULL, res, NULL);
          res = newSmtTerm(SMT_LiaBTerm, LIA_MINUS, 0, NULL, NULL, res, newSmtTerm(SMT_ConstNum, 0, 1, NULL, NULL, NULL, NULL));
          break;
       } else if (ExprValListIsEmpty(expr->d.FUNCAPP.args) && PolyTypeListIsEmpty(expr->d.FUNCAPP.types)) {
          char * name = malloc(sizeof(char) * 10);
          sprintf(name, "x_%d", expr->d.FUNCAPP.id);
          res = newSmtTerm(SMT_VarName, 0, 0, name, NULL, NULL, NULL);
          break;
       } else {
          uf = (struct UFunction *)malloc(sizeof(struct UFunction));
          uf -> name = malloc(sizeof(char) * (strlen(info->name) + 1));
          sprintf(uf->name, "%s", info->name);
       }
       uf -> numArgs = num;
       uf -> args = (struct SmtTerm **)malloc(sizeof(struct SmtTerm *) * num);
       int cnt = 0;
       for (struct PolyTypeListNode * now = expr->d.FUNCAPP.types->head; now != NULL; now = now->next) {
        uf -> args[cnt++] = PolyTypeTransSmtTerm(now -> data, env);
       }
       for (struct ExprValListNode * now = expr->d.FUNCAPP.args->head; now != NULL; now = now->next) {
         uf -> args[cnt++] = ExprValTransSmtTerm(now -> data, env);
       }
       res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, uf, NULL, NULL);
       break;
     }
     case LINDEX :{
       res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, newUFunction("LINDEX", 2, ExprValTransSmtTerm(expr->d.LINDEX.list, env), ExprValTransSmtTerm(expr->d.LINDEX.index, env), NULL), NULL, NULL);
       break;
     }
     case TIME_COST :{
       res = newSmtTerm(SMT_UFTerm, 0, 0, NULL, newUFunction("vTime_cost", 0, NULL, NULL, NULL), NULL, NULL);
       break;
     }
   }
   return res;
}

struct SmtProp * PropTransSmtProp(struct Proposition * source_prop, struct environment * env){
  struct SmtProp * res;
  if (source_prop == NULL) {
    res = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, true);
    return res;
  }
  switch (source_prop->t) {
     case T_PROP_TRUE:
        res = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, true);
        break;
     case T_PROP_FALSE:
        res = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, false);
        break;
     case T_PROP_UNARY:
        res = newSmtProp(SMTU_PROP, (source_prop->d.UNARY.op - PROP_NOT) + SMTPROP_NOT, PropTransSmtProp(source_prop->d.UNARY.prop, env), NULL, NULL, NULL, true);
        break;
     case T_PROP_BINARY:
        res = newSmtProp(SMTB_PROP, (source_prop->d.BINARY.op - PROP_AND) + SMTPROP_AND, PropTransSmtProp(source_prop->d.BINARY.prop1, env), PropTransSmtProp(source_prop->d.BINARY.prop2, env), NULL, NULL, true);
        break;
     case T_PROP_PTR:
        switch (source_prop->d.PTR.op) {
          case PROP_NOT_NULL:
            res = newSmtProp(SMTAT_PROP_EQ, SMT_EQ, NULL, NULL, newSmtTerm(SMT_UFTerm, 0,0,NULL,newUFunction("IS_NULL",1, ExprValTransSmtTerm(source_prop->d.PTR.expr, env),NULL,NULL),NULL,NULL), newSmtTerm(SMT_UFTerm,0,0,NULL,Get_False_UF(),NULL,NULL),true);
            break;
          case PROP_IS_NULL: 
            res = newSmtProp(SMTAT_PROP_EQ, SMT_EQ, NULL, NULL, newSmtTerm(SMT_UFTerm, 0,0,NULL,newUFunction("IS_NULL",1, ExprValTransSmtTerm(source_prop->d.PTR.expr, env),NULL,NULL),NULL,NULL), newSmtTerm(SMT_UFTerm,0,0,NULL,Get_True_UF(),NULL,NULL),true);
            break;
          case PROP_MAYBE_NULL:
            res = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, true);
            break;
        } 
        break;
     case T_PROP_COMPARE: {
        // printf("Ready to Constant Fold\n");
        // printf("Expr1: \n");
        // PrintExprVal(source_prop->d.COMPARE.expr1, env);
        // printf("\n");
        // printf("Expr2: \n");
        // PrintExprVal(source_prop->d.COMPARE.expr2, env);
        // printf("\n");
        struct ExprVal * expr1 = ExprValConstantFold(source_prop->d.COMPARE.expr1, &env->persist);
        // printf("After Constant Fold\n");
        // printf("Expr1: \n");
        // PrintExprVal(expr1, env);
        // printf("\n");
        struct ExprVal * expr2 = ExprValConstantFold(source_prop->d.COMPARE.expr2, &env->persist);        
        // printf("Expr2: \n");
        // PrintExprVal(expr2, env);
        // printf("\n");
        switch (source_prop->d.COMPARE.op) {
          case PROP_GE:
            res = newSmtProp(SMTAT_PROP_LIA, SMT_GE, NULL, NULL, ExprValTransSmtTerm(expr1, env), ExprValTransSmtTerm(expr2, env), true);
            break;
          case PROP_GT:
            res = newSmtProp(SMTAT_PROP_LIA, SMT_GT, NULL, NULL, ExprValTransSmtTerm(expr1, env), ExprValTransSmtTerm(expr2, env), true);
            break;
          case PROP_LE:
            res = newSmtProp(SMTAT_PROP_LIA, SMT_LE, NULL, NULL, ExprValTransSmtTerm(expr1, env), ExprValTransSmtTerm(expr2, env), true);
            break;
          case PROP_LT:
            res = newSmtProp(SMTAT_PROP_LIA, SMT_LT, NULL, NULL, ExprValTransSmtTerm(expr1, env), ExprValTransSmtTerm(expr2, env), true);
            break;
          case PROP_EQ:
            res = newSmtProp(SMTAT_PROP_EQ, SMT_EQ, NULL, NULL, ExprValTransSmtTerm(expr1, env), ExprValTransSmtTerm(expr2, env), true);
            break;
          case PROP_NEQ:
            res = newSmtProp(SMTU_PROP, SMTPROP_NOT,newSmtProp(SMTAT_PROP_EQ, SMT_EQ, NULL, NULL, ExprValTransSmtTerm(expr1, env), ExprValTransSmtTerm(expr2, env), true), NULL, NULL, NULL, true);
            break;
        }
        ExprValFree(expr1);
        ExprValFree(expr2);
        break;
     }
     case T_PROP_QUANTIFIER:
        switch (source_prop->d.QUANTIFIER.op) {
          case PROP_FORALL: {
            char * name = malloc(sizeof(char) * 20);
            sprintf(name, "FORALL");
            sprintf(name+6, "i_%d", source_prop->d.QUANTIFIER.ident);
            res = newSmtProp(SMTAT_PROP_EQ, SMT_EQ, NULL, NULL, newSmtTerm(SMT_VarName, 0, 0, name, NULL, NULL, NULL), 
                                                             newSmtTerm(SMT_VarName, 0, 0, "true", NULL, NULL, NULL), true);
            break;
          }
          case PROP_EXISTS: {
            char * name = malloc(sizeof(char) * 20);
            sprintf(name, "EXISTS");
            sprintf(name+6, "i_%d", source_prop->d.QUANTIFIER.ident);
            res = newSmtProp(SMTAT_PROP_EQ, SMT_EQ, NULL, NULL, newSmtTerm(SMT_VarName, 0, 0, name, NULL, NULL, NULL), 
                                                             newSmtTerm(SMT_VarName, 0, 0, "true", NULL, NULL, NULL), true);
            break;
          }
        }
        break;
     case T_PROP_OTHER: {
        struct UFunction *uf = (struct UFunction *)malloc(sizeof(struct UFunction));
        int num = ExprValListLength(source_prop->d.OTHER.args) + PolyTypeListLength(source_prop->d.OTHER.types);
        struct logic_var_info * info = find_logic_var_by_id(source_prop->d.OTHER.predicate, &env->persist);
        uf->name = malloc(sizeof(char) * (strlen(info->name) + 1));
        sprintf(uf->name, "%s", info->name);
        uf->numArgs = num;
        uf->args = (struct SmtTerm **)malloc(sizeof(struct SmtTerm *) * num);
        int cnt = 0;
        struct PolyTypeListNode *i = source_prop->d.OTHER.types->head;
        for (i = source_prop->d.OTHER.types->head; i != NULL; i = i->next) {
          uf->args[cnt++] = PolyTypeTransSmtTerm(i->data, env);
        }
        // printf("Ready for Constant Fold\n");
        // PrintExprValList(source_prop->d.OTHER.args, env);
        struct ExprValList * args = ExprValListConstantFold(source_prop->d.OTHER.args, &env->persist);
        struct ExprValListNode *j = args->head;
        for (j = args->head; j != NULL; j = j->next) {
          uf->args[cnt++] = ExprValTransSmtTerm(j->data, env);
        }
        ExprValListFree(args);
        res = newSmtProp(SMTAT_PROP_EQ, SMT_EQ, NULL, NULL, newSmtTerm(SMT_UFTerm, 0, 0, NULL, uf, NULL, NULL), 
                                                             newSmtTerm(SMT_VarName, 0, 0, "true", NULL, NULL, NULL), true);
        break;
     }
     default:
        fprintf(stderr, "PropTransSmtProp: Some case not handled\n");
  }
  return res;
}

struct SmtProplist * ProplistTransSmtProplist(struct PropList * source_prop_list, struct environment * env){
  if (source_prop_list == NULL) return NULL;
  struct SmtProplist * ret = (struct SmtProplist *) malloc(sizeof(struct SmtProplist));
  ret->prop = PropTransSmtProp(source_prop_list->head, env);
  // PrintProp(source_prop_list->head, env);
  ret->next = ProplistTransSmtProplist(source_prop_list->next, env);
  return ret;
}

// This function will not change the source_prop_list and target_prop_list 
struct Prop_solver_return * PropEntail(struct PropList *source_prop_list, struct PropList *target_prop_list, struct environment * env){
  // printf("Proposition before Trans: \n");
  // PrintPropList(source_prop_list, env);
  // printf("|- \n");
  // PrintPropList(target_prop_list, env);
  // printf("\n");

  // printf("Source Proposition after adhoc: \n");
  /*if (exec_info) {
    printf("Start to solve the following proposition:\n");
    PrintPropList(source_prop_list, env);
    printf("--> \n");
    PrintPropList(target_prop_list, env);
  } */
  struct PropList *src_prop_list = Adhoc_change_src(source_prop_list);
  // PrintPropList(src_prop_list, env);
  // printf("\n");

  struct SmtProp *source = SmtProp_list_to_SmtProp(ProplistTransSmtProplist(src_prop_list, env));
  PropListFree(src_prop_list);
  struct PropList *res_prop_list = PropListNil();
  struct Prop_solver_return *res = (struct Prop_solver_return *) malloc(sizeof(struct Prop_solver_return));

  // printf("Source Proposition after Trans: \n");
  // printSmtProp(source);
  // printf("\n");
  // for debug only

  // printf("Start Target Quantifier adhoc : \n");
  // PrintPropList(target_prop_list, env);
  // printf("\n");
  
  struct PropList *tar_prop_list = Adhoc_change_tar(target_prop_list,source_prop_list, env); 

  // printf("Target Proposition after adhoc: \n");
  // PrintPropList(tar_prop_list, env);
  // printf("\n");

  struct PropList *now_prop_list = tar_prop_list;
  struct Proposition *now_prop = NULL;
  struct SmtProp * now_tar;
  int flag;
  while (now_prop_list != NULL) {
    now_prop = now_prop_list -> head;
    // printf("tar Proposition before trans : \n");
    // PrintProp(now_prop, env);
    // printf("\n");
    now_tar = PropTransSmtProp(now_prop, env);
    // printf("tar Proposition after trans : \n");
    // printSmtProp(now_tar);
    // printf("\n");
    flag = SingleSmtPropCheck(source, now_tar);
     /*if (flag == 1) {
       printf("Unclear\n");
     } else if (flag == 0) {
      printf("Solved\n");
     } else {
       printf("Wrong\n");
     }*/
    if (flag == -1) {
      res->result = -1;
      res->res_prop = PropListCons(PropDeepCopy(now_prop),PropListNil());
      PropListFree(tar_prop_list);
      freeSmtProp(source);
      freeSmtProp(now_tar);
      return res;
    }
    else {
      if (flag == 1) {
        res_prop_list = PropListCons(PropDeepCopy(now_prop),res_prop_list);
      }
      now_prop_list = now_prop_list -> next;
    }
    freeSmtProp(now_tar);
  }
  res->result = (res_prop_list == NULL);
  res->res_prop = res_prop_list;
  PropListFree(tar_prop_list);
  freeSmtProp(source);
  /*if (exec_info) {
    printf("Result is %d\n", res->result);
    if (! (res -> result)) PrintPropList(res_prop_list, env);
  }*/
  return res;
}

void Prop_solver_return_free(struct Prop_solver_return * prop_solver_return) {
  if (prop_solver_return == NULL) return;
  PropListFree(prop_solver_return->res_prop);
  free(prop_solver_return);
}