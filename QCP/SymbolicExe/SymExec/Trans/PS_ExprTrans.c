#include <assert.h>
#include <string.h>
#include "../../compiler/lang.h"
#include "../../compiler/env.h"
#include "../Utility/InnerAsrtPrinter.h"
#include "PS_ExprTrans.h"
#include "TypeTrans.h"

extern struct PolyType *cpa_type_of(struct atype *ty);

struct VirtArg * VirtArgTrans(struct virt_arg * ori, struct environment * env) {
   if (ori == NULL) {
      return NULL;
   }
   struct TypeArgList * type_args = TypeArgListNil();
   for (struct type_arg_list * i = ori->type_arg; i != NULL; i = i->next) {
      struct PolyType * type = cpa_type_of(i->type);
      char * name = malloc(sizeof(char) * (strlen(i->name) + 1));
      strcpy(name, i->name);
      type_args = TypeArgListCons(name, type, type_args);
   }
   struct VirtArgList * args = VirtArgListNil();
   for (struct virt_arg_list * i = ori->arg; i != NULL; i = i->next) {
      struct ExprVal * val = ExprValDeepCopy(i->val);
      struct PolyType * type = cpa_type_of(i->type);
      char * name = malloc(sizeof(char) * (strlen(i->name) + 1));
      strcpy(name, i->name);
      args = VirtArgListCons(name, val, type, args);
}
   return CreateVirtArg(func_spec_deep_copy(ori->ctx), type_args, args);
}

struct Cexpr * PS_ExprTrans(struct expr * origin, struct environment * env) {
   if (origin == NULL) {
      return NULL;
   }
   struct Cexpr * ret;
   struct SimpleCtype * expr_type = TransType(origin->type);
   
   switch (origin->t) {
   case T_CONST:
      ret = CexprConst(origin->d.CONST.value, expr_type);
      break;
   case T_VAR:
      ret = CexprVar(origin->d.VAR.info->id, expr_type);
      break;
   case T_BINOP:
      ret = CexprBinop(origin->d.BINOP.op,
                       PS_ExprTrans(origin->d.BINOP.left, env),
                       PS_ExprTrans(origin->d.BINOP.right, env), 
                       expr_type);
      break;
   case T_UNOP:
      ret = CexprUnop(origin->d.UNOP.op, PS_ExprTrans(origin->d.UNOP.arg, env), expr_type);
      break;
   case T_CAST:
      ret = CexprCast(PS_ExprTrans(origin->d.CAST.arg, env), expr_type);
      break;
   case T_CALL: {
      struct expr_list * i = origin->d.CALL.args;
      struct CexprList * args = CexprListNil();
      while (i != NULL) {
         args = CexprListSnoc(PS_ExprTrans(i->head, env), args);
         i = i->tail;
      }
      struct VirtArg * vargs = VirtArgTrans(origin->d.CALL.vargs, env);
      ret = CexprCall(PS_ExprTrans(origin->d.CALL.func, env), args, expr_type, vargs,
                      origin->d.CALL.vargs == NULL ? NULL : origin->d.CALL.vargs->spec_name, NULL);
      break;
   }
   case T_DEREF:
      ret = CexprDeref(PS_ExprTrans(origin->d.DEREF.arg, env), expr_type);
      break;
   case T_ADDRES:
      ret = CexprAddrof(PS_ExprTrans(origin->d.ADDRES.arg, env), expr_type);
      break;
   case T_SIZEOFTYPE:
      ret = CexprSizeof(TransType(origin->d.SIZEOFTYPE.ty), expr_type);
      break;
   case T_INDEX:
      ret = CexprIndex(PS_ExprTrans(origin->d.INDEX.arg, env), 
                       PS_ExprTrans(origin->d.INDEX.pos, env), expr_type);
      break;
   case T_FIELDOF:
      if (origin->d.FIELDOF.arg->type->t == T_STRUCT) {
         ret = CexprStructfield(PS_ExprTrans(origin->d.FIELDOF.arg, env), 
                                origin->d.FIELDOF.field->id, expr_type);
      } else if (origin->d.FIELDOF.arg->type->t == T_UNION) {
         ret = CexprUnionfield(PS_ExprTrans(origin->d.FIELDOF.arg, env), 
                               origin->d.FIELDOF.field->id, expr_type);
      } else {
         fprintf(stderr, "error at %s %d\n", __FILE__, __LINE__);
         exit(1);
      }
      break;
   case T_FIELDOFPTR: {
      assert(origin->d.FIELDOFPTR.arg->type->t == T_PTR);
      struct Cexpr * tmp = CexprDeref(PS_ExprTrans(origin->d.FIELDOFPTR.arg, env),
                                      TransType(origin->d.FIELDOFPTR.arg->type->d.PTR.ty));
      if (tmp->d.C_DEREF.expr->t == C_ADDROF) {
         struct Cexpr * t1, * t2;
         t1 = tmp; t2 = tmp->d.C_DEREF.expr;
         tmp = tmp->d.C_DEREF.expr->d.C_ADDROF.expr;
         free(t1);
         free(t2);
      }
      if (origin->d.FIELDOFPTR.arg->type->d.PTR.ty->t == T_STRUCT) {
         ret = CexprStructfield(tmp, origin->d.FIELDOFPTR.field->id, expr_type);
      } else if (origin->d.FIELDOFPTR.arg->type->d.PTR.ty->t == T_UNION) {
         ret = CexprUnionfield(tmp, origin->d.FIELDOFPTR.field->id, expr_type);
      } else {
         fprintf(stderr, "error at %s %d\n", __FILE__, __LINE__);
         exit(1);
      }
      break;
   }
   case T_ENUMLIT: {
      ret = CexprConst(origin->d.ENUMLIT.info->repr, SimpleCtypeInt32(Signed));
      break;
   }
   case T_CONDITION: {
      ret = CexprTernary(PS_ExprTrans(origin->d.CONDITION.cond, env),
                         PS_ExprTrans(origin->d.CONDITION.btrue, env),
                         PS_ExprTrans(origin->d.CONDITION.bfalse, env), expr_type);
      break;
   }
   }
   return ret;
}
