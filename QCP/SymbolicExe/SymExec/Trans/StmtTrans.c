#include <assert.h>
#include "../../compiler/env.h"
#include "../../compiler/utils.h"
#include "../../compiler/cp.h"
#include "StmtTrans.h"
#include "TypeTrans.h"

struct PartialStmtList * CSimpleCommandTrans(struct simple_cmd *cmd, struct environment * env) {
   struct CSimpleCommand * simple;
   struct PartialStmt * ps;
   switch (cmd->t) {
   case T_COMPUTATION:
      simple = CSimpleCommandCompute(PS_ExprTrans(cmd->d.COMPUTATION.arg, env));
      break;
   case T_ASGN:
      simple = CSimpleCommandAssign(cmd->d.ASGN.op, 
                                    PS_ExprTrans(cmd->d.ASGN.left, env), 
                                    PS_ExprTrans(cmd->d.ASGN.right, env));
      break;
   case T_INCDEC:
      simple = CSimpleCommandIncdec(cmd->d.INCDEC.op, PS_ExprTrans(cmd->d.INCDEC.arg, env));
      break;
   }
   ps = PartialStmtSimple(simple);
   return PartialStmtListSnoc(ps, PartialStmtListNil());
}

struct PartialStmtList * StmtTrans(struct cmd *cmd, struct environment * env, int block_killer) {
   if (cmd == NULL) return PartialStmtListNil();
   struct PartialStmtList * ret;
   struct PartialStmt * ps;
   struct PartialStmtList *l1, *l2;
   ret = NULL;
   switch (cmd->t) {
   case T_VARDECL: {
      struct PSVarDef * var = PSVarDefNew(cmd->d.VARDECL.info->id, 
                                          NULL,
                                          TransType(cmd->d.VARDECL.info->type));
      ps = PartialStmtVarDef(PSVarDefListCons(var, PSVarDefListNil()));
      ret = PartialStmtListSnoc(ps, PartialStmtListNil());
      break;
   }
   case T_SIMPLE:
      ret = CSimpleCommandTrans(cmd->d.SIMPLE.scmd, env);
      break;
   case T_SEQ:
      l1 = StmtTrans(cmd->d.SEQ.left, env, 0);
      l2 = StmtTrans(cmd->d.SEQ.right, env, 0);
      ret = PartialStmtListLink(l1, l2);
      break;
   case T_IF:
      ps = PartialStmtIfCondition(PS_ExprTrans(cmd->d.IF.cond, env));
      ret = PartialStmtListSnoc(ps, PartialStmtListNil());
      l1 = StmtTrans(cmd->d.IF.left, env, 1);
      ret = PartialStmtListLink(ret, l1);
      if (cmd->d.IF.right != NULL) {
         ret = PartialStmtListSnoc(PartialStmtElse(), ret);
         l2 = StmtTrans(cmd->d.IF.right, env, 1);
         ret = PartialStmtListLink(ret, l2);
      } else {
         ret = PartialStmtListSnoc(PartialStmtElse(), ret);
         ret = PartialStmtListSnoc(PartialStmtSimple(CSimpleCommandSkip()), ret);
      }
      ret = PartialStmtListSnoc(PartialStmtBlockEnd(), ret);
      break;
   case T_SWITCH: {
      ps = PartialStmtSwitch(PS_ExprTrans(cmd->d.SWITCH.cond, env));
      ret = PartialStmtListSnoc(ps, PartialStmtListNil());
      int cnt = 0, has_default = 0;
      struct Case_list * i = cmd->d.SWITCH.body;
      while (i != NULL) {
         struct Case * c = i->head;
         if (c->t == T_CASE) {
            if (cnt == 0) {
               ps = PartialStmtFstCase(PS_ExprTrans(c->d.CASE.cond, env));
            } else {
               ps = PartialStmtOtherCase(PS_ExprTrans(c->d.CASE.cond, env));
            }
            ret = PartialStmtListSnoc(ps, ret);
            l1 = StmtTrans(c->d.CASE.body, env, 0);
            if (l1->head == NULL) {
               l1 = PartialStmtListSnoc(PartialStmtSimple(CSimpleCommandSkip()), l1);
            }
            ret = PartialStmtListLink(ret, l1);
         } else if (c->t == T_DEFAULT) {
            ret = PartialStmtListSnoc(PartialStmtDefault(), ret);
            l1 = StmtTrans(c->d.DEFAULT.body, env, 0);
            if (l1->head == NULL) {
               l1 = PartialStmtListSnoc(PartialStmtSimple(CSimpleCommandSkip()), l1);
            }
            has_default = 1;
            ret = PartialStmtListLink(ret, l1);
         } else {
            fprintf(stderr, "ERROR at %s %d", __FILE__, __LINE__);
         }
         i = i->tail;
         ++cnt;
      }
      if (!has_default) {
         ret = PartialStmtListSnoc(PartialStmtDefault(), ret);
         ret = PartialStmtListSnoc(PartialStmtSimple(CSimpleCommandSkip()), ret);
      }
      if (cmd->d.SWITCH.body != NULL) {
         ret = PartialStmtListSnoc(PartialStmtBlockEnd(), ret);
      }
      ret = PartialStmtListSnoc(PartialStmtBlockEnd(), ret);
      break;
   }
   case T_WHILE:
      if (cmd->d.WHILE.inv != NULL) {
         ps = PartialStmtInv(cmd->d.WHILE.inv, 0, NULL);
         ret = PartialStmtListSnoc(ps, PartialStmtListNil());
      } else {
         ret = PartialStmtListNil();
      }
      ps = PartialStmtWhileCondition(PS_ExprTrans(cmd->d.WHILE.cond, env), NULL);
      ret = PartialStmtListSnoc(ps, ret);
      l1 = StmtTrans(cmd->d.WHILE.body, env, 1);
      ret = PartialStmtListLink(ret, l1);
      ret = PartialStmtListSnoc(PartialStmtBlockEnd(), ret);
      break;
   case T_DOWHILE:
      ret = PartialStmtListSnoc(PartialStmtDo(), ret);
      l1 = StmtTrans(cmd->d.DOWHILE.body, env, 1);
      ret = PartialStmtListLink(ret, l1);
      ps = PartialStmtDoWhileCondition(PS_ExprTrans(cmd->d.DOWHILE.cond,env),
                                       cmd->d.DOWHILE.inv,
                                       cmd->d.DOWHILE.is_partial, NULL);
      ret = PartialStmtListSnoc(ps, ret);
      break;
   case T_FOR:
      if (cmd->d.FOR.inv != NULL) {
         ps = PartialStmtInv(cmd->d.FOR.inv, 0, NULL);
         ret = PartialStmtListSnoc(ps, PartialStmtListNil());
      }
      l1 = CSimpleCommandTrans(cmd->d.FOR.init, env);
      assert(l1->head->next == NULL && l1->head->data->t == PS_simple); // only support one single simple cmd      
      l2 = CSimpleCommandTrans(cmd->d.FOR.incr, env);
      assert(l2->head->next == NULL && l2->head->data->t == PS_simple); // only support one single simple cmd
      ps = PartialStmtFor(l1->head->data->d.PS_simple.comd,
                          PS_ExprTrans(cmd->d.FOR.cond, env),
                          l2->head->data->d.PS_simple.comd,
                          cmd->d.FOR.inv,
                          cmd->d.FOR.is_partial,
                          NULL);
      ret = PartialStmtListSnoc(ps, ret);
      free(l1->head);
      free(l1);
      free(l2->head);
      free(l2);
      l1 = StmtTrans(cmd->d.FOR.body, env, 1);
      ret = PartialStmtListLink(ret, l1);
      ret = PartialStmtListSnoc(PartialStmtBlockEnd(), ret);
      break;
   case T_BREAK:
      ret = PartialStmtListSnoc(PartialStmtBreak(), PartialStmtListNil());
      break;
   case T_CONTINUE:
      ret = PartialStmtListSnoc(PartialStmtContinue(), PartialStmtListNil());
      break;
   case T_RETURN:
      ret = PartialStmtListSnoc(PartialStmtReturn(PS_ExprTrans(cmd->d.RETURN.arg, env), NULL), PartialStmtListNil());
      break;
   case T_COMMENT:
      ret = PartialStmtListSnoc(PartialStmtAssert(cmd->d.COMMENT.asrt, cmd->d.COMMENT.is_partial, NULL), PartialStmtListNil());
      break;
   case T_SKIP:
      ret = PartialStmtListSnoc(PartialStmtSimple(CSimpleCommandSkip()), PartialStmtListNil());
      break;
   case T_BLOCK:
      ret = PartialStmtListNil();
      // if (!block_killer) {
         ret = PartialStmtListSnoc(PartialStmtBlockBegin(), ret);
      // }
      l1 = StmtTrans(cmd->d.BLOCK.cmd, env, 0);
      ret = PartialStmtListLink(ret, l1);
      // if (!block_killer) {
         ret = PartialStmtListSnoc(PartialStmtBlockEnd(), ret);
      // }
      break;
   }
   struct PartialStmtListNode * it;
   for (it = ret->head; it != NULL; it = it->next) {
      if (it->next == NULL) {
         it->data->next = NULL;
      } else {
         it->data->next = it->next->data;
      }
   }
   return ret;
}

struct Cexpr *PS_PPExprTrans(struct pp_expr * e, struct environment *env) {
   struct SimpleCtype *type = TransType(e->type);
   switch (e->t) {
   case PP_CONST:
      return CexprConst(e->d.CONST.value, type);
   case PP_STRING:
      fprintf(stderr, "error: String literal is not supported yet");
      exit(1);
   case PP_VAR: 
      return CexprVar(e->d.VAR.info->id, type);
   case PP_BINOP:
      return CexprBinop(e->d.BINOP.op,
                        PS_PPExprTrans(e->d.BINOP.left, env),
                        PS_PPExprTrans(e->d.BINOP.right, env),
                        type);
   case PP_UNOP:
      return CexprUnop(e->d.UNOP.op, PS_PPExprTrans(e->d.UNOP.arg, env), type);
   case PP_CAST:
      return CexprCast(PS_PPExprTrans(e->d.CAST.arg, env), type);
   case PP_CALL: {
     struct pp_expr_list *i;
     struct CexprList *args = CexprListNil();
     for (i = e->d.CALL.args; i != NULL; i = i->tail)
       args = CexprListSnoc(PS_PPExprTrans(i->head, env), args);
     struct VirtArg *vargs = NULL;
     if (e->d.CALL.vargs != NULL)
       vargs = VirtArgTrans(e->d.CALL.vargs->after, env);
     return CexprCall(PS_PPExprTrans(e->d.CALL.func, env), args, type, vargs,
                      e->d.CALL.vargs != NULL ? e->d.CALL.vargs->after->spec_name : NULL, e->d.CALL.vargs == NULL ? NULL : e->d.CALL.vargs->scopes);
   }
   case PP_DEREF:
      return CexprDeref(PS_PPExprTrans(e->d.DEREF.arg, env), type);
   case PP_ADDRESS:
      return CexprAddrof(PS_PPExprTrans(e->d.ADDRESS.arg, env), type);
   case PP_SIZEOFTYPE:
      return CexprSizeof(TransType(type_of_pp_type(e->d.SIZEOFTYPE.ty->type)), type);
   case PP_INDEX:
      return CexprIndex(PS_PPExprTrans(e->d.INDEX.arg, env),
                        PS_PPExprTrans(e->d.INDEX.pos, env),
                        type);
   case PP_FIELDOF:
      if (e->d.FIELDOF.field->parent->t == IS_STRUCT) {
         return CexprStructfield(PS_PPExprTrans(e->d.FIELDOF.arg, env),
                                 e->d.FIELDOF.field->id, type);
      } else {
         return CexprUnionfield(PS_PPExprTrans(e->d.FIELDOF.arg, env),
                                 e->d.FIELDOF.field->id, type);
      }
   case PP_FIELDOFPTR:
      if (e->d.FIELDOFPTR.arg->t == PP_ADDRESS) {
         if (e->d.FIELDOFPTR.field->parent->t == IS_STRUCT) {
            return CexprStructfield(PS_PPExprTrans(e->d.FIELDOFPTR.arg->d.ADDRESS.arg, env),
                                    e->d.FIELDOF.field->id, type);
         } else {
            return CexprUnionfield(PS_PPExprTrans(e->d.FIELDOFPTR.arg->d.ADDRESS.arg, env),
                                   e->d.FIELDOF.field->id, type);
         }
      } else {
         if (e->d.FIELDOFPTR.field->parent->t == IS_STRUCT) {
            return CexprStructfield(CexprDeref(PS_PPExprTrans(e->d.FIELDOF.arg, env),
                                               TransType(TStruct(e->d.FIELDOFPTR.field->parent))),
                                    e->d.FIELDOF.field->id, type);
         } else {
            return CexprUnionfield(CexprDeref(PS_PPExprTrans(e->d.FIELDOF.arg, env),
                                              TransType(TUnion(e->d.FIELDOFPTR.field->parent))),
                                   e->d.FIELDOF.field->id, type);
         }
      }
   case PP_ENUMLIT:
      return CexprConst(e->d.ENUMLIT.info->repr, SimpleCtypeInt32(Signed));
   case PP_CONDITION:
      return CexprTernary(PS_PPExprTrans(e->d.CONDITION.cond, env),
                          PS_PPExprTrans(e->d.CONDITION.btrue, env),
                          PS_PPExprTrans(e->d.CONDITION.bfalse, env),
                          type);
   }
}

struct CSimpleCommand * PPSimpleCommandTrans(struct pp_simple *c, struct environment * env) {
   if (c == NULL) return CSimpleCommandSkip();
   switch (c->t) {
   case PP_COMPUTATION:
      return CSimpleCommandCompute(PS_PPExprTrans(c->d.COMPUTATION.arg, env));
      break;
   case PP_ASGN:
      return CSimpleCommandAssign(c->d.ASGN.op,
                                    PS_PPExprTrans(c->d.ASGN.left, env),
                                    PS_PPExprTrans(c->d.ASGN.right, env));
      break;
   case PP_INCDEC:
      return CSimpleCommandIncdec(c->d.INCDEC.op, PS_PPExprTrans(c->d.INCDEC.arg, env));
      break;
   }
}

struct PartialStmt * SingleStmtTrans(struct partial_program *c, struct environment * env) {
   switch (c->t) {
   case PP_SIMPLE:
      return PartialStmtSimple(PPSimpleCommandTrans(c->d.SIMPLE.simple, env));
   case PP_BREAK:
      return PartialStmtBreak();
   case PP_CONTINUE:
      return PartialStmtContinue();
   case PP_RETURN:
     if (c->d.RETURN.ret == NULL)
       return PartialStmtReturn(NULL, NULL);
     else
       return PartialStmtReturn(PS_PPExprTrans(c->d.RETURN.ret, env), NULL);
   case PP_WHILE:
      return PartialStmtWhileCondition(PS_PPExprTrans(c->d.WHILE.cond, env), NULL);
   case PP_IF:
      return PartialStmtIfCondition(PS_PPExprTrans(c->d.IF.cond, env));
   case PP_ELSE:
      return PartialStmtElse();
   case PP_DO:
      return PartialStmtDo();
   case PP_SWITCH:
      return PartialStmtSwitch(PS_PPExprTrans(c->d.SWITCH.cond, env));
   case PP_DEFAULT:
      return PartialStmtDefault();
   case PP_BLOCK:
      return PartialStmtBlockBegin();
   case PP_SKIP:
     return PartialStmtSimple(CSimpleCommandSkip());
   case PP_DO_STRATEGY:
     return PartialStmtDoStrategy(clone_str(c->d.DO_STRATEGY.name));
   case PP_FOR:
   case PP_FIRST_DECL:
   case PP_MORE_DECL:
   case PP_ASSERT:
   case PP_INV:
   case PP_WI:
   case PP_PROOF:
   case PP_STRUCT_DEF:
   case PP_UNION_DEF:
   case PP_ENUM_DEF:
   case PP_STRUCT_DEC:
   case PP_UNION_DEC:
   case PP_ENUM_DEC:
   case PP_SEPDEF:
   case PP_FUNC_DEF:
   case PP_FUNC_DEC:
   case PP_COQ_DEC:
   case PP_ATYPE_DEC:
   case PP_CASE:
   case PP_END:
   case PP_PROJ_DEC:
   case PP_COQ_TYPE_ALIAS:
     assert(0);
   }
}
