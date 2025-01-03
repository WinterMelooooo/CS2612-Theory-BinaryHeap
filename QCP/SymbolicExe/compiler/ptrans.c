#include "env.h"
#include "utils.h"
#include "pparser.h"
#include "../SymExec/Trans/StmtTrans.h"
#include "../SymExec/Trans/TypeTrans.h"
#include "../SymExec/Automation/dsl_match/ASTtoLibRule.h"
#include "../SymExec/Automation/AutomationSolver/CustomSolver.h"

#define APPEND_ONE_COMMAND(tail, cmd) \
  { \
    if (*(tail) == NULL) \
      *(tail) = cmd; \
    else \
      *(tail) = TSeq(*(tail), cmd); \
  }

/* feed a cmd and update accordingly */
void finalize(struct cmd *c, struct environment *env,
              struct AsrtList * (*k_partial_statement)(struct PartialStmt *p, struct environment *env)) {
  struct context *ctx = &env->context;
  struct context_stack *s = ctx->c;
  struct ephemeral_env *eph = &env->ephemer;
  struct cmd *t;

  switch (s->t) {
  case CTX_FUNC: APPEND_ONE_COMMAND(s->d.FUNC.tail, c);
                 break;
  case CTX_BLOCK: APPEND_ONE_COMMAND(s->d.BLOCK.tail, c);
                  break;
  case CTX_CASE: APPEND_ONE_COMMAND(s->d.CASE.tail, c);
                 break;
  case CTX_HOLE: t = s->d.HOLE.c;
                 *s->d.HOLE.hole = c;
                 context_up(ctx);
                 flow_env_up(eph);
                 k_partial_statement(PartialStmtBlockEnd(), env);
                 finalize(t, env, k_partial_statement);
                 break;
  case CTX_THEN: t = s->d.THEN.c;
                 t->d.IF.left = c;
                 context_up(ctx);
                 context_deep_after_then(t, ctx);
                 flow_env_up(eph);
                 break;
  case CTX_AFTER_THEN: t = s->d.AFTER_THEN.c;
                       t->d.IF.right = NULL;
                       context_up(ctx);
                       k_partial_statement(PartialStmtElse(), env);
                       k_partial_statement(PartialStmtSimple(CSimpleCommandSkip()), env);
                       k_partial_statement(PartialStmtBlockEnd(), env);
                       finalize(t, env, k_partial_statement);
                       finalize(c, env, k_partial_statement);
                       break;
  case CTX_DOWHILE: t = s->d.DOWHILE.c;
                    t->d.DOWHILE.body = c;
                    context_up(ctx);
                    context_deep_before_while(t, ctx);
                    flow_env_up(eph);
                    break;
  case CTX_DECL: { struct pp_type *t = s->d.DECL.base;
                   int is_typedef = s->d.DECL.is_typedef;
                   context_up(ctx);
                   finalize(c, env, k_partial_statement);
                   context_deep_decl(t, is_typedef, ctx);
                   break; }
  case CTX_BEFORE_WHILE: failwith("Expected `while' in do/while loop");
  case CTX_AFTER_WHILE:  failwith("Expected `;' after do/while statement");
  case CTX_TOP:          failwith("Statement at toplevel");
  case CTX_SWITCH:       failwith("Statement will never be executed before the first `case'");
  case CTX_INV:          failwith("Expected loop after loop invariant");
  }
}

void maybe_get_inv(struct context *ctx,
                   struct AsrtList **inv, int *partial, struct StringList **scopes) {
  *partial = 0;
  *inv = NULL;
  if (ctx->c->t == CTX_INV) {
    *inv = ctx->c->d.INV.inv;
    *partial = ctx->c->d.INV.partial;
    *scopes = ctx->c->d.INV.scopes;
    context_up(ctx);

    /* if (*inv == NULL) */
      /* failwith("Did not fill in the invariant"); */
  }
}

void finalize_case(struct environment *env,
                   struct AsrtList * (*k_partial_statement)(struct PartialStmt *p, struct environment *env)) {
  struct context *ctx = &env->context;
  struct ephemeral_env *eph = &env->ephemer;
  struct Case *c = ctx->c->d.CASE.c;
  struct Case_list *cl = CLCons(c, NULL);

  context_up(ctx);
  *ctx->c->d.SWITCH.tail = cl;
  ctx->c->d.SWITCH.tail = &cl->tail;
  if (c->t == T_CASE && c->d.CASE.body == NULL ||
      c->t == T_DEFAULT && c->d.DEFAULT.body == NULL)
    k_partial_statement(PartialStmtSimple(CSimpleCommandSkip()), env);
  flow_env_up(eph);
}

struct AsrtList *false_assertion() {
  struct Assertion *f = CreateAsrt();
  f->exist_list = ExistListNil();
  f->fp_spec_list = FPSpecListNil();
  f->local_list = CreateLocalLinkedHashMap();
  f->prop_list = PropListCons(PropFalse(), PropListNil());
  f->sep_list = SepListNil();
  return AsrtListCons(f, AsrtListNil());
}

int DslInit = 0;
/* handle context and deep/up; environment is maintained by parse_... */
void trans(struct partial_program *s, struct environment *env,
           void (*k_func_begin)(struct func_info *info, struct environment *env),
           struct AsrtList * (*k_partial_statement)(struct PartialStmt *p, struct environment *env),
           void (*k_func_end)(struct func_info *info, struct environment *env)) {
  struct context *ctx = &env->context;
  struct ephemeral_env *eph = &env->ephemer;
  struct cmd *c;

#define ENSURE_NOT_TOP() { if (ctx->c->t == CTX_TOP) failwith("Invalid syntax at toplevel"); }
#define ENSURE_NOT_DECL() { if (ctx->c->t == CTX_DECL) failwith("Invalid syntax after declaration"); }

  if (s->t != PP_MORE_DECL)
    ENSURE_NOT_DECL();

  if (ctx->c->t == CTX_AFTER_THEN && s->t != PP_ELSE) {
    struct cmd *t = ctx->c->d.AFTER_THEN.c;
    t->d.IF.right = NULL;
    context_up(ctx);
    k_partial_statement(PartialStmtElse(), env);
    k_partial_statement(PartialStmtSimple(CSimpleCommandSkip()), env);
    k_partial_statement(PartialStmtBlockEnd(), env);
    finalize(t, env, k_partial_statement);
  }

  switch (s->t) {
  case PP_FIRST_DECL: { if (ctx->c->t != CTX_TOP &&
                            ctx->c->t != CTX_FUNC &&
                            ctx->c->t != CTX_BLOCK &&
                            ctx->c->t != CTX_DECL &&
                            ctx->c->t != CTX_AFTER_THEN)
                          failwith("Variable declaration is not allowed here");
                        struct pp_type *base = parse_decl_head(s->d.FIRST_DECL.pre->triv, env);
                        if (!s->d.FIRST_DECL.is_end)
                          context_deep_decl(base, s->d.FIRST_DECL.is_typedef, ctx);
                        if (s->d.FIRST_DECL.is_typedef) {
                          struct type_info *info = parse_type_def(base, s->d.FIRST_DECL.pre->deriv, env);
                          if (ctx->c->t != CTX_TOP &&
                              !(ctx->c->t == CTX_DECL && ctx->c->outer->t == CTX_TOP))
                            finalize(TTypedef(info), env, k_partial_statement);
                        } else {
                          struct prog_var_info *info = parse_decl(base, s->d.FIRST_DECL.pre->deriv, env);
                          if (ctx->c->t != CTX_TOP &&
                              !(ctx->c->t == CTX_DECL && ctx->c->outer->t == CTX_TOP)) {
                            finalize(TVarDecl(info), env, k_partial_statement);
                            k_partial_statement(PartialStmtVarDef
                                                (PSVarDefListCons
                                                 (PSVarDefNew
                                                  (info->id, NULL, TransType(info->type)),
                                                  PSVarDefListNil())), env);
                          }
                          if (s->d.FIRST_DECL.init != NULL) {
                            if (ctx->c->t == CTX_TOP) {
                              fprintf(stderr, "warning: Global variable initialization is omitted.\n");
                            } else if (s->d.FIRST_DECL.init->t == PP_SINGLE_EXPR) {
                              struct partial_program *asgn =
                                PPSimple(PPAsgn(T_ASSIGN, PPVar(info->name),
                                                s->d.FIRST_DECL.init->d.SINGLE_EXPR.expr));
                              finalize(TSimple(parse_simple_cmd(asgn->d.SIMPLE.simple, env)), env, k_partial_statement);
                              k_partial_statement(SingleStmtTrans(asgn, env), env);
                            } else
                              failwith("Complex initialization is not supported yet");
                          }
                        }
                        if (s->d.FIRST_DECL.is_end)
                          free_pp_type(base);
                        break; }
  case PP_MORE_DECL: { if (ctx->c->d.DECL.is_typedef) {
                         struct type_info *info = parse_type_def(ctx->c->d.DECL.base, s->d.MORE_DECL.deriv, env);
                         if (ctx->c->outer->t != CTX_TOP)
                           finalize(TTypedef(info), env, k_partial_statement);
                       } else {
                         struct prog_var_info *info = parse_decl(ctx->c->d.DECL.base, s->d.MORE_DECL.deriv, env);
                         if (!(ctx->c->outer->t == CTX_TOP)) {
                           finalize(TVarDecl(info), env, k_partial_statement);
                           k_partial_statement(PartialStmtVarDef
                                               (PSVarDefListCons
                                                (PSVarDefNew
                                                 (info->id, NULL, TransType(info->type)),
                                                 PSVarDefListNil())), env);
                         }
                         if (s->d.MORE_DECL.init != NULL) {
                           if (ctx->c->outer->t == CTX_TOP) {
                             fprintf(stderr, "warning: Global variable initialization is omitted.\n");
                           } else if (s->d.MORE_DECL.init->t == PP_SINGLE_EXPR) {
                             struct partial_program *asgn =
                               PPSimple(PPAsgn(T_ASSIGN, PPVar(info->name),
                                               s->d.MORE_DECL.init->d.SINGLE_EXPR.expr));
                             finalize(TSimple(parse_simple_cmd(asgn->d.SIMPLE.simple, env)), env, k_partial_statement);
                             k_partial_statement(SingleStmtTrans(asgn, env), env);
                           } else
                           failwith("Complex initialization is not supported yet");
                         }
                       }
                       if (s->d.MORE_DECL.is_end) {
                         free_pp_type(ctx->c->d.DECL.base);
                         context_up(ctx);
                       }
                       break;
                     }
  case PP_SIMPLE: { struct cmd *c = TSimple(parse_simple_cmd(s->d.SIMPLE.simple, env));
                    k_partial_statement(SingleStmtTrans(s, env), env);
                    finalize(c, env, k_partial_statement);
                    break; }
  case PP_BREAK: { struct context_stack *stk;
                   for (stk = ctx->c; stk != NULL; stk = stk->outer)
                     if (stk->t == CTX_CASE ||
                         stk->t == CTX_DOWHILE ||
                         stk->t == CTX_HOLE && stk->d.HOLE.c->t != T_IF) {
                       finalize(TBreak(), env, k_partial_statement);
                       break;
                     }
                   if (stk == NULL)
                     failwith("`break' statement not in loop or switch statement");
                   k_partial_statement(SingleStmtTrans(s, env), env);
                   break; }
  case PP_CONTINUE: { struct context_stack *stk;
                      for (stk = ctx->c; stk != NULL; stk = stk->outer)
                        if (stk->t == CTX_DOWHILE ||
                            stk->t == CTX_HOLE && stk->d.HOLE.c->t != T_IF) {
                          finalize(TContinue(), env, k_partial_statement);
                          break;
                        }
                      if (stk == NULL)
                        failwith("`continue' statement not in loop statement");
                      k_partial_statement(SingleStmtTrans(s, env), env);
                      break; }
  case PP_RETURN: { struct cmd *c;
                    if (s->d.RETURN.ret != NULL)
                      c = TReturn(parse_ret(s->d.RETURN.ret, env));
                    else
                      c = TReturn(NULL);
                    k_partial_statement(SingleStmtTrans(s, env), env);
                    finalize(c, env, k_partial_statement);
                    break; }
  case PP_WHILE: { struct AsrtList *inv;
                   int partial;
                   struct StringList *scopes;
                   maybe_get_inv(ctx, &inv, &partial, &scopes);
                   if (ctx->c->t == CTX_BEFORE_WHILE) {
                     c = ctx->c->d.BEFORE_WHILE.c;
                     c->d.DOWHILE.inv = inv;
                     c->d.DOWHILE.is_partial = partial;
                     c->d.DOWHILE.cond = parse_cond(s->d.WHILE.cond, env);
                     context_up(ctx);
                     context_deep_after_while(c, ctx);
                     k_partial_statement
                       (PartialStmtDoWhileCondition
                        (PS_PPExprTrans(s->d.WHILE.cond, env), inv, partial, scopes), env);
                     break;
                   } else {
                     ENSURE_NOT_TOP();
                     c = TWhile(inv, partial, parse_cond(s->d.WHILE.cond, env), NULL);
                     context_deep_hole(c, &c->d.WHILE.body, ctx);
                     flow_env_deep(eph);
                     if (inv != NULL)
                       k_partial_statement(PartialStmtInv(inv, partial, scopes), env);
                     k_partial_statement(SingleStmtTrans(s, env), env);
                     break;
                   }}
  case PP_IF: ENSURE_NOT_TOP();
              c = TIf(parse_cond(s->d.IF.cond, env), NULL, NULL);
              context_deep_then(c, ctx);
              flow_env_deep(eph);
              k_partial_statement(SingleStmtTrans(s, env), env);
              break;
  case PP_ELSE: if (ctx->c->t == CTX_AFTER_THEN) {
                  c = ctx->c->d.AFTER_THEN.c;
                  context_up(ctx);
                  context_deep_hole(c, &c->d.IF.right, ctx);
                  flow_env_deep(eph);
                  k_partial_statement(SingleStmtTrans(s, env), env);
                  break;
                } else
                  failwith("`else' is not following an `if'");
  case PP_DO: { ENSURE_NOT_TOP();
                c = TDoWhile(NULL, 0, NULL, NULL);
                context_deep_dowhile(c, ctx);
                flow_env_deep(eph);
                k_partial_statement(SingleStmtTrans(s, env), env);
                break; }
  case PP_FOR: { ENSURE_NOT_TOP();
                 struct AsrtList *inv;
                 int partial;
                 struct StringList * scopes;
                 maybe_get_inv(ctx, &inv, &partial, &scopes);
                 c = TFor(inv, partial,
                          parse_simple_cmd(s->d.FOR.init, env),
                          s->d.FOR.cond == NULL ? NULL : parse_cond(s->d.FOR.cond, env),
                          parse_simple_cmd(s->d.FOR.step, env), NULL);
                 context_deep_hole(c, &c->d.FOR.body, ctx);
                 flow_env_deep(eph);
                 k_partial_statement
                   (PartialStmtFor
                      (PPSimpleCommandTrans(s->d.FOR.init, env),
                       s->d.FOR.cond == NULL ? CexprConst(1, SimpleCtypeInt32(Signed)) : PS_PPExprTrans(s->d.FOR.cond, env),
                       PPSimpleCommandTrans(s->d.FOR.step, env),
                       inv, partial, scopes), env);
                 break; }
  case PP_SWITCH: ENSURE_NOT_TOP();
                  c = TSwitch(parse_switch_cond(s->d.SWITCH.cond, env), NULL);
                  context_deep_switch(c, ctx);
                  k_partial_statement(SingleStmtTrans(s, env), env);
                  break;
  case PP_CASE: { int first = 1;
                  if (ctx->c->t == CTX_CASE) {
                    first = 0;
                    finalize_case(env, k_partial_statement);
                  }
                  if (ctx->c->t == CTX_SWITCH) {
                    struct Case *c;
                    c = TCase(parse_case_cond(s->d.CASE.cond, env), NULL);
                    context_deep_case(c, ctx);
                    flow_env_deep(eph);
                    if (first)
                      k_partial_statement(PartialStmtFstCase(PS_PPExprTrans(s->d.CASE.cond,
                                                                            env)), env);
                    else
                      k_partial_statement(PartialStmtOtherCase(PS_PPExprTrans(s->d.CASE.cond,
                                                                              env)), env);
                    break;
                  } else
                    failwith("`case' statement not in `switch' statement"); }
  case PP_DEFAULT: if (ctx->c->t == CTX_CASE)
                     finalize_case(env, k_partial_statement);
                   if (ctx->c->t == CTX_SWITCH) {
                     context_deep_case(TDefault(NULL), ctx);
                     flow_env_deep(eph);
                     k_partial_statement(SingleStmtTrans(s, env), env);
                     break;
                   } else
                     failwith("`default' statement not in `switch' statement");
  case PP_BLOCK: ENSURE_NOT_TOP();
                 scope_env_deep(eph);
                 context_deep_block(TBlock(NULL), ctx);
                 k_partial_statement(SingleStmtTrans(s, env), env);
                 break;
  case PP_END: switch (ctx->c->t) {
                 case CTX_TOP: failwith("Extraneous closing brace");
                 case CTX_FUNC: { struct func_info *info = ctx->c->d.FUNC.info;
                   /* finalize_func_def(ctx->c->d.FUNC.info, env); */
                                k_func_end(info, env);
                                scope_env_up(eph);
                                context_up(ctx);
                                flow_env_up(eph);
                                break; }
                 case CTX_THEN: failwith("Nothing after `if'");
                 case CTX_AFTER_THEN: c = ctx->c->d.AFTER_THEN.c;
                                      context_up(ctx);
                                      k_partial_statement(PartialStmtElse(), env);
                                      k_partial_statement(PartialStmtSimple(CSimpleCommandSkip()), env);
                                      k_partial_statement(PartialStmtBlockEnd(), env);
                                      finalize(c, env, k_partial_statement);
                                      trans(s, env, k_func_begin, k_partial_statement, k_func_end);
                                      break;
                 case CTX_HOLE: failwith("Expected statement");
                 case CTX_DOWHILE: failwith("Nothing following `do'");
                 case CTX_BEFORE_WHILE: failwith("Expected `while' in do/while statement");
                 case CTX_AFTER_WHILE: failwith("Expected `;' after do/while statement");
                 case CTX_SWITCH: /* empty switch */
                                  c = ctx->c->d.SWITCH.c;
                                  context_up(ctx);
                                  k_partial_statement(PartialStmtBlockEnd(), env);
                                  finalize(c, env, k_partial_statement);
                                  break;
                 case CTX_CASE: c = *ctx->c->d.CASE.tail;
                                if (c == NULL)
                                  failwith("Label at end of compound statement; "
                                           "expected statement");
                                int no_default = 0;
                                if (ctx->c->d.CASE.c->t != T_DEFAULT)
                                  no_default = 1;
                                finalize_case(env, k_partial_statement);
                                c = ctx->c->d.SWITCH.c;
                                context_up(ctx);
                                if (no_default) {
                                  k_partial_statement(PartialStmtDefault(), env);
                                  k_partial_statement(PartialStmtAssert(false_assertion(), 0, NULL), env);
                                  k_partial_statement(PartialStmtSimple(CSimpleCommandSkip()), env);
                                }
                                k_partial_statement(PartialStmtBlockEnd(), env);
                                k_partial_statement(PartialStmtBlockEnd(), env);
                                finalize(c, env, k_partial_statement);
                                break;
                 case CTX_BLOCK: scope_env_up(eph);
                                 c = ctx->c->d.BLOCK.c;
                                 context_up(ctx);
                                 finalize(c, env, k_partial_statement);
                                 k_partial_statement(PartialStmtBlockEnd(), env);
                                 break;
                 case CTX_INV: failwith("Expected loop after loop invariant");
                 case CTX_DECL: failwith("Missing semicolon after declaration");
               }
               break;
  case PP_ASSERT: { struct AsrtList *a = parse_comment(s->d.ASSERT.assert, s->d.ASSERT.mark, env);
                    struct AsrtList *b = k_partial_statement(PartialStmtAssert(a, s->d.ASSERT.partial, s->d.ASSERT.scopes), env);
                    finalize(TComment(a, s->d.ASSERT.partial, s->d.ASSERT.mark), env, k_partial_statement);
                    if (s->d.ASSERT.mark != NULL)
                      add_assertion(s->d.ASSERT.mark, b, &(env->ephemer));
                    break; }
  case PP_INV: { ENSURE_NOT_TOP();
                 struct AsrtList *a = parse_comment(s->d.INV.assert, NULL, env);
                 context_deep_inv(a, s->d.INV.partial, s->d.INV.scopes, ctx);
                 break; }
  case PP_WI: { struct func_spec *fp = parse_local_spec(s->d.WI.pre, s->d.WI.post, env);
                struct cmd *c = TPartialComment(fp);
                k_partial_statement(PartialStmtWi(c->d.PARTIAL_COMMENT.specs, s->d.WI.pre_scopes, s->d.WI.post_scopes), env);
                finalize(c, env, k_partial_statement);
                break; }
  case PP_PROOF: finalize(TProof(s->d.PROOF.name), env, k_partial_statement);
                 break;
  case PP_MISSING_INV: ENSURE_NOT_TOP();
                       context_deep_inv(NULL, 0, NULL, ctx);
                       break;
  case PP_DO_STRATEGY: k_partial_statement(SingleStmtTrans(s, env), env);
                       finalize(TDoStrategy(s->d.DO_STRATEGY.name), env, k_partial_statement);
                       break;
  case PP_SKIP: if (ctx->c->t == CTX_AFTER_WHILE) {
                  c = ctx->c->d.AFTER_WHILE.c;
                  context_up(ctx);
                  finalize(c, env, k_partial_statement);
                  break;
                } else {
                  k_partial_statement(SingleStmtTrans(s, env), env);
                  finalize(TSkip(), env, k_partial_statement);
                  break;
                }

  case PP_STRUCT_DEF: { struct struct_union_info *info =
                          parse_struct_def(s->d.STRUCT_DEF.name, s->d.STRUCT_DEF.field, env);
                        if (ctx->c->t != CTX_TOP)
                          finalize(TStructDef(info), env, k_partial_statement);
                        break; }
  case PP_UNION_DEF: { struct struct_union_info *info =
                         parse_union_def(s->d.UNION_DEF.name, s->d.UNION_DEF.field, env);
                       if (ctx->c->t != CTX_TOP)
                         finalize(TUnionDef(info), env, k_partial_statement);
                       break; }
  case PP_ENUM_DEF: { struct enum_info *info =
                        parse_enum_def(s->d.ENUM_DEF.name, s->d.ENUM_DEF.rator, env);
                      if (ctx->c->t != CTX_TOP)
                        finalize(TEnumDef(info), env, k_partial_statement);
                      break; }
  case PP_SEPDEF: if (ctx->c->t != CTX_TOP)
                    failwith("Separation predicate definition is not allowed here");
                  parse_sepdef(s->d.SEPDEF.name,
                               s->d.SEPDEF.witht, s->d.SEPDEF.with,
                               s->d.SEPDEF.condition, env);
                  break;
  case PP_COQ_DEC: {if (ctx->c->t != CTX_TOP)
                      failwith("Importing Coq definition is not allowed here");
                    struct term_list *i;
                    for (i = s->d.COQ_DEC.name; i != NULL; i = i->next)
                      parse_extern_def(i->name, i->qv, i->body, env);
                    break; }
  case PP_COQ_TYPE_ALIAS: if (ctx->c->t != CTX_TOP)
                             failwith("Coq type alias definition is not allowed here");
                           parse_atype_alias(s->d.COQ_TYPE_ALIAS.name,
                                             s->d.COQ_TYPE_ALIAS.type,
                                             env);
                           break;
  case PP_ATYPE_DEC: {if (ctx->c->t != CTX_TOP)
                        failwith("Importing Coq definition is not allowed here");
                      struct atype_list *i;
                      for (i = s->d.ATYPE_DEC.name; i != NULL; i = i->next)
                        parse_atype_def(i->name, i->kind, env);
                      break; }
  case PP_PROJ_DEC: { if (ctx->c->t != CTX_TOP)
                        failwith("Importing Coq projection is not allowed here");
                      struct term_list *i;
                      for (i = s->d.PROJ_DEC.projs; i != NULL; i = i->next)
                        parse_proj_def(i->name, i->qv, i->body, env);
                      break; }
  case PP_RECORD_DEC: { if (ctx->c->t != CTX_TOP)
                          failwith("Importing Coq record is not allowed here");
                        parse_record_def(s->d.RECORD_DEC.params,
                                         s->d.RECORD_DEC.record_name,
                                         s->d.RECORD_DEC.constr_name,
                                         s->d.RECORD_DEC.fields,
                                         env);
                        break; }
  case PP_STRUCT_DEC: { struct struct_union_info *info =
                          parse_struct_dec(s->d.STRUCT_DEC.name, env);
                        if (ctx->c->t != CTX_TOP)
                          finalize(TStructDec(info), env, k_partial_statement);
                        break; }
  case PP_UNION_DEC: { struct struct_union_info *info =
                         parse_union_dec(s->d.UNION_DEC.name, env);
                       if (ctx->c->t != CTX_TOP)
                         finalize(TUnionDec(info), env, k_partial_statement);
                       break; }
  case PP_ENUM_DEC: { struct enum_info *info =
                        parse_enum_dec(s->d.ENUM_DEC.name, env);
                      if (ctx->c->t != CTX_TOP)
                        finalize(TEnumDec(info), env, k_partial_statement);
                      break; }
  case PP_FUNC_DEF: { if (ctx->c->t != CTX_TOP)
                        failwith("Function definition is not allowed here");
                      flow_env_deep(eph);
                      if (!DslInit) {
                          initIncludePaths();
                          setIncludePath();
                          initStrategyLibInScopes(env);
                          DslInit = 1;
                      }
                      struct func_info *info = parse_func_def(s->d.FUNC_DEF.func,
                                                              s->d.FUNC_DEF.spec,
                                                              env);
                      context_deep_func(info,
                                        ctx);
                      k_func_begin(info, env);
                      break; }
  case PP_FUNC_DEC: { if (ctx->c->t != CTX_TOP)
                        failwith("Function declaration is not allowed here");
                      flow_env_deep(eph);
                      parse_func_dec(s->d.FUNC_DEC.func,
                                     s->d.FUNC_DEC.spec,
                                     env);
                      flow_env_up(eph);
                      break; }
  }

#undef ENSURE_NOT_TOP
}
