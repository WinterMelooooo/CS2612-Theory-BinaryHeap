// note:  - struct/union names and types are not preserved (both C types and
//            assertion types).

#include "cp.h"
#include "utils.h"
#include "../SymExec/AsrtDef/AssDef.h"
#include "../SymExec/Utility/OperatorTranser.h"

struct RAssertion *cpu_clone_ra(struct RAssertion *ra) {
  switch (ra->t) {
  case RA_CONST:
    return RAConst(ra->d.RACONST.value);
  case RA_PROGVAR:
    return RAVar(clone_str(ra->d.RAPROGVAR.name));
  case RA_BINOP:
    return RABinop(ra->d.RABINOP.op,
                   cpu_clone_ra(ra->d.RABINOP.left),
                   cpu_clone_ra(ra->d.RABINOP.right));
  case RA_UNOP:
    return RAUnop(ra->d.RAUNOP.op,
                  cpu_clone_ra(ra->d.RAUNOP.arg));
  case RA_APP:
    return RAApp(cpu_clone_ra(ra->d.RAAPP.f), cpu_clone_ra(ra->d.RAAPP.rand));
  case RA_DEREF:
    return RADeref(NULL, cpu_clone_ra(ra->d.RADEREF.arg));
  case RA_ADDRESS:
    return RAAddress(cpu_clone_ra(ra->d.RAADDRESS.arg));
  case RA_INDEX:
    return RAIndex(cpu_clone_ra(ra->d.RAINDEX.pos),
                   cpu_clone_ra(ra->d.RAINDEX.pos));
  case RA_FIELDOF:
    return RAFieldof(cpu_clone_ra(ra->d.RAFIELDOF.arg),
                     clone_str(ra->d.RAFIELDOF.name),
                     NULL);
  case RA_FIELDOFPTR:
    return RAFieldofptr(cpu_clone_ra(ra->d.RAFIELDOFPTR.arg),
                        clone_str(ra->d.RAFIELDOFPTR.name),
                        NULL);
  case RA_ENUMLIT:
    return RAEnumLit(clone_str(ra->d.RAENUMLIT.name));
  case RA_SHADOW:
    return RAShadow(cpu_clone_ra(ra->d.RASHADOW.arg));
  case RA_TIME_COST:
    return RATimeCost();
  case RA___RETURN:
    return RA__return();
  case RA_UNDEF_DATA_AT:
    return RAUndef_data_at(NULL, cpu_clone_ra(ra->d.RAUNDEF_DATA_AT.addr));
  case RA_OLD:
    return RAOld(clone_str(ra->d.RAOLD.mark), cpu_clone_ra(ra->d.RAOLD.arg));
  case RA_LOGICVAR:
  case RA_CONN:
  case RA_CAST:
  case RA_ANN:
  case RA_QFOP:
  case RA_EMP:
  case RA_SIZEOF:
  case RA_TRUE:
  case RA_FALSE:
  case RA_DATA_AT:
  case RA_FIELD_ADDRESS:
  case RA_ARR:
  case RA_SPEC:
    assert(0);
  }
}

void cpu_free_deriv(struct pp_derivtype *d);
void cpu_free_annot_list(struct annot_list *l) {
  if (l == NULL)
    return;
  free(l->head->type->triv);
  cpu_free_deriv(l->head->type->deriv);
  free(l->head->type);
  free(l->head);
  cpu_free_annot_list(l->tail);
  free(l);
}

void cpu_free_deriv(struct pp_derivtype *d) {
  switch (d->t) {
  case PP_DERIV_END:
    break;
  case PP_DERIV_PTR:
    cpu_free_deriv(d->d.PTR.deriv);
    break;
  case PP_DERIV_ARRAY:
    free(d->d.ARRAY.size);
    cpu_free_deriv(d->d.ARRAY.deriv);
    break;
  case PP_DERIV_FUNCTION:
    cpu_free_annot_list(d->d.FUNCTION.param);
    cpu_free_deriv(d->d.FUNCTION.deriv);
    break;
  }
  free(d);
}

void cpu_free_ra(struct RAssertion *ra) {
  switch (ra->t) {
  case RA_CONST:
    break;
  case RA_PROGVAR:
    free(ra->d.RAPROGVAR.name);
    break;
  case RA_BINOP:
    cpu_free_ra(ra->d.RABINOP.left);
    cpu_free_ra(ra->d.RABINOP.right);
    break;
  case RA_CONN:
    cpu_free_ra(ra->d.RACONN.left);
    cpu_free_ra(ra->d.RACONN.right);
    break;
  case RA_UNOP:
    cpu_free_ra(ra->d.RAUNOP.arg);
    break;
  case RA_APP:
    cpu_free_ra(ra->d.RAAPP.f);
    cpu_free_ra(ra->d.RAAPP.rand);
    break;
  case RA_DEREF:
    cpu_free_ra(ra->d.RADEREF.arg);
    break;
  case RA_ADDRESS:
    cpu_free_ra(ra->d.RAADDRESS.arg);
    break;
  case RA_INDEX:
    cpu_free_ra(ra->d.RAINDEX.arg);
    cpu_free_ra(ra->d.RAINDEX.pos);
    break;
  case RA_FIELDOF:
    cpu_free_ra(ra->d.RAFIELDOF.arg);
    free(ra->d.RAFIELDOF.name);
    break;
  case RA_FIELDOFPTR:
    cpu_free_ra(ra->d.RAFIELDOFPTR.arg);
    free(ra->d.RAFIELDOFPTR.name);
    break;
  case RA_QFOP:
    free(ra->d.RAQFOP.abs.name);
    cpu_free_ra(ra->d.RAQFOP.arg);
    break;
  case RA_ENUMLIT:
  case RA_EMP:
  case RA___RETURN:
  case RA_TIME_COST:
  case RA_TRUE:
  case RA_FALSE:
    break;
  case RA_SHADOW:
    cpu_free_ra(ra->d.RASHADOW.arg);
    break;
  case RA_ARR:
    cpu_free_ra(ra->d.RAARR.addr);
    cpu_free_ra(ra->d.RAARR.len);
    cpu_free_ra(ra->d.RAARR.list);
    break;
  case RA_SPEC:
    free(ra->d.RASPEC.sig->triv);
    cpu_free_deriv(ra->d.RASPEC.sig->deriv);
    free(ra->d.RASPEC.sig);
    cpu_free_ra(ra->d.RASPEC.f);
    cpu_free_pp_spec(ra->d.RASPEC.spec);
    break;
  case RA_UNDEF_DATA_AT:
    cpu_free_ra(ra->d.RAUNDEF_DATA_AT.addr);
    break;
  case RA_OLD:
    free(ra->d.RAOLD.mark);
    cpu_free_ra(ra->d.RAOLD.arg);
    break;
  case RA_CAST:
  case RA_ANN:
  case RA_SIZEOF:
  case RA_DATA_AT:
  case RA_FIELD_ADDRESS:
  case RA_LOGICVAR:
    assert(0);
  }
  free(ra);
}

void cpu_free_lvar_list(struct lvar_list *l) {
  if (l == NULL)
    return;
  struct lvar_list *tl = l->next;
  free(l);
  cpu_free_lvar_list(tl);
}

void cpu_free_pp_spec(struct pp_spec *spec) {
  cpu_free_lvar_list(spec->with);
  cpu_free_ra(spec->pre);
  cpu_free_ra(spec->post);
  free(spec);
}

void cpu_c_addressable(void *l, struct hashtbl *map, struct environment *env);
void cpu_c_nonaddressable(void *l, struct hashtbl *map, struct environment *env);

/* graph stuff */

struct cpu_node_list;

struct cpu_node {
  enum { WHITE, GREY, BLACK } color;
  int occur;
  struct ExprVal *val;
  struct Separation *sep; // corresponding proposition
  struct RAssertion *uval;
  struct cpu_node_list *neighbor;
};

struct cpu_node_list {
  struct cpu_node *node;
  struct cpu_node_list *next;
};

struct cpu_node_list *cpu_node_cons(struct cpu_node *car, struct cpu_node_list *cdr) {
  struct cpu_node_list *res;
  res = (struct cpu_node_list *)malloc(sizeof(struct cpu_node_list));
  res->node = car;
  res->next = cdr;
  return res;
}

void cpu_add_edge(struct cpu_node *from, struct cpu_node *to) {
  struct cpu_node_list *it;
  for (it = from->neighbor; it != NULL; it = it->next)
    if (it->node == to)
      return;
  from->neighbor = cpu_node_cons(to, from->neighbor);
}

struct cpu_node_list *cpu_dfs(struct cpu_node *n, struct cpu_node_list *sorted) {
  struct cpu_node_list *it;
  n->color = GREY;
  for (it = n->neighbor; it != NULL; it = it->next)
    switch (it->node->color) {
    case WHITE:
      sorted = cpu_dfs(it->node, sorted);
      break;
    case GREY:
      n->color = BLACK;
      return sorted;
    case BLACK:
      break;
    }
  n->color = BLACK;
  return cpu_node_cons(n, sorted);
}

struct cpu_node_list *cpu_list;
void cpu_sort_aux(void *key, void *val) {
  struct cpu_node *node;
  node = val;
  if (node->color == WHITE)
    cpu_list = cpu_dfs(node, cpu_list);
}
struct cpu_node_list *cpu_sort(struct hashtbl *graph) {
  cpu_list = NULL;
  hashtbl_iter(graph, cpu_sort_aux);
  return cpu_list;
}

// graph is a hash table id -> node

struct cpu_node *cpu_find_node(unsigned int id, struct hashtbl *graph) {
  int v;
  return hashtbl_find(graph, cast_int(id), &v);
}

/* graph end */

void cpu_add_dependency(struct cpu_node *from, struct ExprVal *e, struct hashtbl *g) {
  switch (e->t) {
  case EZ_VAL:
  case TIME_COST:
  case SIZE_OF:
    break;
  case VFIELD_ADDRESS:
    cpu_add_dependency(from, e->d.VFIELD_ADDRESS.expr, g);
    break;
  case LINDEX:
    cpu_add_dependency(from, e->d.LINDEX.list, g);
    cpu_add_dependency(from, e->d.LINDEX.index, g);
    break;
  case VUOP:
    cpu_add_dependency(from, e->d.VUOP.expr, g);
    break;
  case VBOP:
    cpu_add_dependency(from, e->d.VBOP.expr1, g);
    cpu_add_dependency(from, e->d.VBOP.expr2, g);
    break;
  case FUNCAPP: {
    struct cpu_node *to;
    to = cpu_find_node(e->d.FUNCAPP.id, g);
    if (to != NULL)
      cpu_add_edge(from, to);
    break;
    struct ExprValListNode *l;
    for (l = e->d.FUNCAPP.args->head; l != NULL; l = l->next)
      cpu_add_dependency(from, l->data, g);
    break; }
  }
}

struct logic_var_info *cpu_potentially_substutable(struct ExprVal *e, struct environment *env) {
  if (e->t == FUNCAPP &&
      e->d.FUNCAPP.args->head == NULL) {
    struct logic_var_info *info = find_logic_var_by_id(e->d.FUNCAPP.id, &env->persist);
    if (info->category == LOGIC_GEN_EXISTS || info->category == LOGIC_USER_EXISTS)
      return info;
    else
      return NULL;
  } else
    return NULL;
}

struct cpu_node *cpu_init_node(struct Separation *sep, struct ExprVal *val) {
  struct cpu_node *node = (struct cpu_node *)malloc(sizeof(struct cpu_node));
  node->sep = sep;
  node->occur = 0;
  node->color = WHITE;
  node->val = val;
  node->neighbor = NULL;
  node->uval = NULL;
  return node;
}

void cpu_build_graph(struct SepList *sepl, struct hashtbl *map, struct environment *env) {
  struct cpu_node *node;
  struct SepList *it;
  struct Separation *sep;

  for (it = sepl; it != NULL; it = it->next) { // todo: simplify
    sep = it->head;
    if (sep->t == T_DATA_AT) {
      struct logic_var_info *info = cpu_potentially_substutable(sep->d.DATA_AT.right, env);
      if (info != NULL)
        hashtbl_add(map, cast_int(sep->d.DATA_AT.right->d.FUNCAPP.id),
                    cpu_init_node(sep, sep->d.DATA_AT.left));
    } else if (sep->t == T_ARR) {
      struct logic_var_info *info = cpu_potentially_substutable(sep->d.ARR.value, env);
      if (info != NULL)
        hashtbl_add(map, cast_int(sep->d.ARR.value->d.FUNCAPP.id),
                    cpu_init_node(sep, sep->d.ARR.addr));
    }
  }
  for (it = sepl; it != NULL; it = it->next) {
    sep = it->head;
    if (sep->t == T_DATA_AT) {
      if (cpu_potentially_substutable(sep->d.DATA_AT.right, env)) {
        node = cpu_find_node(sep->d.DATA_AT.right->d.FUNCAPP.id, map);
        cpu_add_dependency(node, node->val, map);
      }
    } else if (sep->t == T_ARR) {
      if (cpu_potentially_substutable(sep->d.ARR.value, env)) {
        node = cpu_find_node(sep->d.ARR.value->d.FUNCAPP.id, map);
        cpu_add_dependency(node, node->val, map);
      }
    }
  }
}

void cpu_make_occur(struct cpu_node *node) {
  if (node->occur == 0) {
    node->occur = 1;
    struct cpu_node_list *it;
    for (it = node->neighbor; it != NULL; it = it->next)
      cpu_make_occur(it->node);
  }
}

char *cpu_id_to_varname(unsigned int id, struct environment *env) {
  struct logic_var_info *info;
  info = find_logic_var_by_id(id, &env->persist);

  if (info->category == LOGIC_EXTERN ||
      info->category == LOGIC_FREE ||
      info->category == LOGIC_SEPDEF)
    return clone_str(info->name);

  char *fmt = embed_str("%s_%%u", info->name);
  char *ret = embed_int(fmt, id);
  free(fmt);
  return ret;
}

struct RAssertion *cpu_id_to_var(unsigned int id, struct environment *env) {
  struct logic_var_info *info;
  info = find_logic_var_by_id(id, &env->persist);
  // maybe better put into c_local?
  if (info->value_or_address != NULL && info->value_or_address->value == info)
    return RAOld(clone_str("pre"), RAVar(clone_str(info->name)));
  // a little slow
  return RAVar(cpu_id_to_varname(id, env));
}

struct RAssertion *cpu_exprval(struct ExprVal *e, struct hashtbl *map, int occur,
                               struct environment *env);

struct RAssertion *cpu_app(int id, struct ExprValListNode *arg, struct hashtbl *map, int occur,
                           struct environment *env) {
  struct RAssertion *ret;
  struct cpu_node *node = cpu_find_node(id, map);
  if (node == NULL || node->uval == NULL)
    ret = cpu_id_to_var(id, env);
  else {
    if (occur)
      cpu_make_occur(node);
    ret = cpu_clone_ra(node->uval);
  }
  struct ExprValListNode *i;
  for (i = arg; i != NULL; i = i->next)
    ret = RAApp(ret, cpu_exprval(i->data, map, occur, env));
  return ret;
}

struct RAssertion *cpu_exprval(struct ExprVal *e, struct hashtbl *map, int occur,
                               struct environment *env) {
  switch (e->t) {
  case TIME_COST:
    return RATimeCost();
  case EZ_VAL:
    return RAConst(e->d.EZ_VAL.number);
  case SIZE_OF:
    // shall be improved
    return RAConst(type_size(type_of_simple_ctype(e->d.SIZE_OF.type, &env->persist)));
  case VFIELD_ADDRESS: {
    struct field_info *field = find_field_by_id(e->d.VFIELD_ADDRESS.field_id, &env->persist);
    return RAAddress(RAFieldofptr(cpu_exprval(e->d.VFIELD_ADDRESS.expr, map, occur, env),
                                  clone_str(field->name),
                                  NULL)); }
  case LINDEX:
    return RAIndex(cpu_exprval(e->d.LINDEX.list, map, occur, env),
                   cpu_exprval(e->d.LINDEX.index, map, occur, env));
  case VUOP:
    return RAUnop(InnerUnaryToUserUnary(e->d.VUOP.op),
                  cpu_exprval(e->d.VUOP.expr, map, occur, env));
  case VBOP:
    return RABinop(InnerBinOpToUserBinOp(e->d.VBOP.op),
                   cpu_exprval(e->d.VBOP.expr1, map, occur, env),
                   cpu_exprval(e->d.VBOP.expr2, map, occur, env));
  case FUNCAPP:
    return cpu_app(e->d.FUNCAPP.id, e->d.FUNCAPP.args->head, map, occur, env);
  }
}

struct RAssertion *cpu_sep(struct Separation *sep, struct hashtbl *map, struct environment *env) {
  switch (sep->t) {
  case T_DATA_AT: {
    struct RAssertion *v;
    if (cpu_potentially_substutable(sep->d.DATA_AT.right, env) &&
        (cpu_find_node(sep->d.DATA_AT.right->d.FUNCAPP.id, map)->uval == NULL))
      v = RAVar(cpu_id_to_varname(sep->d.DATA_AT.right->d.FUNCAPP.id, env));
    else
      v = cpu_exprval(sep->d.DATA_AT.right, map, 1, env);
    return RABinop(T_EQ,
                   RADeref(NULL,
                           cpu_exprval(sep->d.DATA_AT.left, map, 1, env)), v); }
  case T_UNDEF_DATA_AT:
    return RAUndef_data_at(NULL, cpu_exprval(sep->d.UNDEF_DATA_AT.left, map, 1, env));
  case T_ARR: {
    struct RAssertion *v;
    if (cpu_potentially_substutable(sep->d.ARR.value, env) &&
        (cpu_find_node(sep->d.DATA_AT.right->d.FUNCAPP.id, map)->uval == NULL))
      v = RAVar(cpu_id_to_varname(sep->d.ARR.value->d.FUNCAPP.id, env));
    else
      v = cpu_exprval(sep->d.ARR.value, map, 1, env);
    return RAArr(cpu_exprval(sep->d.ARR.addr, map, 1, env),
                 NULL,
                 cpu_exprval(sep->d.ARR.size, map, 1, env),
                 v); }
  case T_OTHER:
    return cpu_app(sep->d.OTHER.sep_id, sep->d.OTHER.exprs->head, map, 1, env);
  }
}

struct RAssertion *cpu_prop(struct Proposition *prop, struct hashtbl *map,
                            struct environment *env) {
  switch (prop->t) {
  case T_PROP_TRUE:
    return RATrue();
  case T_PROP_FALSE:
    return RAFalse();
  case T_PROP_UNARY:
    return RAUnop(T_NOTBOOL, cpu_prop(prop->d.UNARY.prop, map, env));
  case T_PROP_BINARY: {
    struct RAssertion *p;
    struct RAssertion *q;
    p = cpu_prop(prop->d.BINARY.prop1, map, env);
    q = cpu_prop(prop->d.BINARY.prop2, map, env);
    switch (prop->d.BINARY.op) {
    case PROP_AND:
      return RABinop(T_AND, p, q);
    case PROP_OR:
      return RABinop(T_OR, p, q);
    case PROP_IMPLY:
      return RAConn(A_IMPLY, p, q);
    case PROP_IFF:
      return RAConn(A_IFF, p, q);
    }}
  case T_PROP_PTR: {
    struct RAssertion *expr;
    expr = cpu_exprval(prop->d.PTR.expr, map, 1, env);
    switch (prop->d.PTR.op) {
    case PROP_NOT_NULL:
      return RABinop(T_NE, expr, RAConst(0));
    case PROP_MAYBE_NULL:
      return RABinop(T_OR,
                     RABinop(T_EQ, expr, RAConst(0)),
                     RABinop(T_NE, expr, RAConst(0)));
    case PROP_IS_NULL:
      return RABinop(T_EQ, expr, RAConst(0));
    }}
  case T_PROP_COMPARE:
    return RABinop(InnerToUserPropCompOpTrans(prop->d.COMPARE.op),
                   cpu_exprval(prop->d.COMPARE.expr1, map, 1, env),
                   cpu_exprval(prop->d.COMPARE.expr2, map, 1, env));
  case T_PROP_QUANTIFIER:
    if (prop->d.QUANTIFIER.op == PROP_FORALL)
      return RAQfop(A_FORALL, 0, cpu_id_to_varname(prop->d.QUANTIFIER.ident, env),
                    NULL, NULL,
                    cpu_prop(prop->d.QUANTIFIER.prop, map, env));
    else
      return RAQfop(A_EXISTS, 0, cpu_id_to_varname(prop->d.QUANTIFIER.ident, env),
                    NULL, NULL,
                    cpu_prop(prop->d.QUANTIFIER.prop, map, env));
  case T_PROP_OTHER:
    return cpu_app(prop->d.OTHER.predicate, prop->d.OTHER.args->head, map, 1, env);
  }
}

struct pp_pretype * cpu_type(struct type *ty);

struct annot_list *cpu_type_list(struct type_list *l) {
  if (l == NULL)
    return NULL;
  return ALCons(TAnnot(cpu_type(l->hd)), cpu_type_list(l->tl));
}

void cpu_type_rec(struct type *ty, struct pp_trivtype **triv, struct pp_derivtype **deriv) {
  ty = type_unalias(ty);
  switch (ty->t) {
  case T_BASIC:
    *triv = TRIVBasic(ty->d.BASIC.ty);
    break;
  case T_STRUCT:
    *triv = TRIVStruct(clone_str(ty->d.STRUCT.info->name));
    break;
  case T_UNION:
    *triv = TRIVUnion(clone_str(ty->d.UNION.info->name));
    break;
  case T_ENUM:
    *triv = TRIVUnion(clone_str(ty->d.ENUM.info->name));
    break;
  case T_PTR:
    *deriv = DERIVPtr(*deriv);
    break;
  case T_ARRAY:
    *deriv = DERIVArray(*deriv, PPConst(ty->d.ARRAY.size, 0, 0, 0));;
    break;
  case T_FUNCTION:
    *deriv = DERIVFunction(*deriv, cpu_type_list(ty->d.FUNCTION.param));
    break;
  case T_TYPE_ALIAS:
    assert(0);
  }
}

struct pp_pretype *cpu_type(struct type *ty) {
  struct pp_trivtype *triv;
  struct pp_derivtype *deriv = DERIVEnd(NULL);
  cpu_type_rec(ty, &triv, &deriv);
  return PreType(triv, deriv);
}

struct annot_list *cpu_info_list(struct prog_var_info_list *l) {
  if (l == NULL)
    return NULL;
  return ALCons(TAnnot(cpu_type(l->head->type)), cpu_info_list(l->tail));
}

struct RAssertion *cpu_fspec(struct FPSpec *s, struct hashtbl *map, struct environment *env) {
  struct pp_pretype *pre = cpu_type(s->func_info->ret_type);
  pre->deriv = DERIVFunction(pre->deriv, cpu_info_list(s->func_info->param));
  return RASpec(cpu_exprval(s->fp_addr, map, 1, env), pre, cpu_spec(s->func_info->spec, env));
}

struct RAssertion *cpu_prog_var(unsigned int id, struct environment *env) {
  struct prog_var_info *info;
  info = find_prog_var_by_id(id, &env->persist);
  struct RAssertion *res;
  res = RAVar(clone_str(info->name));
  for (info = find_prog_var_by_name(info->name, &env->ephemer)->d.prog_var;
       info->id != id;
       info = info->shadowing)
    res = RAShadow(res);
  return res;
}

void cpu_eval_mapping(struct cpu_node_list *sorted, struct hashtbl *map, struct environment *env) {
  if (sorted == NULL)
    return;
  cpu_eval_mapping(sorted->next, map, env);
  switch (sorted->node->sep->t) {
  case T_DATA_AT:
    sorted->node->uval = RADeref(NULL,
                                 cpu_exprval(sorted->node->val, map, 0, env));
    break;
  case T_ARR: {
    struct RAssertion *t;
    t = cpu_exprval(sorted->node->val, map, 0, env);
    cpb_assert(t, env);
    cpt_assert(t, NULL);
    if (t->type != NULL && type_unalias(t->type)->t == T_ARRAY) // can be inferred
      sorted->node->uval = t;
    else {
      free_ra(t);
      sorted->node->uval = NULL;
    }
    break; }
  case T_UNDEF_DATA_AT:
  case T_OTHER:
    assert(0);
  }
}

struct RAssertion *cpu_simplify(struct RAssertion *ra) {
  switch (ra->t) {
  case RA_CONST:
  case RA_LOGICVAR:
  case RA_PROGVAR:
  case RA_EMP:
  case RA___RETURN:
  case RA_SHADOW:
  case RA_TRUE:
  case RA_FALSE:
  case RA_TIME_COST:
  case RA_OLD:
    return ra;
  case RA_ENUMLIT:
  case RA_SIZEOF:
  case RA_CAST:
    assert(0);
  case RA_BINOP:
    ra->d.RABINOP.left = cpu_simplify(ra->d.RABINOP.left);
    ra->d.RABINOP.right = cpu_simplify(ra->d.RABINOP.right);
    return ra;
  case RA_CONN:
    ra->d.RACONN.left = cpu_simplify(ra->d.RACONN.left);
    ra->d.RACONN.right = cpu_simplify(ra->d.RACONN.right);
    return ra;
  case RA_UNOP:
    ra->d.RAUNOP.arg = cpu_simplify(ra->d.RAUNOP.arg);
    return ra;
  case RA_APP:
    ra->d.RAAPP.f = cpu_simplify(ra->d.RAAPP.f);
    ra->d.RAAPP.rand = cpu_simplify(ra->d.RAAPP.rand);
    return ra;
  case RA_DEREF:
    ra->d.RADEREF.arg = cpu_simplify(ra->d.RADEREF.arg);
    if (ra->d.RADEREF.arg->t == RA_ADDRESS) {
      struct RAssertion *res;
      res = ra->d.RADEREF.arg->d.RAADDRESS.arg;
      free(ra->d.RADEREF.arg);
      free(ra);
      return res;
    }
    return ra;
  case RA_ADDRESS:
    ra->d.RAADDRESS.arg = cpu_simplify(ra->d.RAADDRESS.arg);
    if (ra->d.RAADDRESS.arg->t == RA_DEREF) {
      struct RAssertion *res;
      res = ra->d.RAADDRESS.arg->d.RADEREF.arg;
      free(ra->d.RAADDRESS.arg);
      free(ra);
      return res;
    }
    return ra;
  case RA_INDEX:
    ra->d.RAINDEX.arg = cpu_simplify(ra->d.RAINDEX.arg);
    ra->d.RAINDEX.pos = cpu_simplify(ra->d.RAINDEX.pos);
    return ra;
  case RA_FIELDOF:
    ra->d.RAFIELDOF.arg = cpu_simplify(ra->d.RAFIELDOF.arg);
    if (ra->d.RAFIELDOF.arg->t == RA_DEREF) {
      struct RAssertion *ret = RAFieldofptr(ra->d.RAFIELDOF.arg->d.RADEREF.arg, ra->d.RAFIELDOF.name, NULL);
      free(ra->d.RAFIELDOF.arg);
      free(ra);
      return ret;
    }
    return ra;
  case RA_FIELDOFPTR:
    ra->d.RAFIELDOFPTR.arg = cpu_simplify(ra->d.RAFIELDOFPTR.arg);
    if (ra->d.RAFIELDOFPTR.arg->t == RA_ADDRESS) {
      struct RAssertion *ret = RAFieldof(ra->d.RAFIELDOFPTR.arg->d.RAADDRESS.arg, ra->d.RAFIELDOFPTR.name, NULL);
      free(ra->d.RAFIELDOFPTR.arg);
      free(ra);
      return ret;
    }
    return ra;
  case RA_QFOP:
    ra->d.RAQFOP.arg = cpu_simplify(ra->d.RAQFOP.arg);
    return ra;
  case RA_ARR:
    ra->d.RAARR.addr = cpu_simplify(ra->d.RAARR.addr);
    ra->d.RAARR.len = cpu_simplify(ra->d.RAARR.len);
    ra->d.RAARR.list = cpu_simplify(ra->d.RAARR.list);
    return ra;
  case RA_SPEC:
    ra->d.RASPEC.f = cpu_simplify(ra->d.RASPEC.f);
    return ra;
  case RA_UNDEF_DATA_AT:
    ra->d.RAUNDEF_DATA_AT.addr = cpu_simplify(ra->d.RAUNDEF_DATA_AT.addr);
    return ra;
  case RA_DATA_AT:
  case RA_FIELD_ADDRESS:
  case RA_ANN:
    assert(0);
  }
}

// todo: time complexity
int cpu_occur_in(char *name, struct RAssertion *ra) {
  switch (ra->t) {
  case RA_LOGICVAR:
  case RA_TRUE:
  case RA_FALSE:
  case RA_ENUMLIT:
  case RA_EMP:
  case RA___RETURN:
  case RA_SIZEOF:
  case RA_TIME_COST:
  case RA_CONST: return 0;
  case RA_PROGVAR: return strcmp(ra->d.RAPROGVAR.name, name) == 0;
  case RA_BINOP: return cpu_occur_in(name, ra->d.RABINOP.left) || cpu_occur_in(name, ra->d.RABINOP.right);
  case RA_CONN: return cpu_occur_in(name, ra->d.RACONN.left) || cpu_occur_in(name, ra->d.RACONN.right);
  case RA_UNOP: return cpu_occur_in(name, ra->d.RAUNOP.arg);
  case RA_CAST: return cpu_occur_in(name, ra->d.RACAST.arg);
  case RA_APP: return cpu_occur_in(name, ra->d.RAAPP.f) || cpu_occur_in(name, ra->d.RAAPP.rand);
  case RA_DEREF: return cpu_occur_in(name, ra->d.RADEREF.arg);
  case RA_ADDRESS: return cpu_occur_in(name, ra->d.RAADDRESS.arg);
  case RA_INDEX: return cpu_occur_in(name, ra->d.RAINDEX.arg) || cpu_occur_in(name, ra->d.RAINDEX.pos);
  case RA_FIELDOF: return cpu_occur_in(name, ra->d.RAFIELDOF.arg);
  case RA_FIELDOFPTR: return cpu_occur_in(name, ra->d.RAFIELDOFPTR.arg);
  case RA_QFOP: return cpu_occur_in(name, ra->d.RAQFOP.arg);
  case RA_OLD: return cpu_occur_in(name, ra->d.RAOLD.arg);
  case RA_SHADOW: return cpu_occur_in(name, ra->d.RASHADOW.arg);
  case RA_DATA_AT: return cpu_occur_in(name, ra->d.RADATA_AT.addr) || cpu_occur_in(name, ra->d.RADATA_AT.val);
  case RA_FIELD_ADDRESS: return cpu_occur_in(name, ra->d.RAFIELD_ADDRESS.addr);
  case RA_ARR: return cpu_occur_in(name, ra->d.RAARR.addr) ||
                      cpu_occur_in(name, ra->d.RAARR.len) ||
                      cpu_occur_in(name, ra->d.RAARR.list);
  case RA_SPEC: return cpu_occur_in(name, ra->d.RASPEC.f);
  case RA_UNDEF_DATA_AT: return cpu_occur_in(name, ra->d.RAUNDEF_DATA_AT.addr);
  case RA_ANN:
    assert(0);
  }
}

void cpu_free_node_list(struct cpu_node_list *l) {
  if (l == NULL)
    return;
  struct cpu_node_list *tl = l->next;
  free(l);
  cpu_free_node_list(tl);
}

void cpu_free_node(void *id, void *node) {
  struct cpu_node *n = node;
  if (n->uval != NULL)
    cpu_free_ra(n->uval);
  cpu_free_node_list(n->neighbor);
  free(n);
}

struct RAssertion *cpu_heap(void (*local)(void *local, struct hashtbl *map,
                                          struct environment *env),
                            struct ExprVal *retval,
                            struct Assertion *h, struct environment *env) {
  struct hashtbl map;
  struct cpu_node_list *sorted;

  init_hashtbl(&map, hash_uint, uint_equal);

  {
    local(h->local_list, &map, env);
    if (retval != NULL) {
      struct cpu_node *node = (struct cpu_node *)malloc(sizeof(struct cpu_node));
      node->neighbor = NULL;
      node->color = BLACK;
      node->occur = 1;
      node->uval = RA__return();
      hashtbl_add(&map, cast_int(retval->d.FUNCAPP.id), node);
    }
  }

  cpu_build_graph(h->sep_list, &map, env);
  sorted = cpu_sort(&map);
  cpu_eval_mapping(sorted, &map, env);

  struct RAssertion *prop;
  if (h->prop_list == NULL)
    prop = NULL;
  else {
    struct PropList *i;
    prop = cpu_prop(h->prop_list->head, &map, env);
    for (i = h->prop_list->next; i != NULL; i = i->next)
      prop = RABinop(T_AND, prop, cpu_prop(i->head, &map, env));
  }

  struct RAssertion *fpspec;
  if (h->fp_spec_list->head == NULL)
    fpspec = NULL;
  else {
    struct FPSpecListNode *i;
    fpspec = cpu_fspec(h->fp_spec_list->head->data, &map, env);
    for (i = h->fp_spec_list->head->next; i != NULL; i = i->next)
      fpspec = RABinop(T_AND, fpspec, cpu_fspec(i->data, &map, env));
  }

  struct RAssertion *sep;
  struct RAssertion *sep_acc;
  sep_acc = NULL;
  struct SepList *i;
  for (i = h->sep_list; i != NULL; i = i->next) {
    if (i->head->t == T_DATA_AT &&
        cpu_potentially_substutable(i->head->d.DATA_AT.right, env) &&
        cpu_find_node(i->head->d.DATA_AT.right->d.FUNCAPP.id, &map)->uval != NULL)
      continue;
    if (i->head->t == T_ARR &&
        cpu_potentially_substutable(i->head->d.ARR.value, env) &&
        cpu_find_node(i->head->d.ARR.value->d.FUNCAPP.id, &map)->uval != NULL)
      continue;
    sep = cpu_sep(i->head, &map, env);
    if (sep_acc == NULL)
      sep_acc = sep;
    else
      sep_acc = RABinop(T_MUL, sep_acc, sep);
  }

  struct cpu_node_list *j;
  for (j = sorted; j != NULL; j = j->next)
    if (j->node->uval != NULL && j->node->occur == 0) {
      cpu_make_occur(j->node);
      sep = cpu_sep(j->node->sep, &map, env); // the unused variables should be kept as is
      if (sep_acc == NULL)
        sep_acc = sep;
      else
        sep_acc = RABinop(T_MUL, sep_acc, sep);
    }

  struct RAssertion *res;
  if (prop != NULL && fpspec != NULL && sep_acc != NULL)
    res = RABinop(T_AND, RABinop(T_AND, prop, fpspec), sep);
  else if (prop != NULL && fpspec != NULL)
    res = RABinop(T_AND, prop, fpspec);
  else if (prop != NULL && sep_acc != NULL)
    res = RABinop(T_AND, prop, sep_acc);
  else if (fpspec != NULL && sep_acc != NULL)
    res = RABinop(T_AND, fpspec, sep_acc);
  else if (prop != NULL)
    res = prop;
  else if (fpspec != NULL)
    res = fpspec;
  else if (sep_acc != NULL)
    res = sep_acc;
  else
    res = RAEmp();

  struct ExistList *l;
  for (l = h->exist_list; l != NULL; l = l->next) {
    char *name = cpu_id_to_varname(l->id, env);
    if (cpu_occur_in(name, res))
      res = RAQfop(A_EXISTS, 0, name,
                   NULL, NULL,
                   res);
    else
      free(name);
  }

  cpu_free_node_list(sorted);
  hashtbl_iter(&map, cpu_free_node);
  hashtbl_clear(&map);

  return cpu_simplify(res);
}

struct RAssertion *cpu_assert(void (*local)(void *local, struct hashtbl *map,
                                            struct environment *env),
                              struct ExprVal *retval,
                              struct AsrtList *a, struct environment *env) {
  if (a == NULL)
    return RAEmp();
  else if (a->next == NULL)
    return cpu_heap(local, retval, a->head, env);
  else
    return RABinop(T_OR, cpu_heap(local, retval, a->head, env), cpu_assert(local, retval, a->next, env));
}

struct RAssertion *cpu_comment(struct AsrtList *a, struct environment *env) {
  return cpu_assert(cpu_c_addressable, NULL, a, env);
}

struct lvar_list *cpu_withlist(struct ExistList *with, struct environment *env) {
  if (with == NULL)
    return NULL;
  return lvar_list_cons(find_logic_var_by_id(with->id, &env->persist)->name, NULL,
                        cpu_withlist(with->next, env));
}

struct pp_spec *cpu_spec(struct func_spec *spec, struct environment *env) {
  return PPSpec(spec->name, spec->derived_by,
                NULL, cpu_withlist(spec->with, env),
                cpu_assert(cpu_c_nonaddressable, spec->__return, spec->pre, env),
                cpu_assert(cpu_c_nonaddressable, spec->__return, spec->post, env));
}

void cpu_c_addressable(void *l, struct hashtbl *map, struct environment *env) {
  struct LocalLinkedHashMap *local;
  local = l;
  struct LocalLinkedHashMapNode *in;
  for (in = local->head; in != NULL; in = in->next)
    if (in->state == 1) {
      struct cpu_node *node;
      node = (struct cpu_node *)malloc(sizeof(struct cpu_node));
      node->neighbor = NULL;
      node->color = BLACK;
      node->occur = 1;
      if (type_unalias(find_prog_var_by_id(in->id, &env->persist)->type)->t == T_ARRAY)
        node->uval = cpu_prog_var(in->id, env);
      else
        node->uval = RAAddress(cpu_prog_var(in->id, env));
      hashtbl_add(map, cast_int(in->value->d.FUNCAPP.id), node);
    }
}

void cpu_c_nonaddressable(void *l, struct hashtbl *map, struct environment *env) {
  struct LocalLinkedHashMap *local;
  local = l;
  struct LocalLinkedHashMapNode *in;
  for (in = local->head; in != NULL; in = in->next)
    if (in->state == 1) {
      struct cpu_node *node;
      node = (struct cpu_node *)malloc(sizeof(struct cpu_node));
      node->neighbor = NULL;
      node->color = BLACK;
      node->occur = 1;
      node->uval = RAVar(clone_str(find_prog_var_by_id(in->id, &env->persist)->name));
      hashtbl_add(map, cast_int(in->value->d.FUNCAPP.id), node);
    }
}

