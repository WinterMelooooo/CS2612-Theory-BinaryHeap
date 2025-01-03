#include "utils.h"
#include "cp.h"

#include "../SymExec/Trans/TypeTrans.h"
#include "../SymExec/Utility/OperatorTranser.h"
#include "../SymExec/SymExec/CexprExec.h"
#include "../SymExec/Trans/AddressabilityTrans.h"

extern void* (*LocalDeepCopy)(void*);
int cpa_addressable;

struct RAssertion *cpa_clone_ra(struct RAssertion *ra) {
  struct RAssertion *res;
  switch (ra->t) {
  case RA_CONST:
    res = RAConst(ra->d.RACONST.value);
    break;
  case RA_PROGVAR:
    res = RAVar(NULL); // hack for cpuser
    res->d.RAPROGVAR.info = ra->d.RAPROGVAR.info;
    break;
  case RA_LOGICVAR:
    res = RALogicVar(ra->d.RALOGICVAR.info);
    res->d.RALOGICVAR.impl = clone_qvar_list(ra->d.RALOGICVAR.impl);
    break;
  case RA_BINOP:
    res = RABinop(ra->d.RABINOP.op,
                  cpa_clone_ra(ra->d.RABINOP.left),
                  cpa_clone_ra(ra->d.RABINOP.right));
    break;
  case RA_CONN:
    res = RAConn(ra->d.RACONN.op,
                 cpa_clone_ra(ra->d.RACONN.left),
                 cpa_clone_ra(ra->d.RACONN.right));
    break;
  case RA_UNOP:
    res = RAUnop(ra->d.RAUNOP.op,
                 cpa_clone_ra(ra->d.RAUNOP.arg));
    break;
  case RA_CAST:
    res = RACast(NULL,
                 cpa_clone_ra(ra->d.RACAST.arg));
    break;
  case RA_APP:
    res = RAApp(cpa_clone_ra(ra->d.RAAPP.f), cpa_clone_ra(ra->d.RAAPP.rand));
    break;
  case RA_ANN:
    res = RAAnn(ra->d.RAANN.type, cpa_clone_ra(ra->d.RAANN.expr));
    break;
  case RA_DEREF:
    res = RADeref(NULL, cpa_clone_ra(ra->d.RADEREF.arg));
    break;
  case RA_ADDRESS:
    res = RAAddress(cpa_clone_ra(ra->d.RAADDRESS.arg));
    break;
  case RA_INDEX:
    res = RAIndex(cpa_clone_ra(ra->d.RAINDEX.pos),
                  cpa_clone_ra(ra->d.RAINDEX.pos));
    break;
  case RA_FIELDOF:
    res = RAFieldof(cpa_clone_ra(ra->d.RAFIELDOF.arg),
                    NULL,
                    NULL);
    res->d.RAFIELDOF.field = ra->d.RAFIELDOF.field;
    break;
  case RA_FIELDOFPTR:
    res = RAFieldofptr(cpa_clone_ra(ra->d.RAFIELDOFPTR.arg),
                       NULL,
                       NULL);
    res->d.RAFIELDOFPTR.field = ra->d.RAFIELDOFPTR.field;
    break;
  case RA_QFOP:
    res = RAQfop(ra->d.RAQFOP.op,
                 ra->d.RAQFOP.bracket,
                 NULL,
                 NULL, NULL,
                 cpa_clone_ra(ra->d.RAQFOP.arg));
    res->d.RAQFOP.abs.info = ra->d.RAQFOP.abs.info;
    break;
  case RA_ENUMLIT:
    res = RAEnumLit(NULL);
    res->d.RAENUMLIT.info = ra->d.RAENUMLIT.info;
    break;
  case RA_EMP:
    res = RAEmp();
    break;
  case RA___RETURN:
    res = RA__return();
    break;
  case RA_SIZEOF:
    res = RASizeOf(NULL);
    ASSIGN_TYPE(res->d.RASIZEOF.type, ra->d.RASIZEOF.type);
    break;
  case RA_OLD:
    res = RAOld(clone_str(ra->d.RAOLD.mark),
                cpa_clone_ra(ra->d.RAOLD.arg));
    break;
  case RA_SHADOW:
    res = RAShadow(cpa_clone_ra(ra->d.RASHADOW.arg));
    break;
  case RA_TRUE:
    res = RATrue();
    break;
  case RA_FALSE:
    res = RAFalse();
    break;
  case RA_DATA_AT:
    res = RAData_at(NULL,
                    cpa_clone_ra(ra->d.RADATA_AT.addr),
                    cpa_clone_ra(ra->d.RADATA_AT.val));
    ASSIGN_TYPE(res->d.RADATA_AT.ty, ra->d.RADATA_AT.ty);
    break;
  case RA_UNDEF_DATA_AT:
    res = RAUndef_data_at(NULL,
                          cpa_clone_ra(ra->d.RAUNDEF_DATA_AT.addr));
    ASSIGN_TYPE(res->d.RAUNDEF_DATA_AT.ty, ra->d.RAUNDEF_DATA_AT.ty);
    break;
  case RA_FIELD_ADDRESS:
    res = RAField_addr(cpa_clone_ra(ra->d.RAFIELD_ADDRESS.addr),
                       NULL,
                       NULL);
    res->d.RAFIELD_ADDRESS.field = ra->d.RAFIELD_ADDRESS.field;
    break;
  case RA_ARR:
    res = RAArr(cpa_clone_ra(ra->d.RAARR.addr),
                NULL,
                cpa_clone_ra(ra->d.RAARR.len),
                cpa_clone_ra(ra->d.RAARR.list));
    ASSIGN_TYPE(res->d.RAARR.ty, ra->d.RAARR.ty);
    break;
  case RA_SPEC:
    res = RASpec(cpa_clone_ra(ra->d.RASPEC.f), NULL, NULL);
    res->d.RASPEC.info = ra->d.RASPEC.info;
    break;
  case RA_TIME_COST:
    res = RATimeCost();
    break;
  }
  if (ra->type != NULL)
    ASSIGN_TYPE(res->type, ra->type);
  return res;
}

/* DNF */

int cpa_is_relop(enum BinOpType op) {
  switch (op) {
  case T_LT:
  case T_GT:
  case T_LE:
  case T_GE:
  case T_EQ:
  case T_NE: return 1;
  default:   return 0;
  }
}

int cpa_is_conn(enum BinOpType op) {
  switch (op) {
  case T_AND:
  case T_MUL:
  case T_OR: return 1;
  default:   return 0;
  }
}

void cpa_shallow_free(struct RAssertion *l) {
  if (l != NULL) {
    cpa_shallow_free(l->d.RABINOP.right);
    free(l);
  }
}

// destruct l and r
struct RAssertion *cpa_prod(enum BinOpType conn, struct RAssertion *l, struct RAssertion *r) {
  struct RAssertion *res;
  struct RAssertion *it1;
  struct RAssertion *it2;

  res = NULL;
  for (it1 = l; it1 != NULL; it1 = it1->d.RABINOP.right)
    for (it2 = r; it2 != NULL; it2 = it2->d.RABINOP.right)
      if (it1 == l && it2 == r)
        res = RABinop(T_OR, RABinop(conn, it1->d.RABINOP.left, it2->d.RABINOP.left), res);
      else if (it1 == l)
        res = RABinop(T_OR, RABinop(conn, cpa_clone_ra(it1->d.RABINOP.left), it2->d.RABINOP.left), res);
      else if (it2 == r)
        res = RABinop(T_OR, RABinop(conn, it1->d.RABINOP.left, cpa_clone_ra(it2->d.RABINOP.left)), res);
      else
        res = RABinop(T_OR, RABinop(conn, cpa_clone_ra(it1->d.RABINOP.left), cpa_clone_ra(it2->d.RABINOP.left)), res);
  cpa_shallow_free(l);
  cpa_shallow_free(r);
  return res;
}

// destruct l1 and l2
struct RAssertion *cpa_append(struct RAssertion *l1, struct RAssertion *l2) {
  if (l1 == NULL)
    return l2;
  l1->d.RABINOP.right = cpa_append(l1->d.RABINOP.right, l2);
  return l1;
}

struct RAssertion *cpa_dnf1(struct RAssertion *ra) {
  switch (ra->t) {
  case RA_CONST:
  case RA_PROGVAR:
  case RA_CAST:
  case RA_DEREF:
  case RA_ADDRESS:
  case RA_INDEX:
  case RA_FIELDOF:
  case RA_FIELDOFPTR:
  case RA_ENUMLIT:
  case RA___RETURN:
  case RA_OLD:
  case RA_SHADOW:
  case RA_SIZEOF:
  case RA_FIELD_ADDRESS:
  case RA_TIME_COST:
    failwith("Expected proposition");
  case RA_BINOP:
    if (ra->d.RABINOP.op == T_OR) {
      struct RAssertion *res = cpa_append(cpa_dnf1(ra->d.RABINOP.left),
                                          cpa_dnf1(ra->d.RABINOP.right));
      free(ra);
      return res;
    } else if (cpa_is_conn(ra->d.RABINOP.op)) {
      struct RAssertion *res = cpa_prod(ra->d.RABINOP.op,
                                        cpa_dnf1(ra->d.RABINOP.left),
                                        cpa_dnf1(ra->d.RABINOP.right));
      free(ra);
      return res;
    } else if (cpa_is_relop(ra->d.RABINOP.op))
      return RABinop(T_OR, ra, NULL);
    else
      failwith("Expected proposition");
  case RA_UNOP:
    if (ra->d.RAUNOP.op == T_NOTBOOL)
      return RABinop(T_OR, ra, NULL);
    else
      failwith("Expected proposition");
  case RA_QFOP:
    if (ra->d.RAQFOP.op == A_EXISTS) {
      struct RAssertion *ra1 = ra->d.RAQFOP.arg;
      free(ra);
      return cpa_dnf1(ra1);
    } else
      return RABinop(T_OR, ra, NULL);
  case RA_CONN:
  case RA_DATA_AT:
  case RA_UNDEF_DATA_AT:
  case RA_ARR:
  case RA_SPEC:
  case RA_EMP:
  case RA_TRUE:
  case RA_FALSE:
  case RA_LOGICVAR:
  case RA_APP:
  case RA_ANN:
    return RABinop(T_OR, ra, NULL);
  }
}

struct RAssertion *cpa_build_disj(struct RAssertion *as) {
  if (as->d.RABINOP.right == NULL) {
    struct RAssertion *res = as->d.RABINOP.left;
    free(as);
    return res;
  }
  as->d.RABINOP.right = cpa_build_disj(as->d.RABINOP.right);
  return as;
}

struct RAssertion *cpa_dnf(struct RAssertion *ra) {
  if (ra == NULL)
    return ra;
  struct RAssertion *dnf = cpa_dnf1(ra);
  struct RAssertion *res = cpa_build_disj(dnf);
  return res;
}

/* DNF end */

struct __RETURN_OCCUR {
  struct ExprVal *v;
  int occur;
};

struct cpa_param {
  int old;
  struct __RETURN_OCCUR *retval;
  struct Assertion *ctx;
  struct Assertion *a;
  struct environment *env;
  struct hashtbl autogen;
  int is_post; // if so, make any `old value' computed free
};

struct ExistList *cpa_add_exist(unsigned int id, struct ExistList *list){
  if (list == NULL)
    return ExistListCons(id, list);
  if ((unsigned int)list->id == id)
    return list;
  list->next = cpa_add_exist(id, list->next);
  return list;
}

void cpa_add_autogen(unsigned int id, struct cpa_param *rec) {
  rec->a->exist_list = cpa_add_exist(id, rec->a->exist_list);
  hashtbl_add(&rec->autogen, cast_int(id), NULL);
}

void cpa_ensure_local(struct prog_var_info *var, struct Assertion *a) {
  // if it is called only in addressable mode
  if (LocalFind(var->id, a->local_list) == NULL) {
    struct ExprVal *e = ExprVal_V_VARI(var->address->id);
    LocalInsert(var->id, e, a->local_list);
    ExprValFree(e);
  }
}

char *cpa_name_or_null(struct ExprVal *e, struct environment *env) {
  if (e->t == FUNCAPP && e->d.FUNCAPP.args->head == NULL)
    return find_logic_var_by_id(e->d.FUNCAPP.id, &env->persist)->name;
  else
    return NULL;
}

struct renaming_info *cpa_rename_or_null(struct ExprVal *e, struct environment *env) {
  if (e->t == FUNCAPP && e->d.FUNCAPP.args->head == NULL)
    return renaming_info_deep_copy(find_logic_var_by_id(e->d.FUNCAPP.id, &env->persist)->renaming);
  else
    return NULL;
}

struct Separation * GetDataSepAtValue(struct Assertion * inner_asrt, struct ExprVal * expr) {
   struct SepList * sep_list = inner_asrt->sep_list;
   while (sep_list != NULL) {
      if (sep_list->head->t == T_DATA_AT) {
         if (ExprValCheckEqual(expr, sep_list->head->d.DATA_AT.left)) {
            return sep_list->head;
         }
      }
      sep_list = sep_list->next;
   }
   return NULL;
}

void cpa_make_free(struct ExprVal *e, struct environment *env) {
   switch (e->t) {
   case EZ_VAL:
   case TIME_COST:
   case SIZE_OF:
     break;
   case VFIELD_ADDRESS:
     cpa_make_free(e->d.VFIELD_ADDRESS.expr, env);
     break;
   case VUOP:
     cpa_make_free(e->d.VUOP.expr, env);
     break;
   case VBOP:
     cpa_make_free(e->d.VBOP.expr1, env);
     cpa_make_free(e->d.VBOP.expr2, env);
     break;
   case FUNCAPP:
     find_logic_var_by_id(e->d.FUNCAPP.id, &env->persist)->category = LOGIC_FREE;
     {
       struct ExprValListNode *i;
       for (i = e->d.FUNCAPP.args->head; i != NULL; i = i->next)
         cpa_make_free(i->data, env);
     }
     break;
   case LINDEX:
     cpa_make_free(e->d.LINDEX.index, env);
     cpa_make_free(e->d.LINDEX.list, env);
     break;
   }
}

struct ExprVal *cpa_value_at_address(struct ExprVal *addr,
                                     struct type *ty,
                                     char *fmt,
                                     char *name,
                                     struct renaming_info *r,
                                     struct cpa_param *rec) {
  struct ExprVal *val = GetDataAtValue(rec->a, addr);
  if (val == NULL) {
    struct Separation *s = GetDataSepAtValue(rec->ctx, addr);
    if (s != NULL) {
      s = SepDeepCopy(s);
      rec->a->sep_list = SepListCons(s, rec->a->sep_list);
      val = s->d.DATA_AT.right;
      cpa_make_free(val, rec->env);
    } else {
      char *val_name;
      if (name == NULL)
        val_name = clone_str("v");
      else
        val_name = embed_str(fmt, name);
      struct logic_var_info *info = add_anonymous_logic_var(LOGIC_GEN_EXISTS, val_name, &rec->env->persist);
      info->qv = NULL;
      ASSIGN_ATYPE(info->atype, ATZ(&rec->env->persist));
      info->renaming = r ? r : renaming_info_fallback("v");
      if (rec->old)
        info->renaming->is_old = 1;
      val = ExprVal_V_VARI(info->id);
      cpa_add_autogen(val->d.FUNCAPP.id, rec);
      rec->a->sep_list = SepListCons(SepDataAt(addr, TransType(ty), val), rec->a->sep_list);
    }
  } else {
      ExprValFree(addr);
  }
  return ExprValDeepCopy(val);
}

struct ExprVal *cpa_list_at_address(struct ExprVal *addr,
                                    struct ExprVal *len, struct type *ty,
                                    char *name,
                                    struct renaming_info *r,
                                    // len and type can be NULL. but if there ain't already
                                    // a list at addr, len must be given.
                                    struct cpa_param *rec) {
  struct SepList *i;
  for (i = rec->a->sep_list; i != NULL; i = i->next)
    if (i->head->t == T_ARR && ExprValCheckEqual(i->head->d.ARR.addr, addr)) {
      ExprValFree(addr);
      ExprValFree(len);
      return ExprValDeepCopy(i->head->d.ARR.value);
    }
  if (len == NULL)
    failwith("Cannot infer size of array");
  struct Separation *s = (struct Separation *) malloc(sizeof(struct Separation));
  s->t = T_ARR;
  s->d.ARR.addr = addr;
  s->d.ARR.size = len;
  struct logic_var_info *info;
  if (name == NULL)
    info = add_anonymous_logic_var(LOGIC_GEN_EXISTS, clone_str("arr"), &rec->env->persist);
  else
    info = add_anonymous_logic_var(LOGIC_GEN_EXISTS, embed_str("%s_l", name), &rec->env->persist);
  info->renaming = r ? r : renaming_info_fallback("l");
  if (rec->old)
    info->renaming->is_old = 1;
  info->qv = NULL;
  ASSIGN_ATYPE(info->atype, ATZ(&rec->env->persist));
  s->d.ARR.value = ExprVal_V_VARI(info->id);
  s->d.ARR.ty = TransType(ty);
  rec->a->sep_list = SepListCons(s, rec->a->sep_list);
  rec->a->exist_list = ExistListCons(s->d.ARR.value->d.FUNCAPP.id, rec->a->exist_list);
  return ExprValDeepCopy(s->d.ARR.value);
}

struct ExprVal *cpa_value_of(struct RAssertion *ra, struct cpa_param *rec);

struct ExprVal *cpa_address_of(struct RAssertion *ra, struct cpa_param *rec) {
  switch (ra->t) {
  case RA_CONST:
  case RA_LOGICVAR:
  case RA___RETURN:
  case RA_OLD:
  case RA_SIZEOF:
  case RA_ENUMLIT:
  case RA_APP:
  case RA_CAST:
  case RA_BINOP:
  case RA_UNOP:
  case RA_ADDRESS:
  case RA_FIELD_ADDRESS:
  case RA_TIME_COST:
    failwith("Cannot take the address of an rvalue");
  case RA_QFOP:
  case RA_CONN:
  case RA_TRUE:
  case RA_FALSE:
  case RA_EMP:
  case RA_DATA_AT:
  case RA_UNDEF_DATA_AT:
  case RA_ARR:
  case RA_SPEC:
    failwith("Expected expression");
  case RA_SHADOW:{
      assert(0);
      break;
  }
  case RA_PROGVAR:
    if (ra->d.RAPROGVAR.info->category == PROG_LOCAL) {
      if (!cpa_addressable)
        failwith("Address of variable is inaccessible");
      cpa_ensure_local(ra->d.RAPROGVAR.info, rec->a);
    }
    return ExprVal_V_VARI(ra->d.RAPROGVAR.info->address->id);
  case RA_ANN:
    return cpa_address_of(ra->d.RAANN.expr, rec);
  case RA_DEREF:
    return cpa_value_of(ra->d.RADEREF.arg, rec);
  case RA_INDEX:
    return ExprVal_VBOP(Oadd, cpa_value_of(ra->d.RAINDEX.arg, rec),
                        ExprVal_VBOP(Omul, cpa_value_of(ra->d.RAINDEX.pos, rec),  ExprVal_SIZE_OF(TransType(ra->type))));
  case RA_FIELDOF:
    return ExprVal_VFIELD_ADDRESS(cpa_address_of(ra->d.RAFIELDOF.arg, rec),
                                  ra->d.RAFIELDOF.field->id);
  case RA_FIELDOFPTR:
    return ExprVal_VFIELD_ADDRESS(cpa_value_of(ra->d.RAFIELDOFPTR.arg, rec),
                                  ra->d.RAFIELDOFPTR.field->id);
  }
}

struct Cexpr *cexpr_of(struct RAssertion *ra);

// extensively share memory
struct Cexpr *cexpr_of(struct RAssertion *ra) {
  struct Cexpr *ce = (struct Cexpr *)malloc(sizeof(struct Cexpr));
  ce->type = NULL;
  switch (ra->t) {
  case RA_CONST:
    ce->t = C_CONST;
    ce->d.C_CONST.number = ra->d.RACONST.value;
    return ce;
  case RA_PROGVAR:
    ce->t = C_VAR;
    ce->d.C_VAR.id = ra->d.RAPROGVAR.info->id;
    return ce;
  case RA_BINOP:
    ce->t = C_BINOP;
    ce->d.C_BINOP.op = ra->d.RABINOP.op;
    ce->d.C_BINOP.expr1 = cexpr_of(ra->d.RABINOP.left);
    ce->d.C_BINOP.expr2 = cexpr_of(ra->d.RABINOP.right);
    return ce;
  case RA_UNOP:
    ce->t = C_UNOP;
    ce->d.C_UNOP.op = ra->d.RAUNOP.op;
    ce->d.C_UNOP.expr = cexpr_of(ra->d.RAUNOP.arg);
    return ce;
  case RA_CAST:
    ce->t = C_CAST;
    ce->d.C_CAST.expr = cexpr_of(ra->d.RACAST.arg);
    return ce;
  case RA_ANN:
    return cexpr_of(ra->d.RAANN.expr);
  case RA_DEREF:
    ce->t = C_DEREF;
    ce->d.C_DEREF.expr = cexpr_of(ra->d.RADEREF.arg);
    return ce;
  case RA_ADDRESS:
    ce->t = C_ADDROF;
    ce->d.C_ADDROF.expr = cexpr_of(ra->d.RAADDRESS.arg);
    return ce;
  case RA_INDEX:
    ce->t = C_INDEX;
    ce->d.C_INDEX.arr_expr = cexpr_of(ra->d.RAINDEX.arg);
    ce->d.C_INDEX.inner_expr = cexpr_of(ra->d.RAINDEX.pos);
    return ce;
  case RA_FIELDOF:
    switch (ra->d.RAFIELDOF.field->parent->t) {
    case IS_UNION:
      ce->t = C_UNIONFIELD;
      ce->d.C_UNIONFIELD.expr = cexpr_of(ra->d.RAFIELDOF.arg);
      ce->d.C_UNIONFIELD.field_id = ra->d.RAFIELDOF.field->id;
      break;
    case IS_STRUCT:
      ce->t = C_STRUCTFIELD;
      ce->d.C_STRUCTFIELD.expr = cexpr_of(ra->d.RAFIELDOF.arg);
      ce->d.C_STRUCTFIELD.field_id = ra->d.RAFIELDOF.field->id;
    }
    return ce;
  case RA_FIELDOFPTR:
    switch (ra->d.RAFIELDOFPTR.field->parent->t) {
    case IS_UNION:
      ce->t = C_UNIONFIELD;
      ce->d.C_UNIONFIELD.expr = (struct Cexpr *)malloc(sizeof(struct Cexpr));
      ce->d.C_UNIONFIELD.expr->t = C_DEREF;
      ce->d.C_UNIONFIELD.expr->d.C_DEREF.expr = cexpr_of(ra->d.RAFIELDOFPTR.arg);
      ce->d.C_UNIONFIELD.field_id = ra->d.RAFIELDOFPTR.field->id;
      break;
    case IS_STRUCT:
      ce->t = C_STRUCTFIELD;
      ce->d.C_STRUCTFIELD.expr = (struct Cexpr *)malloc(sizeof(struct Cexpr));
      ce->d.C_STRUCTFIELD.expr->t = C_DEREF;
      ce->d.C_STRUCTFIELD.expr->d.C_DEREF.expr = cexpr_of(ra->d.RAFIELDOFPTR.arg);
      ce->d.C_STRUCTFIELD.field_id = ra->d.RAFIELDOFPTR.field->id;
    }
    return ce;
  case RA_FIELD_ADDRESS:
    switch (ra->d.RAFIELD_ADDRESS.field->parent->t) {
    case IS_STRUCT:
      ce->t = C_ADDROF;
      ce->d.C_ADDROF.expr = (struct Cexpr *)malloc(sizeof(struct Cexpr));
      ce->d.C_ADDROF.expr->t = C_UNIONFIELD;
      ce->d.C_ADDROF.expr->d.C_UNIONFIELD.expr = (struct Cexpr *)malloc(sizeof(struct Cexpr));
      ce->d.C_ADDROF.expr->d.C_UNIONFIELD.expr->t = C_DEREF;
      ce->d.C_ADDROF.expr->d.C_UNIONFIELD.expr->d.C_DEREF.expr = cexpr_of(ra->d.RAFIELD_ADDRESS.addr);
      ce->d.C_ADDROF.expr->d.C_UNIONFIELD.field_id = ra->d.RAFIELD_ADDRESS.field->id;
      break;
    case IS_UNION:
      ce->t = C_ADDROF;
      ce->d.C_ADDROF.expr = (struct Cexpr *)malloc(sizeof(struct Cexpr));
      ce->d.C_ADDROF.expr->t = C_STRUCTFIELD;
      ce->d.C_ADDROF.expr->d.C_STRUCTFIELD.expr = (struct Cexpr *)malloc(sizeof(struct Cexpr));
      ce->d.C_ADDROF.expr->d.C_STRUCTFIELD.expr->t = C_DEREF;
      ce->d.C_ADDROF.expr->d.C_STRUCTFIELD.expr->d.C_DEREF.expr = cexpr_of(ra->d.RAFIELD_ADDRESS.addr);
      ce->d.C_ADDROF.expr->d.C_STRUCTFIELD.field_id = ra->d.RAFIELD_ADDRESS.field->id;
    }
    return ce;
  case RA_ENUMLIT: // ok?
    ce->t = C_CONST;
    ce->d.C_CONST.number = ra->d.RAENUMLIT.info->repr;
    return ce;
  case RA_SIZEOF:
    ce->t = C_SIZEOF;
    ce->d.C_SIZEOF.inner_type = TransType(ra->d.RASIZEOF.type);
    return ce;
  case RA_SHADOW: {
    assert(0);
    break;
  }
  case RA_OLD:
  case RA_APP:
  case RA_LOGICVAR:
  case RA___RETURN:
  case RA_QFOP:
  case RA_CONN:
  case RA_EMP:
  case RA_TRUE:
  case RA_FALSE:
  case RA_DATA_AT:
  case RA_UNDEF_DATA_AT:
  case RA_ARR:
  case RA_SPEC:
  case RA_TIME_COST:
    failwith("Expected C expression");
  }
}

struct ExprVal *cpa_list_of(struct RAssertion *ra, struct cpa_param *rec) {
  if (ra->t == RA_LOGICVAR)
    return ExprVal_V_VARI(ra->d.RALOGICVAR.info->id);
  else if (ra->t == RA_APP)
    return cpa_value_of(ra, rec);
  else if (ra->t == RA_ANN)
    return cpa_list_of(ra->d.RAANN.expr, rec);
  struct ExprVal *len = NULL;
  struct type *type = type_unalias(ra->type);
  if (type != NULL && type->t == T_ARRAY)
    len = ExprVal_EZ_VAL(type->d.ARRAY.size);
  struct ExprVal *addr = cpa_value_of(ra, rec);
  struct renaming_info *r = cpa_rename_or_null(addr, rec->env);
  struct type *elt =
    type == NULL ? NULL :
    type->t == T_ARRAY ? type->d.ARRAY.ty :
    type->t == T_PTR ? type->d.PTR.ty : NULL;
  return cpa_list_at_address(addr, len, elt,
                             cpa_name_or_null(addr, rec->env),
                             r ? renaming_info_deref(r) : NULL,
                             rec);
}

struct PolyType *cpa_type_of(struct atype *ty);

struct PolyType *cpa_to_typeapp(struct atype *app) {
  struct PolyTypeList *arg = PolyTypeListNil();
  for (; app->t == AT_APP; app = app->d.APP.tfn)
    arg = PolyTypeListCons(cpa_type_of(app->d.APP.rand), arg);
  while (app->t == AT_TVAR)
    app = app->d.TVAR.link;
  if (atype_is_list(app)) {
    struct PolyType *ret = PolyTypeList(arg->head->data);
    free(arg->head);
    free(arg);
    return ret;
  } else
    return PolyTypeFuncApp(app->d.ATOM.info->id, arg);
}

struct PolyType *cpa_type_of(struct atype *ty) {
  if (ty == NULL) return NULL;
  switch (ty->t) {
  case AT_ARROW:
    return PolyTypeArrow(cpa_type_of(ty->d.ARROW.from), cpa_type_of(ty->d.ARROW.to));
  case AT_ATOM:
    return PolyTypeFuncApp(ty->d.ATOM.info->id, PolyTypeListNil());
  case AT_APP:
    return cpa_to_typeapp(ty);
  case AT_QVAR: {
    assert(0);
    break;
  }
  case AT_TVAR:
    return cpa_type_of(ty->d.TVAR.link);
  }
}

struct atype *cpu_type_of(struct PolyType *ty, struct persistent_env *env) {
  if (ty == NULL)
    return NULL;
  switch (ty->t) {
  case POLY_ARROW:
    return ATArrow(cpu_type_of(ty->d.ARROW.left, env),
                   cpu_type_of(ty->d.ARROW.right, env));
  case POLY_FUNCAPP: {
    struct atype_info *info = find_atype_by_id(ty->d.FUNCAPP.func, env);
    struct atype *ret = ATAtom(info);
    struct PolyTypeListNode *i = ty->d.FUNCAPP.args->head;
    while (i != NULL) {
      ret = ATApp(ret, cpu_type_of(i->data, env));
      i = i->next;
    }
    return ret;
  }
  case POLY_VAR:
    assert(0);
  }
}

struct PolyTypeList *cpa_implicit_of(struct qvar_list *impl) {
  if (impl == NULL)
    return PolyTypeListNil();
  return PolyTypeListCons(cpa_type_of(impl->qv), cpa_implicit_of(impl->next));
}

struct ExprVal *cpa_to_funcapp(struct RAssertion *app, struct cpa_param *rec) {
  struct ExprValList *rand = ExprValListNil();
  for (; app->t == RA_APP; app = app->d.RAAPP.f)
    rand = ExprValListCons(cpa_value_of(app->d.RAAPP.rand, rec), rand);
  if (app->t != RA_LOGICVAR)
    failwith("Nontrivial function is not supported yet");
  if (app->d.RALOGICVAR.info->category == LOGIC_USER_EXISTS)
    rec->a->exist_list = cpa_add_exist(app->d.RALOGICVAR.info->id, rec->a->exist_list);
  return ExprVal_FUNCAPP(app->d.RALOGICVAR.info->id,
                         cpa_implicit_of(app->d.RALOGICVAR.impl),
                         rand);
}

struct ExprVal *cpa_value_of(struct RAssertion *ra, struct cpa_param *rec) {
  switch (ra->t) {
  case RA_QFOP:
  case RA_CONN:
  case RA_TRUE:
  case RA_FALSE:
  case RA_EMP:
  case RA_DATA_AT:
  case RA_UNDEF_DATA_AT:
  case RA_ARR:
  case RA_SPEC:
    failwith("Expected expression");
  case RA_SIZEOF:
    return ExprVal_SIZE_OF(TransType(ra->d.RASIZEOF.type));
  case RA_SHADOW: {
    assert(0);
    break;
  }
  case RA_CONST:
    return ExprVal_EZ_VAL(ra->d.RACONST.value);
  case RA_TIME_COST:
    return ExprVal_TIME_COST();
  case RA_PROGVAR: {
    if (cpa_addressable && ra->d.RAPROGVAR.info->category == PROG_LOCAL)
      cpa_ensure_local(ra->d.RAPROGVAR.info, rec->a);
    if (cpa_addressable || ra->d.RAPROGVAR.info->category != PROG_LOCAL) {
      if (type_unalias(ra->d.RAPROGVAR.info->type)->t != T_ARRAY)
        return cpa_value_at_address(ExprVal_V_VARI(ra->d.RAPROGVAR.info->address->id),
                                    ra->d.RAPROGVAR.info->type, "%s", ra->d.RAPROGVAR.info->name,
                                    renaming_info_var_value(ra->d.RAPROGVAR.info->name, 0, 0),
                                    rec);
      else
        return ExprVal_V_VARI(ra->d.RAPROGVAR.info->address->id);
    } else {
        return ExprVal_V_VARI(ra->d.RAPROGVAR.info->value->id);
    } }
  case RA_BINOP:
    return ExprVal_VBOP(AriBinOpTrans(ra->d.RABINOP.op),
                        cpa_value_of(ra->d.RABINOP.left, rec),
                        cpa_value_of(ra->d.RABINOP.right, rec));
  case RA_UNOP:
    if (ra->d.RAUNOP.op == T_UPLUS)
      return cpa_value_of(ra->d.RAUNOP.arg, rec);
    else
      return ExprVal_VUOP(UserUnaryToInnerUnary(ra->d.RAUNOP.op),
                          cpa_value_of(ra->d.RAUNOP.arg, rec));
  case RA_CAST:
    return cpa_value_of(ra->d.RACAST.arg, rec);
  case RA_ANN:
    return cpa_value_of(ra->d.RAANN.expr, rec);
  case RA_LOGICVAR:
  case RA_APP:
    return cpa_to_funcapp(ra, rec);
  case RA_DEREF: {
    struct ExprVal *addr;
    addr = cpa_value_of(ra->d.RADEREF.arg, rec);
    struct renaming_info *r = cpa_rename_or_null(addr, rec->env);
    return cpa_value_at_address(addr, ra->type, "%s_v",
                                cpa_name_or_null(addr, rec->env),
                                r ? renaming_info_deref(r) : NULL,
                                rec); }
  case RA_ADDRESS:
    return cpa_address_of(ra->d.RAADDRESS.arg, rec);
  case RA_INDEX:
    return ExprVal_LINDEX(cpa_list_of(ra->d.RAINDEX.arg, rec),
                          cpa_value_of(ra->d.RAINDEX.pos, rec));
  case RA_FIELDOF: {
    struct ExprVal *addr = cpa_address_of(ra->d.RAFIELDOF.arg, rec);
    char *fmt;
    if (addr->t == FUNCAPP && addr->d.FUNCAPP.args->head == NULL)
      fmt = embed_str("%%s_%s", ra->d.RAFIELDOF.field->name);
    else
      fmt = NULL;
    struct renaming_info *r = cpa_rename_or_null(addr, rec->env);
    struct ExprVal *res = cpa_value_at_address(ExprVal_VFIELD_ADDRESS(addr, ra->d.RAFIELDOF.field->id),
                                               ra->d.RAFIELDOF.field->type, fmt,
                                               cpa_name_or_null(addr, rec->env),
                                               r ? renaming_info_field(r, ra->d.RAFIELDOF.field->name) : NULL,
                                               rec);
    free(fmt);
    return res; }
  case RA_FIELDOFPTR: {
    struct ExprVal *addr = cpa_value_of(ra->d.RAFIELDOFPTR.arg, rec);
    char *fmt;
    if (addr->t == FUNCAPP && addr->d.FUNCAPP.args->head == NULL)
      fmt = embed_str("%%s_%s", ra->d.RAFIELDOFPTR.field->name);
    else
      fmt = NULL;
    struct renaming_info *r = cpa_rename_or_null(addr, rec->env);
    struct ExprVal *res = cpa_value_at_address(ExprVal_VFIELD_ADDRESS(addr, ra->d.RAFIELDOFPTR.field->id),
                                               ra->d.RAFIELDOFPTR.field->type, fmt,
                                               cpa_name_or_null(addr, rec->env),
                                               r ? renaming_info_field(r, ra->d.RAFIELDOFPTR.field->name) : NULL,
                                               rec);
    free(fmt);
    return res; }
  case RA_FIELD_ADDRESS:
    return ExprVal_VFIELD_ADDRESS(cpa_value_of(ra->d.RAFIELD_ADDRESS.addr, rec),
                                  ra->d.RAFIELD_ADDRESS.field->id);
  case RA_ENUMLIT:
    return ExprVal_EZ_VAL(ra->d.RAENUMLIT.info->repr);
  case RA___RETURN:
    if (rec->retval == NULL)
      failwith("`__return' not in function specification");
    if (rec->retval->v == NULL) {
      struct logic_var_info * tmp = add_anonymous_logic_var(LOGIC_GEN_EXISTS, clone_str("retval"), &rec->env->persist);
      tmp->qv = NULL;
      ASSIGN_ATYPE(tmp->atype, ATZ(&rec->env->persist));
      tmp->renaming = renaming_info_return_value();
      rec->retval->v = ExprVal_V_VARI(tmp->id);
    }
    rec->retval->occur = 1;
    return ExprValDeepCopy(rec->retval->v);
  case RA_OLD: {
    struct ExprExecRetValue *ret;
    struct AsrtList *old = find_assertion(ra->d.RAOLD.mark, &rec->env->ephemer);
    if (old == NULL)
      failwith("No such assertion `%s' in scope", ra->d.RAOLD.mark);
    ret = AsrtListExprExecRightValue(AsrtListDeepCopy(old), cexpr_of(ra->d.RAOLD.arg), rec->env)->ret_value;
    if (ret == NULL)
      failwith("Old value at `%s' error", ra->d.RAOLD.mark);
    if (ret->next != NULL)
      failwith("Old value at `%s' is not determined", ra->d.RAOLD.mark);
    rec->a->prop_list = PropListLink(rec->a->prop_list, ret->constraits);
    struct IntListNode *l;
    for (l = ret->introed_vars->head; l != NULL; l = l->next)
      rec->a->exist_list = ExistListCons(l->data, rec->a->exist_list);
    if (rec->is_post)
      cpa_make_free(ret->val, rec->env);
    return ret->val; }
  }
}

struct Proposition *cpa_to_pure(struct RAssertion *ra, struct cpa_param *rec) {
  struct Proposition *res;
  switch (ra->t) {
  case RA_CONST:
  case RA_PROGVAR:
  case RA_TIME_COST:
  case RA_CAST:
  case RA_DEREF:
  case RA_ADDRESS:
  case RA_INDEX:
  case RA_FIELDOF:
  case RA_FIELDOFPTR:
  case RA_ENUMLIT:
  case RA___RETURN:
  case RA_SIZEOF:
  case RA_OLD:
  case RA_SHADOW:
  case RA_FIELD_ADDRESS:
  case RA_ANN:
    failwith("Expected proposition");
  case RA_BINOP:
    if (ra->d.RABINOP.op == T_AND)
      return PropBinary(PROP_AND,
                        cpa_to_pure(ra->d.RABINOP.left, rec),
                        cpa_to_pure(ra->d.RABINOP.right, rec));
    else if (ra->d.RABINOP.op == T_OR)
      return PropBinary(PROP_OR,
                        cpa_to_pure(ra->d.RABINOP.left, rec),
                        cpa_to_pure(ra->d.RABINOP.right, rec));
    else if (cpa_is_relop(ra->d.RABINOP.op))
      return PropCompare(BinCompareOpToPropComp(ra->d.RABINOP.op),
                         cpa_value_of(ra->d.RABINOP.left, rec),
                         cpa_value_of(ra->d.RABINOP.right, rec));
    else
      failwith("Expected proposition");
  case RA_CONN:
    if (ra->d.RACONN.op == A_IMPLY)
      return PropBinary(PROP_IMPLY,
                        cpa_to_pure(ra->d.RACONN.left, rec),
                        cpa_to_pure(ra->d.RACONN.right, rec));
    else
      return PropBinary(PROP_IFF,
                        cpa_to_pure(ra->d.RACONN.left, rec),
                        cpa_to_pure(ra->d.RACONN.right, rec));
  case RA_UNOP:
    if (ra->d.RAUNOP.op == T_NOTBOOL)
      return PropUnary(PROP_NOT, cpa_to_pure(ra->d.RAUNOP.arg, rec));
    else
      failwith("Expected proposition");
  case RA_QFOP:
    res = (struct Proposition *) malloc(sizeof(struct Proposition));
    res->t = T_PROP_QUANTIFIER;
    if (ra->d.RAQFOP.op == A_FORALL)
      res->d.QUANTIFIER.op = PROP_FORALL;
    else
      res->d.QUANTIFIER.op = PROP_EXISTS;
    ra->d.RAQFOP.abs.info->category = LOGIC_FORALL;
    // it's not a toplevel exist
    res->d.QUANTIFIER.ident = ra->d.RAQFOP.abs.info->id;
    res->d.QUANTIFIER.prop = cpa_to_pure(ra->d.RAQFOP.arg, rec);
    return res;
  case RA_TRUE:
    return PropTrue();
  case RA_FALSE:
    return PropFalse();
  case RA_APP:
  case RA_LOGICVAR:
  case RA_DATA_AT:
  case RA_UNDEF_DATA_AT:
  case RA_EMP:
  case RA_ARR:
  case RA_SPEC:
    failwith("Expected memory-unrelated proposition");
  }
}

void cpa_to_pred(struct RAssertion *app, struct cpa_param *rec) {
  struct ExprValList *rand = ExprValListNil();
  for (; app->t == RA_APP; app = app->d.RAAPP.f)
    rand = ExprValListCons(cpa_value_of(app->d.RAAPP.rand, rec), rand);
  if (app->t != RA_LOGICVAR)
    failwith("Nontrivial separation predicate is not supported yet");
  if (app->d.RALOGICVAR.info->category == LOGIC_USER_EXISTS)
    rec->a->exist_list = cpa_add_exist(app->d.RALOGICVAR.info->id, rec->a->exist_list);
  struct PolyTypeList *implicit = cpa_implicit_of(app->d.RALOGICVAR.impl);
  struct atype *i = app->d.RALOGICVAR.info->atype;
  for (; i->t == AT_ARROW; i = i->d.ARROW.to)
    ;
  if (atype_is_prop(i))
    rec->a->prop_list = PropListCons(PropOther(app->d.RALOGICVAR.info->id, implicit, rand), rec->a->prop_list);
  else
    rec->a->sep_list = SepListCons(SepOther(app->d.RALOGICVAR.info->id, implicit, rand), rec->a->sep_list);
}

struct SepList *sep_cons_unique(struct Separation *sep, struct SepList *l) {
  struct SepList * i;
  for (i = l; i != NULL; i = i->next)
    if (SeparationCheckEqual(sep, i->head)) {
      SepFree(sep);
      return l;
    }
  l = SepListCons(sep, l);
  return l;
}

void cpa_to_heap(struct RAssertion *ra, struct cpa_param *rec) {
  enum PropCompOp bin_op;
  struct Assertion *a = rec->a;
  switch (ra->t) {
  case RA_BINOP:
    if (cpa_is_relop(ra->d.RABINOP.op)) {
      bin_op = BinCompareOpToPropComp(ra->d.RABINOP.op);
      rec->a->prop_list = PropListCons(PropCompare(bin_op,
                                              cpa_value_of(ra->d.RABINOP.left, rec),
                                              cpa_value_of(ra->d.RABINOP.right, rec)),
                                  rec->a->prop_list);
      break;
    } else if (ra->d.RABINOP.op == T_AND || ra->d.RABINOP.op == T_MUL) {
      cpa_to_heap(ra->d.RABINOP.left, rec);
      cpa_to_heap(ra->d.RABINOP.right, rec);
      break;
    } else
      failwith("Expected proposition");
  case RA_ARR: {
    struct Separation *sep = SepArr(cpa_value_of(ra->d.RAARR.addr, rec),
                                    TransType(ra->d.RAARR.ty),
                                    cpa_value_of(ra->d.RAARR.list, rec),
                                    cpa_value_of(ra->d.RAARR.len, rec));
    a->sep_list = sep_cons_unique(sep, a->sep_list);
    break; }
  case RA_DATA_AT: {
    struct Separation *sep = SepDataAt(cpa_value_of(ra->d.RADATA_AT.addr, rec),
                                       TransType(ra->d.RADATA_AT.ty),
                                       cpa_value_of(ra->d.RADATA_AT.val, rec));
    a->sep_list = sep_cons_unique(sep, a->sep_list);
    break; }
  case RA_UNDEF_DATA_AT: {
    struct Separation *sep = SepUndefDataAt(cpa_value_of(ra->d.RAUNDEF_DATA_AT.addr, rec),
                                            TransType(ra->d.RAUNDEF_DATA_AT.ty));
    a->sep_list = sep_cons_unique(sep, a->sep_list);
    break; }
  case RA_QFOP:
    assert(ra->d.RAQFOP.op == A_FORALL)
    a->prop_list = PropListCons(cpa_to_pure(ra, rec), a->prop_list);
    break;
  case RA_UNOP:
    if (ra->d.RAUNOP.op == T_NOTBOOL)
      a->prop_list = PropListCons(cpa_to_pure(ra, rec), a->prop_list);
    else
      failwith("Expected proposition");
    break;
  case RA_EMP:
  case RA_TRUE:
    break;
  case RA_FALSE:
    a->prop_list = PropListCons(PropFalse(), a->prop_list);
    break;
  case RA_CONN: {
    assert(0);
    break;
  }
  case RA_SPEC: {
    struct FPSpec *fs;
    fs = (struct FPSpec *) malloc(sizeof(struct FPSpec));
    fs->func_info = ra->d.RASPEC.info;
    fs->fp_addr = cpa_value_of(ra->d.RASPEC.f, rec);
    a->fp_spec_list = FPSpecListCons(fs, a->fp_spec_list);
    break; }
  case RA_ANN:
    cpa_to_heap(ra->d.RAANN.expr, rec);
    break;
  case RA_LOGICVAR:
  case RA_APP:
    cpa_to_pred(ra, rec);
    break;
  case RA_PROGVAR:
  case RA_CONST:
  case RA_CAST:
  case RA_DEREF:
  case RA_ADDRESS:
  case RA_INDEX:
  case RA_FIELDOF:
  case RA_FIELDOFPTR:
  case RA_ENUMLIT:
  case RA___RETURN:
  case RA_SIZEOF:
  case RA_OLD:
  case RA_SHADOW:
  case RA_FIELD_ADDRESS:
  case RA_TIME_COST:
    failwith("Expected proposition");
  }
}

/* postprocess */

struct ExistList *cpa_extract_free(struct ExistList **el,
                                   struct persistent_env *env) {
  if (*el == NULL)
    return NULL;
  struct logic_var_info *info = find_logic_var_by_id((*el)->id, env);
  if (info->category == LOGIC_USER_EXISTS ||
      info->category == LOGIC_GEN_EXISTS)
    return cpa_extract_free(&(*el)->next, env);
  else {
    struct ExistList *f = *el;
    *el = f->next;
    f->next = cpa_extract_free(el, env);
    return f;
  }
}

struct ExistList *cpa_remove_free(struct ExistList *el,
                                  struct persistent_env *env) {
  if (el == NULL)
    return NULL;
  struct logic_var_info *info = find_logic_var_by_id(el->id, env);
  if (info->category == LOGIC_FREE)
    return cpa_remove_free(el->next, env);
  else {
    el->next = cpa_remove_free(el->next, env);
    return el;
  }
}

void cpa_ensure_no_escape(struct ExprVal *e, struct environment *env) {
  switch (e->t) {
  case TIME_COST:
  case EZ_VAL:
  case SIZE_OF:
    break;
  case LINDEX:
    cpa_ensure_no_escape(e->d.LINDEX.list, env);
    cpa_ensure_no_escape(e->d.LINDEX.index, env);
    break;
  case VFIELD_ADDRESS:
    cpa_ensure_no_escape(e->d.VFIELD_ADDRESS.expr, env);
    break;
  case VUOP:
    cpa_ensure_no_escape(e->d.VUOP.expr, env);
    break;
  case VBOP:
    cpa_ensure_no_escape(e->d.VBOP.expr1, env);
    cpa_ensure_no_escape(e->d.VBOP.expr2, env);
    break;
  case FUNCAPP: {
    struct logic_var_info *info = find_logic_var_by_id(e->d.FUNCAPP.id, &env->persist);
    if (info != NULL && info->category == LOGIC_FORALL)
      failwith("Expected memory-unrelated proposition");
    struct ExprValListNode *l;
    for (l = e->d.FUNCAPP.args->head; l != NULL; l = l->next)
      cpa_ensure_no_escape(l->data, env);
    break; }
  }
}

void cpa_sanity_check(struct Assertion *a, struct environment *env) {
  struct SepList *i;
  struct Separation *s;
  for (i = a->sep_list; i != NULL; i = i->next) {
    s = i->head;
    switch (s->t) {
    case T_ARR:
      cpa_ensure_no_escape(s->d.ARR.addr, env);
      break;
    case T_DATA_AT:
      cpa_ensure_no_escape(s->d.DATA_AT.left, env);
      cpa_ensure_no_escape(s->d.DATA_AT.right, env);
      break;
    case T_UNDEF_DATA_AT:
      cpa_ensure_no_escape(s->d.UNDEF_DATA_AT.left, env);
      break;
    case T_OTHER: {
      struct ExprValListNode *l;
      for (l = s->d.OTHER.exprs->head; l != NULL; l = l->next)
        cpa_ensure_no_escape(l->data, env);
      break; }
    }
  }
}

#define DEFINE_REVERSE(fname, tname) \
  struct tname *fname##_aux(struct tname *l, struct tname *acc) {       \
    if (l == NULL)                                                      \
      return acc;                                                       \
    struct tname *tl = l->next;                                         \
    l->next = acc;                                                      \
    return fname##_aux(tl, l);                                          \
  }                                                                     \
  struct tname *fname(struct tname *l) {                                \
    return fname##_aux(l, NULL);                                        \
  }

DEFINE_REVERSE(cpa_reverse_exist, ExistList);
DEFINE_REVERSE(cpa_reverse_prop, PropList);
DEFINE_REVERSE(cpa_reverse_sep, SepList);

#undef DEFINE_REVERSE

void cpa_adjust_order(struct Assertion *a) {
  a->exist_list = cpa_reverse_exist(a->exist_list);
  a->prop_list = cpa_reverse_prop(a->prop_list);
  a->sep_list = cpa_reverse_sep(a->sep_list);
}

void cpa_collect_triv_eq(struct cpa_param *rec) {
  struct PropList *i;
  for (i = rec->a->prop_list; i != NULL; i = i->next) {
    struct Proposition *p = i->head;
    if (p->t == T_PROP_COMPARE &&
        p->d.COMPARE.op == PROP_EQ) {
      struct ExprVal *e1 = p->d.COMPARE.expr1;
      struct ExprVal *e2 = p->d.COMPARE.expr2;
      if (e1->t == FUNCAPP && e2->t == FUNCAPP &&
          e1->d.FUNCAPP.args->head == NULL &&
          e2->d.FUNCAPP.args->head == NULL) {
        void *v1 = hashtbl_findref(&rec->autogen, cast_int(e1->d.FUNCAPP.id));
        void *v2 = hashtbl_findref(&rec->autogen, cast_int(e2->d.FUNCAPP.id));
        if (v1 && !v2) {
          *(struct ExprVal **)v1 = e2;
        } else if (v2 && !v1) {
          *(struct ExprVal **)v2 = e1;
        }
      }
    }
  }
}

struct Assertion *cpa_cap_a;
struct persistent_env *cpa_cap_per;
void cpa_subst_triv_eq_rec(void *_id, void *_var) {
unsigned int id = cast_void(_id);
  struct ExprVal *var = _var;
  if (var != NULL) {
    cpa_cap_a->exist_list = ExistListRemove(id, cpa_cap_a->exist_list);
    remove_logic_var_by_id(id, cpa_cap_per);
    struct ExprVal *tmp = ExprVal_V_VARI(id);
    cpa_cap_a->prop_list = PropListSubst(cpa_cap_a->prop_list, tmp, var);
    cpa_cap_a->sep_list = SepListSubst(cpa_cap_a->sep_list, tmp, var);
    ExprValFree(tmp);
  }
}

void cpa_subst_triv_eq(struct cpa_param *rec) {
  cpa_cap_a = rec->a;
  cpa_cap_per = &rec->env->persist;
  hashtbl_iter(&rec->autogen, cpa_subst_triv_eq_rec);
}

void cpa_remove_triv_eq(struct Assertion *a) {
  struct PropList **i = &a->prop_list;
  while (*i != NULL) {
    struct Proposition *p = (*i)->head;
    if (p->t == T_PROP_COMPARE &&
        p->d.COMPARE.op == PROP_EQ) {
      struct ExprVal *e1 = p->d.COMPARE.expr1;
      struct ExprVal *e2 = p->d.COMPARE.expr2;
      if (ExprValCheckEqual(e1, e2)) {
        struct PropList *t = *i;
        PropFree(t->head);
        *i = t->next;
        free(t);
        continue;
      }
    }
    i = &(*i)->next;
  }
}

/* postprocess end */

struct Assertion *cpa_single_wrap(struct RAssertion *ra,
                                  struct Assertion *ctx, struct Assertion *a,
                                  struct __RETURN_OCCUR *retval,
                                  int old, int is_post,
                                  struct environment *env) {
  struct cpa_param p;
  p.a = a;
  p.ctx = ctx;
  p.env = env;
  p.retval = retval;
  p.old = old;
  p.is_post = is_post;
  init_hashtbl(&p.autogen, hash_uint, uint_equal);
  cpa_to_heap(ra, &p);
  if (retval != NULL && retval->occur)
    a->exist_list = ExistListCons(retval->v->d.FUNCAPP.id, a->exist_list);
  cpa_sanity_check(a, env);
  cpa_adjust_order(a);
  cpa_collect_triv_eq(&p);
  cpa_subst_triv_eq(&p);
  cpa_remove_triv_eq(a);
  hashtbl_clear(&p.autogen);
  return a;
}

struct AsrtList *cpa_multi_wrap(struct RAssertion *ra,
                                struct Assertion *ctx,
                                int old,
                                struct environment *env) {
  if (ra->t != RA_BINOP || ra->d.RABINOP.op != T_OR) {
    struct Assertion *a = CreateAsrt();
    return AsrtListCons(cpa_single_wrap(ra, ctx, a, NULL, old, 0, env), NULL);
  } else {
    return AsrtListLink(cpa_multi_wrap(ra->d.RABINOP.left, ctx, old, env),
                        cpa_multi_wrap(ra->d.RABINOP.right, ctx, old, env));
  }
}

struct AsrtList *cpa_worlds_of_heap(struct RAssertion *ra,
                                    struct prog_var_info_list *param,
                                    struct __RETURN_OCCUR *__return,
                                    int old, int is_post,
                                    struct environment *env) {
  if (ra->t == RA_BINOP && ra->d.RABINOP.op == T_OR) {
    struct AsrtList *l;
    struct AsrtList *r;
    r = cpa_worlds_of_heap(ra->d.RABINOP.left, param, __return, old, is_post, env);
    l = cpa_worlds_of_heap(ra->d.RABINOP.right, param,  __return, old, is_post, env);
    return AsrtListLink(l, r);
  } else {
    struct Assertion *single = CreateAsrt();
    for (; param != NULL; param = param->tail) {
      struct ExprVal *e = ExprVal_V_VARI(param->head->value->id);
      LocalInsert(param->head->id, e, single->local_list);
      ExprValFree(e);
    }
    if (__return != NULL)
      __return->occur = 0;

    cpa_single_wrap(ra, single, single, __return, old, is_post, env);

    return AsrtListCons(single, AsrtListNil());
  }
}

struct AsrtList *cpa_comment(struct RAssertion *ra, struct environment *env) {
  cpa_addressable = 1;
  LocalDeepCopy = (void*(*)(void *)) LocalListDeepCopy;
  ra = cpa_dnf(ra);
  struct AsrtList *post = cpa_worlds_of_heap(ra, NULL, NULL, 0, 0, env);
  struct AsrtList *pre = cpa_worlds_of_heap(ra, NULL, NULL, 1, 0, env);
  add_twin_assertion(post, pre, &env->persist);
  free_ra(ra);
  return post;
}

struct func_spec *cpa_local_spec(struct ExistList *with,
                                 struct RAssertion *pre, struct RAssertion *post,
                                 struct environment *env) {
  cpa_addressable = 1;
  LocalDeepCopy = (void*(*)(void *)) LocalListDeepCopy;

  struct Assertion *pre_a = CreateAsrt();
  struct Assertion *pre_old = CreateAsrt();
  pre = cpa_dnf(pre);
  post = cpa_dnf(post);
  if (pre->t == RA_BINOP && pre->d.RABINOP.op == T_OR)
    failwith("Multiple cases inside pre- or post-condition");

  cpa_single_wrap(pre, pre_a, pre_a, NULL, 0, 0, env);
  struct AsrtList *post_a = cpa_multi_wrap(post, pre_a, 0, env);
  cpa_single_wrap(pre, pre_old, pre_old, NULL, 1, 0, env);
  struct AsrtList *post_old = cpa_multi_wrap(post, pre_old, 1, env);

  struct func_spec *fsp = (struct func_spec *)malloc(sizeof(struct func_spec));
  fsp->name = NULL; fsp->derived_by = NULL; fsp->witht = NULL; fsp->qv = NULL; fsp->__return = NULL;
  fsp->next = NULL;
  fsp->pre = AsrtListCons(pre_a, NULL);
  fsp->post = post_a;
  fsp->with = ExistListLink(cpa_extract_free(&pre_a->exist_list, &env->persist), with);

  add_twin_assertion(fsp->pre, AsrtListCons(pre_old, NULL), &env->persist);
  add_twin_assertion(fsp->post, post_old, &env->persist);

  return fsp;
}

char *cpa_fresh_with_from_rec(char *fmt, struct ephemeral_env *env, unsigned int suffix) {
  char *fresh = embed_int(fmt, suffix);
  if (find_var_like_by_name(fresh, env) == NULL)
    return fresh;
  else {
    free(fresh);
    return cpa_fresh_with_from_rec(fmt, env, suffix + 1);
  }
}

char *cpa_fresh_with_from(char *name, struct ephemeral_env *env) {
  if (find_var_like_by_name(name, env) == NULL)
    return name;
  else {
    char *fmt = embed_str("%s_%%u", name);
    free(name);
    char *ret = cpa_fresh_with_from_rec(fmt, env, 0);
    free(fmt);
    return ret;
  }
}

struct func_spec *cpa_spec(struct ExistList *witht,
                           struct ExistList *with,
                           struct RAssertion *pre,
                           struct RAssertion *post,
                           struct prog_var_info_list *param,
                           struct environment *env) {
  struct func_spec *spec;
  spec = (struct func_spec *)malloc(sizeof(struct func_spec));

  cpa_addressable = 0;
  LocalDeepCopy = (void*(*)(void *)) LocalListDeepCopy;

  struct hashtbl map;
  init_hashtbl(&map, hash_uint, uint_equal);
  hashtbl_clear(&map);

  pre = cpa_dnf(pre);
  post = cpa_dnf(post);

  spec->witht = witht;
  spec->with = with;
  struct prog_var_info_list *i;
  for (i = param; i != NULL; i = i->tail)
    spec->with = ExistListCons(i->head->value->id, spec->with);
  spec->pre = cpa_worlds_of_heap(pre, param, NULL, 0, 0, env);
  add_assertion("pre", ToAddressable(spec->pre, env), &env->ephemer);
  struct __RETURN_OCCUR ro;
  ro.v = NULL;
  ro.occur = 0;
  spec->post = cpa_worlds_of_heap(post, NULL, &ro, 0, 1, env);
  spec->__return = ro.v;
  spec->qv = NULL;
  spec->name = NULL;
  spec->derived_by = NULL;
  spec->with = ExistListLink(spec->with, cpa_extract_free(&spec->pre->head->exist_list, &env->persist));
  struct AsrtList *j;
  for (j = spec->pre->next; j != NULL; j = j->next)
    j->head->exist_list = cpa_remove_free(j->head->exist_list, &env->persist);
    
  free_ra(pre);
  free_ra(post);
  return spec;
}

struct virt_arg_list *cpa_virt_arg_rec(struct pp_varg_list *l, struct Assertion *ctx,
                                       struct environment *env) {
  if (l == NULL)
    return NULL;
  struct virt_arg_list *res = (struct virt_arg_list *)malloc(sizeof(struct virt_arg_list));
  res->name = l->name;
  ASSIGN_ATYPE(res->type, l->type);

  struct cpa_param p;
  p.a = ctx;
  p.ctx = ctx;
  p.env = env;
  p.retval = NULL;
  init_hashtbl(&p.autogen, hash_uint, uint_equal);
  res->val = cpa_value_of(l->val, &p);
  hashtbl_clear(&p.autogen);

  res->next = cpa_virt_arg_rec(l->next, ctx, env);
  return res;
}

struct virt_arg *cpa_virt_arg(struct pp_varg_list *l, struct environment *env) {
  cpa_addressable = 1;
  LocalDeepCopy = (void*(*)(void *)) LocalListDeepCopy;

  struct Assertion *ctx = CreateAsrt();
  struct virt_arg *res = (struct virt_arg *)malloc(sizeof(struct virt_arg));
  res->arg = cpa_virt_arg_rec(l, ctx, env);
  res->ctx = (struct func_spec *)malloc(sizeof(struct func_spec));
  res->ctx->__return = NULL;
  res->ctx->witht = NULL;
  res->ctx->qv = NULL;
  res->ctx->with = ctx->exist_list;
  ctx->exist_list = NULL;
  res->ctx->pre = AsrtListCons(ctx, NULL);
  res->ctx->post = AsrtListCons(AsrtDeepCopy(ctx), NULL);
  res->ctx->name = NULL;
  res->ctx->derived_by = NULL;
  struct ExistList *i;
  for (i = res->ctx->with; i != NULL; i = i->next) {
    find_logic_var_by_id(i->id, &env->persist)->category = LOGIC_FREE;
  }
  return res;
}

void cpa_expr(struct pp_expr *e, struct environment *env) {
  switch (e->t) {
  case PP_CONST:
  case PP_STRING:
  case PP_VAR:
  case PP_ENUMLIT:
  case PP_SIZEOFTYPE:
    break;
  case PP_BINOP:
    cpa_expr(e->d.BINOP.left, env);
    cpa_expr(e->d.BINOP.right, env);
    break;
  case PP_UNOP:
    cpa_expr(e->d.UNOP.arg, env);
    break;
  case PP_CAST:
    cpa_expr(e->d.CAST.arg, env);
    break;
  case PP_CALL:
    cpa_expr(e->d.CALL.func, env);
    {
      struct pp_expr_list *i;
      for (i = e->d.CALL.args; i != NULL; i = i->tail)
        cpa_expr(i->head, env);
    }
    if (e->d.CALL.vargs != NULL) {
      e->d.CALL.vargs->after = cpa_virt_arg(e->d.CALL.vargs->pre, env);
      e->d.CALL.vargs->after->spec_name = e->d.CALL.vargs->spec_name;
      e->d.CALL.vargs->after->type_arg = e->d.CALL.vargs->type;
    }
    break;
  case PP_DEREF:
    cpa_expr(e->d.DEREF.arg, env);
    break;
  case PP_ADDRESS:
    cpa_expr(e->d.ADDRESS.arg, env);
    break;
  case PP_INDEX:
    cpa_expr(e->d.INDEX.arg, env);
    cpa_expr(e->d.INDEX.pos, env);
    break;
  case PP_FIELDOF:
    cpa_expr(e->d.FIELDOF.arg, env);
    break;
  case PP_FIELDOFPTR:
    cpa_expr(e->d.FIELDOFPTR.arg, env);
    break;
  case PP_CONDITION:
    cpa_expr(e->d.CONDITION.cond, env);
    cpa_expr(e->d.CONDITION.btrue, env);
    cpa_expr(e->d.CONDITION.bfalse, env);
    break;
  }
}

void cpa_rename_exprval(struct ExprVal *e, struct hashtbl *rename);

void cpa_rename_exprvallist(struct ExprValListNode *l, struct hashtbl *rename) {
  if (l == NULL)
    return;
  cpa_rename_exprval(l->data, rename);
  cpa_rename_exprvallist(l->next, rename);
}

void cpa_rename_exprval(struct ExprVal *e, struct hashtbl *rename) {
  switch (e->t) {
  case EZ_VAL:
  case TIME_COST:
  case SIZE_OF:
    break;
  case VFIELD_ADDRESS:
    cpa_rename_exprval(e->d.VFIELD_ADDRESS.expr, rename);
    break;
  case VUOP:
    cpa_rename_exprval(e->d.VUOP.expr, rename);
    break;
  case VBOP:
    cpa_rename_exprval(e->d.VBOP.expr1, rename);
    cpa_rename_exprval(e->d.VBOP.expr2, rename);
    break;
  case LINDEX:
    cpa_rename_exprval(e->d.LINDEX.list, rename);
    cpa_rename_exprval(e->d.LINDEX.index, rename);
    break;
  case FUNCAPP: {
    int v;
    int new_id = cast_void(hashtbl_find(rename, cast_int(e->d.FUNCAPP.id), &v));
    if (v)
      e->d.FUNCAPP.id = new_id;
    cpa_rename_exprvallist(e->d.FUNCAPP.args->head, rename);
    break; }
  }
}

void cpa_rename_prop(struct Proposition *p, struct hashtbl *rename) {
  switch (p->t) {
  case T_PROP_TRUE:
  case T_PROP_FALSE:
    break;
  case T_PROP_UNARY:
    cpa_rename_prop(p->d.UNARY.prop, rename);
    break;
  case T_PROP_BINARY:
    cpa_rename_prop(p->d.BINARY.prop1, rename);
    cpa_rename_prop(p->d.BINARY.prop2, rename);
    break;
  case T_PROP_PTR:
    cpa_rename_exprval(p->d.PTR.expr, rename);
    break;
  case T_PROP_COMPARE:
    cpa_rename_exprval(p->d.COMPARE.expr1, rename);
    cpa_rename_exprval(p->d.COMPARE.expr2, rename);
    break;
  case T_PROP_QUANTIFIER:
    cpa_rename_prop(p->d.QUANTIFIER.prop, rename);
    break;
  case T_PROP_OTHER: {
    int v;
    int new_id = cast_void(hashtbl_find(rename, cast_int(p->d.OTHER.predicate), &v));
    if (v)
      p->d.OTHER.predicate = new_id;
    cpa_rename_exprvallist(p->d.OTHER.args->head, rename);
    break;
  }
  }
}

void cpa_rename_sep(struct Separation *s, struct hashtbl *rename) {
  switch (s->t) {
  case T_DATA_AT:
    cpa_rename_exprval(s->d.DATA_AT.left, rename);
    cpa_rename_exprval(s->d.DATA_AT.right, rename);
    break;
  case T_UNDEF_DATA_AT:
    cpa_rename_exprval(s->d.UNDEF_DATA_AT.left, rename);
    break;
  case T_ARR:
    cpa_rename_exprval(s->d.ARR.addr, rename);
    cpa_rename_exprval(s->d.ARR.size, rename);
    cpa_rename_exprval(s->d.ARR.value, rename);
    break;
  case T_OTHER: {
    int v;
    int new_id = cast_void(hashtbl_find(rename, cast_int(s->d.OTHER.sep_id), &v));
    if (v)
      s->d.OTHER.sep_id = new_id;
    cpa_rename_exprvallist(s->d.OTHER.exprs->head, rename);
    break;
  }
  }
}

void cpa_do_rename(struct Assertion *a, struct hashtbl *rename) {
  {
    struct PropList *i;
    for (i = a->prop_list; i != NULL; i = i->next)
      cpa_rename_prop(i->head, rename);
  }
  {
    struct SepList *i;
    for (i = a->sep_list; i != NULL; i = i->next)
      cpa_rename_sep(i->head, rename);
  }
  {
    struct LocalLinkedHashMap * local = a->local_list;
    for (struct LocalLinkedHashMapNode * node = local->head; node != NULL; node = node->next) {
      cpa_rename_exprval(node->value, rename);
    }
  }
}

unsigned int cpa_rename_logic_var(unsigned int id, struct persistent_env *env) {
  struct logic_var_info *old = find_logic_var_by_id(id, env);
  struct logic_var_info *new = add_anonymous_logic_var(LOGIC_FREE, clone_str(old->name), env);
  new->qv = clone_qvar_list(old->qv);
  new->renaming = renaming_info_deep_copy(old->renaming);
  ASSIGN_ATYPE(new->atype, old->atype);
  return new->id;
}

void cpa_rename_exists(struct Assertion *a, struct hashtbl *mapping, struct persistent_env *env) {
  struct ExistList *i;
  for (i = a->exist_list; i != NULL; i = i->next) {
    // exclude retval
    int v;
    unsigned int new_id = cast_void(hashtbl_find(mapping, cast_int(i->id), &v));
    if (!v) {
      new_id = cpa_rename_logic_var(i->id, env);
      hashtbl_add(mapping, cast_int(i->id), cast_int(new_id));
    }
    i->id = new_id;
  }
  cpa_do_rename(a, mapping);
}

void cpa_rename_func_spec(struct func_spec *spec, struct hashtbl *mapping,
                          struct persistent_env *env) {
  struct ExistList *i;
  for (i = spec->with; i != NULL; i = i->next) {
    int valid;
    unsigned int new_id = cast_void(hashtbl_find(mapping, cast_int(i->id), &valid));
    if (!valid) {
      new_id = cpa_rename_logic_var(i->id, env);
      hashtbl_add(mapping, cast_int(i->id), cast_int(new_id));
    }
    i->id = new_id;
  }
  if (spec->__return != NULL) {
    unsigned int id = spec->__return->d.FUNCAPP.id;
    int valid;
    unsigned int new_id = cast_void(hashtbl_find(mapping, cast_int(id), &valid));
    if (!valid) {
      new_id = cpa_rename_logic_var(id, env);
      hashtbl_add(mapping, cast_int(id), cast_int(new_id));
    }
    spec->__return->d.FUNCAPP.id = new_id;
  }
  struct AsrtList *ia;
  for (ia = spec->pre; ia != NULL; ia = ia->next)
    cpa_rename_exists(ia->head, mapping, env);
  for (ia = spec->post; ia != NULL; ia = ia->next)
    cpa_rename_exists(ia->head, mapping, env);
}

struct renaming_info *cpa_renaming_to_old(struct renaming_info *r) {
  switch (r->t) {
  case RENAME_VAR_PRE_VALUE:
  case RENAME_VAR_ADDR:
  case RENAME_VAR_VALUE:
  case RENAME_RETURN_VALUE:
  case RENAME_FORALL_VAR:
  case RENAME_EXISTS_VAR:
  case RENAME_FREE_VAR:
  case RENAME_POST_INTROED:
    return renaming_info_deep_copy(r);
  case RENAME_DEREF: {
    struct renaming_info *ret = renaming_info_deref(cpa_renaming_to_old(r->d.deref.info));
    ret->is_old = 1;
    return ret; }
  case RENAME_FIELD: {
    struct renaming_info *ret = renaming_info_field(cpa_renaming_to_old(r->d.field.info),
                                                    r->d.field.name);
    ret->is_old = 1;
    return ret; }
  case RENAME_FALLBACK: {
    struct renaming_info *ret = renaming_info_fallback(r->d.fallback.name);
    ret->is_old = 1;
    return ret; }
  }
}

void cpa_to_old(struct AsrtList *a, struct persistent_env *env) {
  struct AsrtList *i;
  struct hashtbl map;
  init_hashtbl(&map, hash_uint, uint_equal);
  for (i = a; i != NULL; i = i->next) {
    struct Assertion *a = i->head;
    struct ExistList *ie;
    for (ie = a->exist_list; ie != NULL; ie = ie->next) {
      struct logic_var_info *old = find_logic_var_by_id(ie->id, env);
      switch (old->renaming->t) {
      case RENAME_VAR_PRE_VALUE:
      case RENAME_VAR_ADDR:
      case RENAME_VAR_VALUE:
      case RENAME_RETURN_VALUE:
      case RENAME_FORALL_VAR:
      case RENAME_EXISTS_VAR:
      case RENAME_FREE_VAR:
      case RENAME_POST_INTROED:
        break;
      case RENAME_DEREF:
      case RENAME_FIELD:
      case RENAME_FALLBACK: {
        struct logic_var_info *new = add_anonymous_logic_var(old->category, clone_str(old->name), env);
        ASSIGN_ATYPE(new->atype, old->atype);
        new->qv = clone_qvar_list(old->qv);
        new->renaming = cpa_renaming_to_old(old->renaming);
        ie->id = new->id;
        hashtbl_add(&map, cast_int(old->id), cast_int(new->id));
        break;
      }
      }
    }
    cpa_do_rename(a, &map);
    hashtbl_clear(&map);
  }
}

