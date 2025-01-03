#include "utils.h"
#include "alang.h"
#include "plang.h"
#include "hashtbl.h"

#define create(name, ty)                                         \
  struct ty *name = (struct ty *)malloc(sizeof(struct ty));      \
  if (name == NULL) {                                            \
    fprintf(stderr, "Failure in malloc.\n");                     \
    exit(0);                                                     \
  }

struct RAssertion *RASizeOf(struct pp_pretype *ty) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_SIZEOF;
  res->d.RASIZEOF.ty = ty;
  return res;
}

struct RAssertion *RAOld(char *mark, struct RAssertion *arg) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_OLD;
  res->d.RAOLD.mark = mark;
  res->d.RAOLD.arg = arg;
  return res;
}

struct RAssertion *RAShadow(struct RAssertion *arg) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_SHADOW;
  res->d.RASHADOW.arg = arg;
  return res;
}

struct RAssertion *RATrue() {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_TRUE;
  return res;
}

struct RAssertion *RAFalse() {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_FALSE;
  return res;
}

struct RAssertion *RAEnumLit(char *name) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_ENUMLIT;
  res->d.RAENUMLIT.name = name;
  return res;
}

struct RAssertion *RAEmp() {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_EMP;
  return res;
}

struct RAssertion *RA__return() {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA___RETURN;
  return res;
}

struct RAssertion *RAConst(unsigned long long value) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_CONST;
  res->d.RACONST.value = value;
  return res;
}

struct RAssertion *RAVar(char *name) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_PROGVAR;
  res->d.RAPROGVAR.name = name;
  return res;
}

struct RAssertion *RALogicVar(struct logic_var_info *info) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_LOGICVAR;
  res->d.RALOGICVAR.info = info;
  return res;
}

struct RAssertion *RABinop(enum BinOpType op, struct RAssertion *left,
                           struct RAssertion *right) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_BINOP;
  res->d.RABINOP.op = op;
  res->d.RABINOP.left = left;
  res->d.RABINOP.right = right;
  return res;
}

struct RAssertion *RAConn(enum LogicConnective op,
                          struct RAssertion *left, struct RAssertion *right) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_CONN;
  res->d.RACONN.op = op;
  res->d.RACONN.left = left;
  res->d.RACONN.right = right;
  return res;
}

struct RAssertion *RAUnop(enum UnOpType op, struct RAssertion *arg) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_UNOP;
  res->d.RAUNOP.op = op;
  res->d.RAUNOP.arg = arg;
  return res;
}

struct RAssertion *RADeref(struct pp_pretype *ty, struct RAssertion *arg) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_DEREF;
  res->d.RADEREF.ty = ty;
  res->d.RADEREF.arg = arg;
  return res;
}

struct RAssertion *RAAddress(struct RAssertion *arg) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_ADDRESS;
  res->d.RAADDRESS.arg = arg;
  return res;
}

struct RAssertion *RACast(struct pp_pretype *ty, struct RAssertion *arg) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_CAST;
  res->d.RACAST.ty = ty;
  res->d.RACAST.arg = arg;
  return res;
}

struct RAssertion *RAApp(struct RAssertion *f, struct RAssertion *rand) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_APP;
  res->d.RAAPP.f = f;
  res->d.RAAPP.rand = rand;
  return res;
}

struct RAssertion *RAAnn(struct atype *type, struct RAssertion *expr) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_ANN;
  ASSIGN_ATYPE(res->d.RAANN.type, type);
  res->d.RAANN.expr = expr;
  return res;
}

struct RAssertion *RAIndex(struct RAssertion *arg,
                           struct RAssertion *pos) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_INDEX;
  res->d.RAINDEX.arg = arg;
  res->d.RAINDEX.pos = pos;
  return res;
}

struct RAssertion *RAFieldof(struct RAssertion *arg, char *name, struct pp_pretype *ty) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_FIELDOF;
  res->d.RAFIELDOF.arg = arg;
  res->d.RAFIELDOF.name = name;
  res->d.RAFIELDOF.ty = ty;
  return res;
}

struct RAssertion *RAFieldofptr(struct RAssertion *arg, char *name, struct pp_pretype *ty) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_FIELDOFPTR;
  res->d.RAFIELDOFPTR.arg = arg;
  res->d.RAFIELDOFPTR.name = name;
  res->d.RAFIELDOFPTR.ty = ty;
  return res;
}

struct RAssertion *RAQfop(enum LogicQuantifierType op, int bracket, char *name,
                          struct atype_list *qv, struct atype *body,
                          struct RAssertion *arg) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_QFOP;
  res->d.RAQFOP.op = op;
  res->d.RAQFOP.bracket = bracket;
  res->d.RAQFOP.arg = arg;
  res->d.RAQFOP.abs.name = name;
  res->d.RAQFOP.abs.qv = qv;
  res->d.RAQFOP.abs.body = body;
  return res;
}

struct RAssertion *RAMultiQfop(enum LogicQuantifierType op, int bracket, struct name_list *names,
                               struct atype_list *qv, struct atype *body,
                               struct RAssertion *arg) {
  if (names == NULL) {
    deep_free_atype_list(qv);
    return arg;
  } else {
    char *name = names->head;
    struct name_list *names1 = names->tail;
    free(names);
    struct atype_list *cqv = clone_atype_list(qv);
    return RAQfop(op, bracket, name, qv, body, RAMultiQfop(op, bracket, names1, cqv, body, arg));
  }
}

struct RAssertion *RAData_at(struct pp_pretype *type, struct RAssertion *addr, struct RAssertion *val) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_DATA_AT;
  res->d.RADATA_AT.type = type;
  res->d.RADATA_AT.addr = addr;
  res->d.RADATA_AT.val = val;
  res->d.RADATA_AT.ty = NULL;
  return res;
}

struct RAssertion *RAUndef_data_at(struct pp_pretype *type, struct RAssertion *val) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_UNDEF_DATA_AT;
  res->d.RAUNDEF_DATA_AT.type = type;
  res->d.RAUNDEF_DATA_AT.addr = val;
  res->d.RAUNDEF_DATA_AT.ty = NULL;
  return res;
}

struct RAssertion *RAField_addr(struct RAssertion *addr, struct pp_pretype *ty, char *field_name) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_FIELD_ADDRESS;
  res->d.RAFIELD_ADDRESS.addr = addr;
  res->d.RAFIELD_ADDRESS.ty = ty;
  res->d.RAFIELD_ADDRESS.field_name = field_name;
  return res;
}

struct RAssertion *RAArr(struct RAssertion *addr, struct pp_pretype *elt, struct RAssertion *len, struct RAssertion *list) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_ARR;
  res->d.RAARR.addr = addr;
  res->d.RAARR.elt = elt;
  res->d.RAARR.len = len;
  res->d.RAARR.list = list;
  res->d.RAARR.ty = NULL;
  return res;
}

struct RAssertion *RASpec(struct RAssertion *f, struct pp_pretype *sig, struct pp_spec *spec) {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_SPEC;
  res->d.RASPEC.f = f;
  res->d.RASPEC.sig = sig;
  res->d.RASPEC.spec = spec;
  return res;
}

struct RAssertion *RATimeCost() {
  create(res, RAssertion);
  res->type = NULL;
  res->t = RA_TIME_COST;
  return res;
}

#undef create

void print_connective_File(FILE *f, enum LogicConnective op) {
  switch (op) {
  case A_IMPLY: fprintf(f, " => "); break;
  case A_IFF:   fprintf(f, " <=> "); break;
  }
}

void print_quantifier_File(FILE *f, enum LogicQuantifierType op) {
  switch (op) {
  case A_EXISTS: fprintf(f, "exists"); break;
  case A_FORALL: fprintf(f, "forall"); break;
  }
}

void print_connective(enum LogicConnective op) {
  print_connective_File(stdout, op);
}

void print_quantifier(enum LogicQuantifierType op) {
  print_quantifier_File(stdout, op);
}

void print_app_rec_File(FILE *f, struct RAssertion *app) {
  if (app->t == RA_APP) {
    print_app_rec_File(f, app->d.RAAPP.f);
    print_RA_File(f, app->d.RAAPP.rand);
    fprintf(f, ", ");
  } else {
    print_RA_File(f, app);
    fprintf(f, "(");
  }
}

void print_app_File(FILE *f, struct RAssertion *app) {
  print_app_rec_File(f, app->d.RAAPP.f);
  print_RA_File(f, app->d.RAAPP.rand);
  fprintf(f, ")");
}

void print_app(struct RAssertion *app) {
  print_app_File(stdout, app);
}

void print_RA_File(FILE *f, struct RAssertion *ra) {
  switch (ra->t) {
  case RA_CONST:
    fprintf(f, "%llu", ra->d.RACONST.value);
    break;
  case RA_PROGVAR:
    fprintf(f, "%s", ra->d.RAPROGVAR.name);
    break;
  case RA_LOGICVAR:
    fprintf(f, "%s", ra->d.RALOGICVAR.info->name);
    break;
  case RA_BINOP:
    fprintf(f, "(");
    print_RA_File(f,ra->d.RABINOP.left);
    fprintf(f," ");
    print_BinOp_File(f, ra->d.RABINOP.op);
    fprintf(f," ");
    print_RA_File(f,ra->d.RABINOP.right);
    fprintf(f,")");
    break;
  case RA_CONN:
    fprintf(f,"(");
    print_RA_File(f, ra->d.RACONN.left);
    print_connective_File(f, ra->d.RACONN.op);
    print_RA_File(f, ra->d.RACONN.right);
    fprintf(f, ")");
    break;
  case RA_UNOP:
    fprintf(f,"(");
    print_UnOp_File(f,ra->d.RAUNOP.op);
    print_RA_File(f,ra->d.RAUNOP.arg);
    fprintf(f,")");
    break;
  case RA_CAST:
    fprintf(f,"((");
    print_pretype_File(f,ra->d.RACAST.ty);
    fprintf(f,")");
    print_RA_File(f,ra->d.RACAST.arg);
    fprintf(f,")");
    break;
  case RA_APP:
    print_app_File(f,ra);
    break;
  case RA_ANN:
    fprintf(f,"(");
    print_RA_File(f,ra->d.RAANN.expr);
    fprintf(f," : ");
    print_pp_atype_File(f,ra->d.RAANN.type);
    fprintf(f,")");
    break;
  case RA_DEREF:
    fprintf(f,"(*");
    if (ra->d.RADEREF.ty != NULL) {
      fprintf(f,"{");
      print_pretype_File(f,ra->d.RADEREF.ty);
      fprintf(f,"}");
    }
    print_RA_File(f,ra->d.RADEREF.arg);
    fprintf(f,")");
    break;
  case RA_ADDRESS:
    fprintf(f,"(&");
    print_RA_File(f,ra->d.RAADDRESS.arg);
    fprintf(f,")");
    break;
  case RA_INDEX:
    fprintf(f,"(");
    print_RA_File(f,ra->d.RAINDEX.arg);
    fprintf(f,"[");
    print_RA_File(f,ra->d.RAINDEX.pos);
    fprintf(f,"])");
    break;
  case RA_FIELDOF:
    fprintf(f,"(");
    print_RA_File(f,ra->d.RAFIELDOF.arg);
    if (ra->d.RAFIELDOF.ty != NULL) {
      fprintf(f, ".{");
      print_pretype_File(f, ra->d.RAFIELDOF.ty);
      fprintf(f, ".%s}", ra->d.RAFIELDOF.name);
    } else
      fprintf(f,".%s)", ra->d.RAFIELDOF.name);
    break;
  case RA_FIELDOFPTR:
    fprintf(f,"(");
    print_RA_File(f, ra->d.RAFIELDOFPTR.arg);
    if (ra->d.RAFIELDOFPTR.ty != NULL) {
      fprintf(f, ".{");
      print_pretype_File(f, ra->d.RAFIELDOFPTR.ty);
      fprintf(f, ".%s}", ra->d.RAFIELDOFPTR.name);
    } else
      fprintf(f,"->%s)", ra->d.RAFIELDOFPTR.name);
    break;
  case RA_ENUMLIT:
    fprintf(f,"%s", ra->d.RAENUMLIT.name);
    break;
  case RA_QFOP: {
    fprintf(f,"(");
    enum LogicQuantifierType q;
    q = ra->d.RAQFOP.op;
    print_quantifier_File(f, q);
    for (; ra->t == RA_QFOP && ra->d.RAQFOP.op == q; ra = ra->d.RAQFOP.arg) {
      if (ra->d.RAQFOP.bracket)
        fprintf(f," [");
      else
        fprintf(f," ");
      fprintf(f,"%s", ra->d.RAQFOP.abs.name);
      if (ra->d.RAQFOP.bracket)
        fprintf(f,"]");
    }
    fprintf(f,", ");
    print_RA_File(f,ra);
    fprintf(f, ")");
    break; }
  case RA_EMP:
    fprintf(f,"emp");
    break;
  case RA___RETURN:
    fprintf(f,"__return");
    break;
  case RA_SIZEOF:
    fprintf(f,"sizeof(");
    print_pretype_File(f, ra->d.RASIZEOF.ty);
    fprintf(f,")");
    break;
  case RA_OLD:
    fprintf(f,"(");
    print_RA_File(f,ra->d.RAOLD.arg);
    fprintf(f,"@%s", ra->d.RAOLD.mark);
    fprintf(f,")");
    break;
  case RA_SHADOW:
    fprintf(f,"(#");
    print_RA_File(f,ra->d.RASHADOW.arg);
    fprintf(f,")");
    break;
  case RA_TRUE:
    fprintf(f,"__true");
    break;
  case RA_FALSE:
    fprintf(f,"__false");
    break;
  case RA_DATA_AT:
    fprintf(f,"data_at(");
    print_RA_File(f,ra->d.RADATA_AT.addr);
    if (ra->d.RADATA_AT.type != NULL) {
      fprintf(f,", ");
      print_pretype_File(f,ra->d.RADATA_AT.type);
    }
    fprintf(f,", ");
    print_RA_File(f,ra->d.RADATA_AT.val);
    fprintf(f,")");
    break;
  case RA_UNDEF_DATA_AT:
    fprintf(f,"undef_data_at(");
    print_RA_File(f,ra->d.RAUNDEF_DATA_AT.addr);
    if (ra->d.RAUNDEF_DATA_AT.type != NULL) {
      fprintf(f,", ");
      print_pretype_File(f,ra->d.RAUNDEF_DATA_AT.type);
    }
    fprintf(f,")");
    break;
  case RA_FIELD_ADDRESS:
    fprintf(f,"field_address(");
    print_RA_File(f,ra->d.RAFIELD_ADDRESS.addr);
    if (ra->d.RAFIELD_ADDRESS.ty != NULL){
      fprintf(f, ", ");
      print_pretype_File(f, ra->d.RAFIELD_ADDRESS.ty);
    }
    fprintf(f,", %s)", ra->d.RAFIELD_ADDRESS.field_name);
    break;
  case RA_ARR:
    fprintf(f, "Arr(");
    print_RA_File(f, ra->d.RAARR.addr);
    if (ra->d.RAARR.elt != NULL) {
      printf(", ");
      print_pretype_File(f,ra->d.RAARR.elt);
    }
    fprintf(f, ", ");
    print_RA_File(f,ra->d.RAARR.len);
    fprintf(f,", ");
    print_RA_File(f,ra->d.RAARR.list);
    fprintf(f,")");
    break;
  case RA_SPEC:
    fprintf(f,"(");
    print_RA_File(f,ra->d.RASPEC.f);
    fprintf(f," |= \n");
    nspace += 2;
    print_space_File(f);
    print_pretype_File(f,ra->d.RASPEC.sig);
    fprintf(f,"\n");
    print_pp_spec_File(f,ra->d.RASPEC.spec);
    print_space_File(f);
    fprintf(f,")");
    nspace -= 2;
    break;
  case RA_TIME_COST:
    fprintf(f, "__time_cost");
    break;
  }
}

void print_RA(struct RAssertion *l) {
    print_RA_File(stdout, l);
}

void free_ra(struct RAssertion *ra) {
  switch (ra->t) {
  case RA_CONST:
    break;
  case RA_LOGICVAR:
    free_qvar_list(ra->d.RALOGICVAR.impl);
    break;
  case RA_PROGVAR:
    free(ra->d.RAPROGVAR.name);
    break;
  case RA_BINOP:
    free_ra(ra->d.RABINOP.left);
    free_ra(ra->d.RABINOP.right);
    break;
  case RA_CONN:
    free_ra(ra->d.RACONN.left);
    free_ra(ra->d.RACONN.right);
    break;
  case RA_UNOP:
    free_ra(ra->d.RAUNOP.arg);
    break;
  case RA_CAST:
    free_ra(ra->d.RACAST.arg);
    if (ra->d.RACAST.ty != NULL) // copied
      free_pp_pretype(ra->d.RACAST.ty);
    break;
  case RA_APP:
    free_ra(ra->d.RAAPP.f);
    free_ra(ra->d.RAAPP.rand);
    break;
  case RA_ANN:
    free_atype(ra->d.RAANN.type);
    free_ra(ra->d.RAANN.expr);
    break;
  case RA_DEREF:
    if (ra->d.RADEREF.ty != NULL)
      free_pp_pretype(ra->d.RADEREF.ty);
    free_ra(ra->d.RADEREF.arg);
    break;
  case RA_ADDRESS:
    free_ra(ra->d.RAADDRESS.arg);
    break;
  case RA_INDEX:
    free_ra(ra->d.RAINDEX.arg);
    free_ra(ra->d.RAINDEX.pos);
    break;
  case RA_FIELDOF:
    free_ra(ra->d.RAFIELDOF.arg);
    free(ra->d.RAFIELDOF.name);
    if (ra->d.RAFIELDOF.ty != NULL)
      free_pp_pretype(ra->d.RAFIELDOF.ty);
    break;
  case RA_FIELDOFPTR:
    free_ra(ra->d.RAFIELDOFPTR.arg);
    free(ra->d.RAFIELDOFPTR.name);
    if (ra->d.RAFIELDOFPTR.ty != NULL)
      free_pp_pretype(ra->d.RAFIELDOFPTR.ty);
    break;
  case RA_QFOP:
    free_ra(ra->d.RAQFOP.arg);
    break;
  case RA_ENUMLIT:
  case RA_EMP:
  case RA___RETURN:
  case RA_TIME_COST:
  case RA_TRUE:
  case RA_FALSE:
    break;
  case RA_SIZEOF:
    if (ra->d.RASIZEOF.ty != NULL)
      free_pp_pretype(ra->d.RASIZEOF.ty);
    free_type(ra->d.RASIZEOF.type);
    break;
  case RA_OLD:
    free_ra(ra->d.RAOLD.arg);
    free(ra->d.RAOLD.mark);
    break;
  case RA_SHADOW:
    free_ra(ra->d.RASHADOW.arg);
    break;
  case RA_DATA_AT:
    free_ra(ra->d.RADATA_AT.addr);
    free_ra(ra->d.RADATA_AT.val);
    if (ra->d.RADATA_AT.type != NULL)
      free_pp_pretype(ra->d.RADATA_AT.type);
    free_type(ra->d.RADATA_AT.ty);
    break;
  case RA_UNDEF_DATA_AT:
    free_ra(ra->d.RAUNDEF_DATA_AT.addr);
    if (ra->d.RAUNDEF_DATA_AT.type != NULL)
      free_pp_pretype(ra->d.RAUNDEF_DATA_AT.type);
    free_type(ra->d.RAUNDEF_DATA_AT.ty);
    break;
  case RA_FIELD_ADDRESS:
    free_ra(ra->d.RAFIELD_ADDRESS.addr);
    if (ra->d.RAFIELD_ADDRESS.ty != NULL)
      free_pp_pretype(ra->d.RAFIELD_ADDRESS.ty);
    free(ra->d.RAFIELD_ADDRESS.field_name);
    break;
  case RA_ARR:
    free_ra(ra->d.RAARR.addr);
    if (ra->d.RAARR.len != NULL)
      free_ra(ra->d.RAARR.len);
    free_ra(ra->d.RAARR.list);
    if (ra->d.RAARR.elt != NULL)
      free_pp_pretype(ra->d.RAARR.elt);
    free_type(ra->d.RAARR.ty);
    break;
  case RA_SPEC:
    free_ra(ra->d.RASPEC.f);
    if (ra->d.RASPEC.sig != NULL)
      free_pp_pretype(ra->d.RASPEC.sig);
    if (ra->d.RASPEC.spec != NULL)
      free_pp_spec(ra->d.RASPEC.spec);
    break;
  }
  free_type(ra->type);
  free(ra);
}

struct kind *KStar() {
  struct kind *k = (struct kind *)malloc(sizeof(struct kind));
  k->refcnt = 0;
  k->t = K_STAR;
  return k;
}

struct kind *KArrow(struct kind *from, struct kind *to) {
  struct kind *k = (struct kind *)malloc(sizeof(struct kind));
  k->refcnt = 0;
  k->t = K_ARROW;
  ASSIGN_KIND(k->d.ARROW.from, from);
  ASSIGN_KIND(k->d.ARROW.to, to);
  return k;
}

struct kind *KVar(char *name) {
  struct kind *k = (struct kind *)malloc(sizeof(struct kind));
  k->refcnt = 0;
  k->t = K_KVAR;
  k->d.KVAR.name = name;
  k->d.KVAR.link = NULL;
  return k;
}

struct atype *ATArrow(struct atype *from, struct atype *to) {
  struct atype *ty = (struct atype *)malloc(sizeof(struct atype));
  ty->refcnt = 0;
  ty->t = AT_ARROW;
  ASSIGN_ATYPE(ty->d.ARROW.from, from);
  ASSIGN_ATYPE(ty->d.ARROW.to, to);
  return ty;
}

struct atype *ATApp(struct atype *tfn, struct atype *rand) {
  struct atype *ty = (struct atype *)malloc(sizeof(struct atype));
  ty->refcnt = 0;
  ty->t = AT_APP;
  ASSIGN_ATYPE(ty->d.APP.tfn, tfn);
  ASSIGN_ATYPE(ty->d.APP.rand, rand);
  return ty;
}

struct atype *ATQVar(char *name, struct kind *kind) {
  struct atype *ty = (struct atype *)malloc(sizeof(struct atype));
  ty->refcnt = 0;
  ty->t = AT_QVAR;
  ty->d.QVAR.name = name;
  ASSIGN_KIND(ty->d.QVAR.kind, kind);
  ty->d.QVAR.inst = NULL;
  return ty;
}

struct atype *ATTVar(char *name, struct kind *k) {
  struct atype *ty = (struct atype *)malloc(sizeof(struct atype));
  ty->refcnt = 0;
  ty->t = AT_TVAR;
  ty->d.TVAR.name = name;
  if (k != NULL)
    ASSIGN_KIND(ty->d.TVAR.kind, k)
  else
    ty->d.TVAR.kind = NULL;
  ty->d.TVAR.link = NULL;
  return ty;
}

struct atype *ATAtom(struct atype_info *info) {
  struct atype *ty = (struct atype *)malloc(sizeof(struct atype));
  ty->refcnt = 0;
  ty->t = AT_ATOM;
  ty->d.ATOM.info = info;
  return ty;
}

struct atype *atype_deep_copy(struct atype *ty) {
  ++ty->refcnt;
  return ty;
}

void free_kind_if_unused(struct kind *k) {
  if (k->refcnt <= 0) {
    switch (k->t) {
    case K_STAR:
      break;
    case K_ARROW:
      free_kind(k->d.ARROW.from);
      free_kind(k->d.ARROW.to);
      break;
    case K_KVAR:
      if (k->d.KVAR.link != NULL)
        free_kind(k->d.KVAR.link);
      break;
    }
    free(k);
  }
}

void free_kind(struct kind *k) {
  k->refcnt -= 1;
  free_kind_if_unused(k);
}

void free_atype(struct atype *ty) {
  ty->refcnt -= 1;
  free_atype_if_unused(ty);
}

void free_atype_if_unused(struct atype *ty) {
  if (ty->refcnt <= 0) {
    switch (ty->t) {
    case AT_ATOM:
      break;
    case AT_QVAR:
      if (ty->d.QVAR.inst != NULL)
        free_atype(ty->d.QVAR.inst);
      free_kind(ty->d.QVAR.kind);
      break;
    case AT_ARROW:
      free_atype(ty->d.ARROW.from);
      free_atype(ty->d.ARROW.to);
      break;
    case AT_APP:
      free_atype(ty->d.APP.tfn);
      free_atype(ty->d.APP.rand);
      break;
    case AT_TVAR:
      if (ty->d.TVAR.kind != NULL)
        free_kind(ty->d.TVAR.kind);
      if (ty->d.TVAR.link != NULL)
        free_atype(ty->d.TVAR.link);
      break;
    }
    free(ty);
  }
}

struct atype *clone_atype(struct atype *ty) {
  switch (ty->t) {
  case AT_TVAR:
    return ATTVar(clone_str(ty->d.TVAR.name), ty->d.TVAR.kind);
  case AT_ATOM:
    return ty;
  case AT_ARROW:
    return ATArrow(clone_atype(ty->d.ARROW.from),
                   clone_atype(ty->d.ARROW.to));
  case AT_APP:
    return ATApp(clone_atype(ty->d.APP.tfn),
                 clone_atype(ty->d.APP.rand));
  case AT_QVAR:
    assert(0);
  }
}

int kind_is_star(struct kind *k) {
  return k->t == K_STAR;
}

int kind_is_arrow(struct kind *k) {
  return k->t == K_ARROW;
}

int kind_is_kvar(struct kind *k) {
  return k->t == K_KVAR;
}

int atype_is_list(struct atype *type) {
  return type->t == AT_ATOM && type->d.ATOM.info->id == BUILTINTYPE_LIST;
}

int atype_is_prod(struct atype *type) {
  return type->t == AT_ATOM && type->d.ATOM.info->id == BUILTINTYPE_PROD;
}

int atype_is_prop(struct atype *type) {
  return type->t == AT_ATOM && type->d.ATOM.info->id == BUILTINTYPE_PROP;
}

int atype_is_tvar(struct atype *type) {
  return type->t == AT_TVAR;
}

int atype_is_atom(struct atype *type) {
  return type->t == AT_ATOM;
}

int atype_is_app(struct atype *type) {
  return type->t == AT_APP;
}

int atype_is_qvar(struct atype *type) {
  return type->t == AT_QVAR;
}

int kind_equal(struct kind *k1, struct kind *k2) {
  if (k1 == k2)
    return 1;

  while (k1->t == K_KVAR && k1->d.KVAR.link != NULL)
    k1 = k1->d.KVAR.link;
  while (k2->t == K_KVAR && k2->d.KVAR.link != NULL)
    k2 = k2->d.KVAR.link;

  if (k1->t != k2->t)
    return 0;

  switch (k1->t) {
  case K_STAR:
    return 1;
  case K_ARROW:
    return
      kind_equal(k1->d.ARROW.from, k2->d.ARROW.from) &&
      kind_equal(k1->d.ARROW.to, k2->d.ARROW.to);
  case K_KVAR:
    return 0;
  }
}

int atype_equal_rec(struct atype *t1, struct atype *t2,
                    struct hashtbl *cor) {
  if (t1 == t2)
    return 1;

  while (t1->t == AT_TVAR && t1->d.TVAR.link != NULL)
    t1 = t1->d.TVAR.link;
  while (t2->t == AT_TVAR && t2->d.TVAR.link != NULL)
    t2 = t2->d.TVAR.link;

  if (t1->t != t2->t)
    return 0;

  switch (t1->t) {
  case AT_ATOM: 
    return t1->d.ATOM.info->id == t2->d.ATOM.info->id;
  case AT_ARROW:
    return
      atype_equal_rec(t1->d.ARROW.from, t2->d.ARROW.from, cor) &&
      atype_equal_rec(t1->d.ARROW.to, t2->d.ARROW.to, cor);
  case AT_APP:
    return
      atype_equal_rec(t1->d.APP.tfn, t2->d.APP.tfn, cor) &&
      atype_equal_rec(t1->d.APP.rand, t2->d.APP.rand, cor);
  case AT_QVAR: {
    int v;
    struct atype *q2 = hashtbl_find(cor, t1, &v);
    if (v) {
      return t2 == q2;
    } else {
      hashtbl_add(cor, t1, t2);
      return 1;
    }
  }
  case AT_TVAR:
    return 0;
  }
}

int atype_equal(struct atype *t1, struct atype *t2) {
  struct hashtbl h;
  init_hashtbl(&h, hash_ptr, ptr_equal);
  int ret = atype_equal_rec(t1, t2, &h);
  hashtbl_clear(&h);
  return ret;
}
