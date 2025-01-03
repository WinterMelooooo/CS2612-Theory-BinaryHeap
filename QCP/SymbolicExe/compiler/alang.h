#ifndef ALANG_H
#define ALANG_H

#include "lang.h"

struct RAssertion;
struct RA_list;

enum LogicConnective { A_IMPLY, A_IFF };

enum LogicQuantifierType { A_FORALL, A_EXISTS };

enum RAssertionType {
  RA_CONST,
  RA_PROGVAR,
  RA_LOGICVAR,
  RA_BINOP,
  RA_CONN,
  RA_UNOP,
  RA_CAST,
  RA_APP,
  RA_ANN,
  RA_DEREF,      // *e
  RA_ADDRESS,     // &e
  RA_INDEX,      // a[i]
  RA_FIELDOF,    // a.t
  RA_FIELDOFPTR, // a->t
  RA_QFOP,
  RA_ENUMLIT,
  RA_EMP,
  RA___RETURN,
  RA_SIZEOF,
  RA_OLD,
  RA_SHADOW,
  RA_TRUE,
  RA_FALSE,
  RA_DATA_AT,
  RA_UNDEF_DATA_AT,
  RA_FIELD_ADDRESS,
  RA_ARR,
  RA_SPEC,
  RA_TIME_COST
};

struct RAssertion {
  struct type *type;
  enum RAssertionType t;
  union {
    struct {
      unsigned long long value;
    } RACONST;
    struct {
      char *name;
      struct prog_var_info *info;
    } RAPROGVAR;
    struct {
      struct qvar_list *impl;
      struct logic_var_info *info;
    } RALOGICVAR;
    struct {
      enum BinOpType op;
      struct RAssertion *left;
      struct RAssertion *right;
    } RABINOP;
    struct {
      enum LogicConnective op;
      struct RAssertion *left;
      struct RAssertion *right;
    } RACONN;
    struct {
      enum UnOpType op;
      struct RAssertion *arg;
    } RAUNOP;
    struct {
      struct pp_pretype *ty;
      struct RAssertion *arg;
    } RADEREF;
    struct {
      struct RAssertion *arg;
    } RAADDRESS;
    struct {
      struct pp_pretype *ty;
      struct RAssertion *arg;
    } RACAST;
    struct {
      struct RAssertion *f;
      struct RAssertion *rand;
    } RAAPP;
    struct {
      struct atype *type;
      struct RAssertion *expr;
    } RAANN;
    struct {
      struct RAssertion *arg;
      struct RAssertion *pos;
    } RAINDEX;
    struct {
      struct RAssertion *arg;
      char *name;
      struct pp_pretype *ty;
      struct struct_union_info *type;
      struct projection_info *proj;
      struct field_info *field;
    } RAFIELDOF;
    struct {
      struct RAssertion *arg;
      char *name;
      struct pp_pretype *ty;
      struct struct_union_info *type;
      struct field_info *field;
    } RAFIELDOFPTR;
    struct {
      int bracket; /* record syntax information here because GLR is not
                      possible when reentrant. */
      enum LogicQuantifierType op;
      struct {
        char *name;
        struct atype_list *qv;
        struct atype *body;
        struct logic_var_info *info;
      } abs;
      struct RAssertion *arg;
    } RAQFOP;
    struct {
      char *name;
      struct enumerator_info *info;
    } RAENUMLIT;
    struct { } RA__RETURN;
    struct { } RA_EMP;
    struct { } RA_TRUE;
    struct { } RA_FALSE;
    struct {
      struct pp_pretype *ty;
      struct type *type;
    } RASIZEOF;
    struct {
      char *mark;
      struct RAssertion *arg;
    } RAOLD;
    struct {
      struct RAssertion *arg;
    } RASHADOW;
    struct {
      struct pp_pretype *type;
      struct type *ty;
      struct RAssertion *addr;
      struct RAssertion *val;
    } RADATA_AT;
    struct {
      struct pp_pretype *type;
      struct type *ty;
      struct RAssertion *addr;
    } RAUNDEF_DATA_AT;
    struct {
      struct RAssertion *addr;
      struct pp_pretype *ty;
      char *field_name;
      struct struct_union_info *type;
      struct field_info *field;
    } RAFIELD_ADDRESS;
    struct {
      struct RAssertion *addr;
      struct pp_pretype *elt;
      struct type *ty;
      struct RAssertion *len;
      struct RAssertion *list;
    } RAARR;
    struct {
      struct RAssertion *f;
      struct pp_pretype *sig;
      struct pp_spec *spec;
      struct func_info *info;
    } RASPEC;
  } d;
};

struct RAssertion *RAConst(unsigned long long value);
struct RAssertion *RAVar(char *name);
struct RAssertion *RALogicVar(struct logic_var_info *info);
struct RAssertion *RABinop(enum BinOpType op, struct RAssertion *left,
                           struct RAssertion *right);
struct RAssertion *RAConn(enum LogicConnective op,
                          struct RAssertion *left, struct RAssertion *right);
struct RAssertion *RAUnop(enum UnOpType op, struct RAssertion *arg);
struct RAssertion *RADeref(struct pp_pretype *ty, struct RAssertion *arg);
struct RAssertion *RAAddress(struct RAssertion *arg);
struct RAssertion *RACast(struct pp_pretype *ty, struct RAssertion *arg);
struct RAssertion *RAApp(struct RAssertion *f, struct RAssertion *rand);
struct RAssertion *RAAnn(struct atype *type, struct RAssertion *expr);
struct RAssertion *RAIndex(struct RAssertion *arg, struct RAssertion *pos);
struct RAssertion *RAFieldof(struct RAssertion *arg, char *name, struct pp_pretype *ty);
struct RAssertion *RAFieldofptr(struct RAssertion *arg, char *name, struct pp_pretype *ty);
struct RAssertion *RAQfop(enum LogicQuantifierType op, int bracket, char *name,
                          struct atype_list *qv, struct atype *body,
                          struct RAssertion *arg);
struct RAssertion *RAMultiQfop(enum LogicQuantifierType op, int bracket, struct name_list *names,
                               struct atype_list *qv, struct atype *body,
                               struct RAssertion *arg);
struct RAssertion *RAEmp();
struct RAssertion *RA__return();
struct RAssertion *RASizeOf(struct pp_pretype *ty);
struct RAssertion *RAOld(char *mark, struct RAssertion *arg);
struct RAssertion *RAShadow(struct RAssertion *arg);
struct RAssertion *RATrue();
struct RAssertion *RAFalse();
struct RAssertion *RAEnumLit(char *name);
struct RAssertion *RAData_at(struct pp_pretype *type, struct RAssertion *addr, struct RAssertion *val);
struct RAssertion *RAUndef_data_at(struct pp_pretype *type, struct RAssertion *val);
struct RAssertion *RAField_addr(struct RAssertion *addr, struct pp_pretype *ty, char *field_name);
struct RAssertion *RAArr(struct RAssertion *addr, struct pp_pretype *elt, struct RAssertion *len, struct RAssertion *list);
struct RAssertion *RASpec(struct RAssertion *f, struct pp_pretype *sig, struct pp_spec *spec);
struct RAssertion *RATimeCost();

void print_quantifier(enum LogicQuantifierType op);
void print_RA(struct RAssertion *ra);
void print_RA_File(FILE *f, struct RAssertion *ra);

void free_ra(struct RAssertion *ra);

/*** type system */

// remember to update init_env!!
enum {
  BUILTINTYPE_Z = 1,
  BUILTINTYPE_NAT,
  BUILTINTYPE_BOOL,
  BUILTINTYPE_LIST,
  BUILTINTYPE_PROD,
  BUILTINTYPE_PROP,
  BUILTINTYPE_ASSERTION,
  BUILTINVALUE_INTMAX,
  BUILTINVALUE_INTMIN,
  BUILTINVALUE_ZPOW,
  BUILTINVALUE_ULNB, // unsigned last n bits for cast
  BUILTINVALUE_LNB, // signed last n bits for cast 
};

struct kind {
  int refcnt;
  enum { K_STAR, K_ARROW, K_KVAR } t;
  union {
    struct { } STAR;
    struct { struct kind *from; struct kind *to; } ARROW;
    struct { char *name; struct kind *link; } KVAR;
  } d;
};

struct atype {
  int refcnt;
  enum {
    AT_ATOM,
    AT_ARROW,
    AT_APP,
    AT_QVAR,
    AT_TVAR,
  } t;
  union {
    struct {
      struct atype *from;
      struct atype *to;
    } ARROW;
    struct {
      struct atype *tfn;
      struct atype *rand;
    } APP;
    struct {
      char *name;
      struct kind *kind;
      struct atype *inst;
    } QVAR;
    struct {
      char *name;
      struct kind *kind;
      struct atype *link;
    } TVAR;
    struct {
      struct atype_info *info;
    } ATOM;
  } d;
};

struct atype_info {
  int defined;
  char *name;
  unsigned int id;
  struct kind *kind;
};

#define ASSIGN_KIND(l, k)                       \
  {                                             \
    struct kind *t = k;                         \
    l = t;                                      \
    t->refcnt += 1;                             \
  }

#define ASSIGN_ATYPE(l, k)                      \
  {                                             \
    struct atype *t = k;                        \
    l = t;                                      \
    t->refcnt += 1;                             \
  }

#define REPLACE_ATYPE(l, k)                     \
  {                                             \
    struct atype *t = k;                        \
    if (l != t) {                               \
      t->refcnt += 1;                           \
      if (l != NULL)                            \
        free_atype(l);                          \
      l = t;                                    \
    }                                           \
}

#define REPLACE_KIND(l, k)                      \
  {                                             \
    struct kind *t = k;                         \
    if (l != t) {                               \
      t->refcnt += 1;                           \
      if (l != NULL)                            \
        free_kind(l);                           \
      l = t;                                    \
    }                                           \
}

struct kind *KStar();
struct kind *KArrow(struct kind *from, struct kind *to);
struct kind *KVar(char *name);

struct atype *ATArrow(struct atype *from, struct atype *to);
struct atype *ATApp(struct atype *tfn, struct atype *rand);
struct atype *ATQVar(char *name, struct kind *kind);
struct atype *ATTVar(char *name, struct kind *k);
struct atype *ATAtom(struct atype_info *info);

struct atype *atype_deep_copy(struct atype *ty);

void free_kind(struct kind *k);
void free_kind_if_unused(struct kind *k);

void free_atype(struct atype *ty);
void free_atype_if_unused(struct atype *ty);

struct atype *clone_atype(struct atype *ty);

void print_atype(struct atype *ty);
void print_atype_File(FILE *f, struct atype *ty);
char * Get_atype_name(struct atype *ty);

int kind_is_star(struct kind *k);
int kind_is_arrow(struct kind *k);
int kind_is_kvar(struct kind *k);

int atype_is_list(struct atype *type);
int atype_is_prod(struct atype *type);
int atype_is_prop(struct atype *type);
int atype_is_tvar(struct atype *type);
int atype_is_atom(struct atype *type);
int atype_is_app(struct atype *type);
int atype_is_qvar(struct atype *type);

int kind_equal(struct kind *k1, struct kind *k2);
// allow QVar; alpha equivalence
int atype_equal(struct atype *t1, struct atype *t2);


#endif
