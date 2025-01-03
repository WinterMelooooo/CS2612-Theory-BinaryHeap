#ifndef LANG_H_INCLUDED
#define LANG_H_INCLUDED

struct persistent_env;

#include "lang_common.h"
#include "../SymExec/AsrtDef/AssDef.h"

struct type_info {
  unsigned int id;
  char *name;
  struct type *type;
};

enum prog_var_category {
    PROG_GLOBAL,
    PROG_LOCAL,
    PROG_FUNC
};

enum logic_var_category {
    LOGIC_USER_EXISTS,
    LOGIC_GEN_EXISTS,
    LOGIC_FORALL, // after cpassert, a FORALL might actually be a nested EXIST (that is, not a EXIST in a symbolic heap, but rather a EXIST in a proposition
    LOGIC_FREE,
    LOGIC_EXTERN,
    LOGIC_PROJ,
    LOGIC_SEPDEF
};

struct prog_var_info {
  enum prog_var_category category;
  unsigned int id;
  char *name;
  struct prog_var_info *shadowing;
  struct type *type;
  struct logic_var_info *value;
  struct logic_var_info *address;
  struct func_info *func;
};

struct qvar_list {
  struct atype *qv;
  struct qvar_list *next;
};

struct logic_var_info {
  enum logic_var_category category;
  unsigned int id;
  char *name;
  struct qvar_list *qv;
  struct atype *atype;
  union {
    struct renaming_info * renaming;
    struct sepdef_info *sep;
  };
  struct prog_var_info *value_or_address;
};

struct struct_union_info {
  enum { IS_STRUCT, IS_UNION } t;
  unsigned int id;
  int defined;
  char *name;
  struct field_info *first_field;
  unsigned int size;
  unsigned int alignment;
};

struct enum_info {
  unsigned int id;
  int defined;
  char *name;
  struct enumerator_info *first_rator;
};

struct enumerator_info {
  unsigned int id;
  char *name;
  int repr;
  struct enum_info *parent;
  struct enumerator_info *next;
};

struct field_info {
  unsigned int id;
  char *name;
  struct type *type;
  int offset;
  struct field_info *another; // same name
  struct field_info *next;
  struct struct_union_info *parent;
};

struct func_spec {
  struct ExistList *witht; // only used when generalizing
  struct qvar_list *qv;
  struct ExistList *with; // despite the name ...
  struct ExprVal *__return;
  struct AsrtList *pre;
  struct AsrtList *post;
  char *name;
  char *derived_by;
  struct func_spec *next;
};

struct func_info {
  unsigned int id;
  int defined;

  struct type *ret_type;
  char *name;
  struct prog_var_info_list *param;
  struct cmd *body;

  struct func_spec *spec;

  struct prog_var_info *var;
};

struct projection_info {
  unsigned int id;
  char *name;
  struct qvar_list *qv;
  struct logic_var_info *var;
  struct projection_info *next;
};

struct sepdef_info {
  int defined;
  unsigned int id;
  char *name;
  struct ExistList *param;
  struct AsrtList *condition;
  struct logic_var_info *var;
};

enum DeclType { T_BASIC, T_STRUCT, T_UNION, T_ENUM, T_PTR, T_ARRAY, T_FUNCTION, T_TYPE_ALIAS };

enum ExprType {
  T_CONST,
  T_STRING,
  T_VAR,
  T_BINOP,
  T_UNOP,
  T_CAST,
  T_CALL,
  T_DEREF,  // *e
  T_ADDRES, // &e
  T_SIZEOFTYPE,
  T_INDEX,     // a[i]
  T_FIELDOF,   // a.t
  T_FIELDOFPTR, // a->t
  T_ENUMLIT,
  T_CONDITION
};

enum CaseType { T_CASE, T_DEFAULT };

enum SimpleCmdType { T_COMPUTATION, T_ASGN, T_INCDEC };

enum CmdType {
  T_VARDECL,
  T_TYPEDEF,
  T_SIMPLE,
  T_SEQ,
  T_IF,
  T_SWITCH,
  T_WHILE,
  T_DOWHILE,
  T_FOR,
  T_BREAK,
  T_CONTINUE,
  T_RETURN,
  T_COMMENT,
  T_PARTIAL_COMMENT,
  T_DO_STRATEGY,
  T_SKIP,
  T_BLOCK,
  T_PROOF,
  T_STRUCT_DEF,
  T_STRUCT_DEC,
  T_UNION_DEF,
  T_UNION_DEC,
  T_ENUM_DEF,
  T_ENUM_DEC,
};

struct type {
  int refcnt;
  enum DeclType t;
  union {
    struct {
      enum BasicType ty;
    } BASIC;
    struct {
      struct struct_union_info *info;
    } STRUCT;
    struct {
      struct struct_union_info *info;
    } UNION;
    struct {
      struct enum_info *info;
    } ENUM;
    struct {
      struct type *ty;
    } PTR;
    struct {
      struct type *ty;
      unsigned int size;
    } ARRAY;
    struct {
      struct type *ret;
      struct type_list *param;
    } FUNCTION;
    struct {
      struct type_info *info;
    } TYPE_ALIAS;
  } d;
};

struct type_list {
  struct type *hd;
  struct type_list *tl;
};

struct type_arg_list {
  char *name;
  struct atype *type;
  struct type_arg_list *next;
};

struct virt_arg_list {
  char *name;
  struct ExprVal *val;
  struct atype *type;
  struct virt_arg_list *next;
};

struct virt_arg {
  struct func_spec *ctx;
  struct type_arg_list *type_arg;
  struct virt_arg_list *arg;
  char *spec_name;
};

struct expr {
  enum ExprType t;
  union {
    struct {
      unsigned long long value;
    } CONST;
    struct {
      char *str;
    } STRING;
    struct {
      struct prog_var_info *info;
    } VAR;
    struct {
      enum BinOpType op;
      struct expr *left;
      struct expr *right;
    } BINOP;
    struct {
      enum UnOpType op;
      struct expr *arg;
    } UNOP;
    struct {
      struct expr *arg;
    } DEREF;
    struct {
      struct expr *arg;
    } ADDRES;
    struct {
      struct type *ty;
      struct expr *arg;
    } CAST;
    struct {
      struct expr *func;
      struct expr_list *args;
      struct virt_arg *vargs;
    } CALL;
    struct {
      struct type *ty;
    } SIZEOFTYPE;
    struct {
      struct expr *arg;
      struct expr *pos;
    } INDEX;
    struct {
      struct expr *arg;
      struct field_info* field;
    } FIELDOF;
    struct {
      struct expr *arg;
      struct field_info* field;
    } FIELDOFPTR;
    struct {
      struct enumerator_info *info;
    } ENUMLIT;
    struct {
      struct expr *cond;
      struct expr *btrue;
      struct expr *bfalse;
    } CONDITION;
  } d;
  struct type *type;
};

struct expr_list {
  struct expr *head;
  struct expr_list *tail;
};

struct simple_cmd {
  enum SimpleCmdType t;
  union {
    struct {
      struct expr *arg;
    } COMPUTATION;
    struct {
      enum AssignType op;
      struct expr *left;
      struct expr *right;
    } ASGN;
    struct {
      enum IncDecType op;
      struct expr *arg;
    } INCDEC;
  } d;
};

struct cmd {
  enum CmdType t;
  union {
    struct {
      struct prog_var_info *info;
    } VARDECL;
    struct {
      struct type_info *info;
    } TYPEDEF;
    struct {
      struct simple_cmd *scmd;
    } SIMPLE;
    struct {
      struct cmd *left;
      struct cmd *right;
    } SEQ;
    struct {
      struct expr *cond;
      struct cmd *left;
      struct cmd *right;
    } IF;
    // right = NULL if the if-else branch does not exist
    struct {
      struct {
        struct AsrtList *inv;
        int is_partial;
      };
      struct expr *cond;
      struct cmd *body;
    } WHILE;
    // inv = NULL if the loop has no invariant annotation
    struct {
      struct expr *cond;
      struct Case_list *body;
    } SWITCH;
    struct {
      struct {
        struct AsrtList *inv;
        int is_partial;
      };
      struct expr *cond;
      struct cmd *body;
    } DOWHILE;
    // inv = NULL if the loop has no invariant annotation
    struct {
      struct {
        struct AsrtList *inv;
        int is_partial;
      };
      struct simple_cmd *init;
      struct expr *cond;
      struct simple_cmd *incr;
      struct cmd *body;
    } FOR;
    // inv = NULL if the loop has no invariant annotation
    struct { } BREAK;
    struct { } CONTINUE;
    struct {
      struct expr *arg;
    } RETURN;
    // arg = NULL if the return command does not have a return value
    struct {
      char *mark;
      int is_partial;
      struct AsrtList *asrt;
    } COMMENT;
    struct {
      struct func_spec *specs;
    } PARTIAL_COMMENT;
    struct {
      char *name;
    } DO_STRATEGY;
    struct { } SKIP;
    struct {
      struct cmd *cmd;
    } BLOCK;
    struct {
      char *proof;
    } PROOF;
    struct {
      struct struct_union_info *info;
    } STRUCT_DEF;
    struct {
      struct struct_union_info *info;
    } STRUCT_DEC;
    struct {
      struct struct_union_info *info;
    } UNION_DEF;
    struct {
      struct struct_union_info *info;
    } UNION_DEC;
    struct {
      struct enum_info *info;
    } ENUM_DEF;
    struct {
      struct enum_info *info;
    } ENUM_DEC;
  } d;
};

struct Case {
  enum CaseType t;
  union {
    struct {
      struct expr *cond;
      struct cmd *body;
    } CASE;
    struct {
      struct cmd *body;
    } DEFAULT;
  } d;
};

struct Case_list {
  struct Case *head;
  struct Case_list *tail;
};

struct qvar_list *qvar_list_cons(struct atype *qv, struct qvar_list *next);
void free_qvar_list(struct qvar_list *qv);
struct qvar_list *clone_qvar_list(struct qvar_list *qv);

struct type *TBasic(enum BasicType ty);
struct type *TStruct(struct struct_union_info *info);
struct type *TUnion(struct struct_union_info *info);
struct type *TEnum(struct enum_info *info);
struct type *TPtr(struct type *ty);
struct type *TArray(struct type *ty, unsigned int size);
struct type *TFunction(struct type *ret, struct type_list *param);
struct type *TTypeAlias(struct type_info *info);

struct type_list *TLNil();
struct type_list *TLCons(struct type *hd, struct type_list *tl);

struct expr *TConst(unsigned long long value);
struct expr *TString(char *string);
struct expr *TVar(struct prog_var_info *info);
struct expr *TBinop(enum BinOpType op, struct expr *left, struct expr *right);
struct expr *TUnop(enum UnOpType op, struct expr *arg);
struct expr *TDeref(struct expr *arg);
struct expr *TAddress(struct expr *arg);
struct expr *TCast(struct type *ty, struct expr *arg);
struct expr *TCall(struct expr *func, struct expr_list *args, struct virt_arg *vargs);
struct expr *TSizeofType(struct type *ty);
struct expr *TIndex(struct expr *arg, struct expr *pos);
struct expr *TFieldof(struct expr *arg, struct field_info *field);
struct expr *TFieldofptr(struct expr *arg, struct field_info *field);
struct expr *TEnumLit(struct enumerator_info *info);
struct expr *TCondition(struct expr *cond, struct expr *true, struct expr *false);

struct expr_list *ELNil();
struct expr_list *ELCons(struct expr *head, struct expr_list *tail);

struct simple_cmd *TComputation(struct expr *arg);
struct simple_cmd *TAsgn(enum AssignType op, struct expr *left, struct expr *right);
struct simple_cmd *TIncDec(enum IncDecType op, struct expr *arg);

struct cmd *TVarDecl(struct prog_var_info *info);
struct cmd *TTypedef(struct type_info *info);
struct cmd *TSimple(struct simple_cmd *scmd);
struct cmd *TSeq(struct cmd *left, struct cmd *right);
struct cmd *TIf(struct expr *cond, struct cmd *left, struct cmd *right);
struct cmd *TSwitch(struct expr *cond, struct Case_list *body);
struct cmd *TWhile(struct AsrtList *inv, int is_partial, struct expr *cond, struct cmd *body);
struct cmd *TDoWhile(struct AsrtList *inv, int is_partial, struct expr *cond,
                     struct cmd *body);
struct cmd *TFor(struct AsrtList *inv, int is_partial, struct simple_cmd *init,
                 struct expr *cond, struct simple_cmd *incr, struct cmd *body);
struct cmd *TBreak();
struct cmd *TContinue();
struct cmd *TReturn(struct expr *arg);
struct cmd *TComment(struct AsrtList *asrt, int is_partial, char *mark);
struct cmd *TPartialComment(struct func_spec *specs);
struct cmd *TProof(char *proof);
struct cmd *TDoStrategy(char *name);
struct cmd *TSkip();
struct cmd *TBlock(struct cmd *cmd);
struct cmd *TStructDef(struct struct_union_info *info);
struct cmd *TStructDec(struct struct_union_info *info);
struct cmd *TUnionDef(struct struct_union_info *info);
struct cmd *TUnionDec(struct struct_union_info *info);
struct cmd *TEnumDef(struct enum_info *info);
struct cmd *TEnumDec(struct enum_info *info);

struct Case *TCase(struct expr *cond, struct cmd *body);
struct Case *TDefault(struct cmd *body);
struct Case_list *CLNil();
struct Case_list *CLCons(struct Case *head, struct Case_list *tail);

struct qvar_list * qvar_list_deep_copy(struct qvar_list *qv);
struct func_spec * func_spec_deep_copy(struct func_spec *spec);
void func_spec_free(struct func_spec *spec);

void print_type(struct type *ty, char *ident);
void print_expr(struct expr *e, struct persistent_env *env);
void print_cmd(struct cmd *c, int full_asrt, struct persistent_env *env);

extern int print_suffix;
void print_assertion(struct AsrtList *a, int addressable, struct persistent_env *env);
void print_exprval(struct ExprVal *e, struct persistent_env *env);
void print_prop(struct Proposition *p, struct persistent_env *env);
void print_sep(struct Separation *sep, struct persistent_env *env);
void print_spec(struct func_spec *spec, struct persistent_env *env);

#define ASSIGN_TYPE(t, u) \
  {                       \
    struct type *v = u;   \
    t = v;                \
    v->refcnt += 1;       \
  }

#define REPLACE_TYPE(t, u) \
  {                       \
    struct type *v = u;   \
    if (t != u) {         \
      v->refcnt += 1;     \
      if (t != NULL)      \
        free_type(t);     \
      t = v;              \
    }                     \
  }

struct type *type_unalias(struct type *ty);
int type_size(struct type *t);
int type_align(struct type *t);
int type_equal(struct type *t1, struct type *t2);
int type_is_void(struct type *ty);
void free_type(struct type *ty);
void free_expr(struct expr *e);

struct type *type_of_simple_ctype(struct SimpleCtype *ct, struct persistent_env *env);

struct atype *atype_of_polytype(struct PolyType *t, struct persistent_env *env);

#endif // LANG_H_INCLUDED

/* nullable summary:
   - right(alternate) branch of if
   - function body
   - union/structure/enumeration body
   - function specification
   - loop invariant
   - return value
   - type in declaration (annotated variable). this happens in function
     specification and predicate definition. */
