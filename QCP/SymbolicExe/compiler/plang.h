#ifndef PLANG_H_INCLUDED
#define PLANG_H_INCLUDED

#include "lang_common.h"
#include "alang.h"
#include "../SymExec/Utility/List.h"

struct pp_trivtype {
  int is_extern_or_static;
  enum {
    PP_TRIV_BASIC,
    PP_TRIV_STRUCT,
    PP_TRIV_UNION,
    PP_TRIV_ENUM,
    PP_TRIV_ANON_STRUCT,
    PP_TRIV_ANON_UNION,
    PP_TRIV_ANON_ENUM,
    PP_TRIV_TYPE_ALIAS
  } t;
  union {
    struct { enum BasicType ty; } BASIC;
    struct { char *name; } STRUCT;
    struct { char *name; } UNION;
    struct { char *name; } ENUM;
    struct { char *name; struct annot_list *fields; } ANON_STRUCT;
    struct { char *name; struct annot_list *fields; } ANON_UNION;
    struct { char *name; struct pp_enum_list *names; } ANON_ENUM;
    struct { char *name; } TYPE_ALIAS;
  } d;
};

struct pp_derivtype {
  enum {
    PP_DERIV_END,
    PP_DERIV_PTR,
    PP_DERIV_ARRAY,
    PP_DERIV_FUNCTION
  } t;
  union {
    struct { char *name; } END;
    struct { struct pp_derivtype *deriv; } PTR;
    struct { struct pp_derivtype *deriv; struct pp_expr *size; } ARRAY;
    struct { struct pp_derivtype *deriv; struct annot_list *param; } FUNCTION;
  } d;
};

struct pp_pretype {
  struct pp_trivtype *triv;
  struct pp_derivtype *deriv;
  struct pp_type *type;
};

struct pp_varg_list {
  char *name;
  struct atype *type;
  struct RAssertion *val;
  struct pp_varg_list *next;
};

struct pp_varg {
  char *spec_name;
  struct StringList *scopes;
  struct virt_arg *after;
  struct type_arg_list *type;
  struct pp_varg_list *pre;
};

struct pp_expr {
  enum {
    PP_CONST,
    PP_STRING,
    PP_VAR,
    PP_BINOP,
    PP_UNOP,
    PP_CAST,
    PP_CALL,
    PP_DEREF,
    PP_ADDRESS,
    PP_SIZEOFTYPE,
    PP_INDEX,
    PP_FIELDOF,
    PP_FIELDOFPTR,
    PP_ENUMLIT,
    PP_CONDITION
  } t;
  union {
    struct { unsigned long long value; int hex; int l; int u; }                        CONST;
    struct { char *str; }                                                              STRING;
    struct { char *name; struct prog_var_info *info; }                                 VAR;
    struct { enum BinOpType op; struct pp_expr *left; struct pp_expr *right; }         BINOP;
    struct { enum UnOpType op; struct pp_expr *arg; }                                  UNOP;
    struct { struct pp_expr *arg; }                                                    DEREF;
    struct { struct pp_expr *arg; }                                                    ADDRESS;
    struct { struct pp_pretype *ty; struct pp_expr *arg; }                             CAST;
    struct { struct pp_expr *func; struct pp_expr_list *args; struct pp_varg *vargs; } CALL;
    struct { struct pp_pretype *ty; }                                                  SIZEOFTYPE;
    struct { struct pp_expr *arg; struct pp_expr *pos; }                               INDEX;
    struct { struct pp_expr *arg; char *name; struct field_info *field; }              FIELDOF;
    struct { struct pp_expr *arg; char *name; struct field_info *field; }              FIELDOFPTR;
    struct { char *name; struct enumerator_info *info; }                               ENUMLIT;
    struct { struct pp_expr *cond; struct pp_expr *btrue; struct pp_expr *bfalse; }    CONDITION;
  } d;
  struct type *type;
};

struct pp_type {
  enum {
    PP_BASIC,
    PP_STRUCT,
    PP_UNION,
    PP_ENUM,
    PP_PTR,
    PP_ARRAY,
    PP_ANON_STRUCT,
    PP_ANON_UNION,
    PP_ANON_ENUM,
    PP_FUNCTION,
    PP_TYPE_ALIAS
  } t;
  union {
    struct { enum BasicType ty; }                               BASIC;
    struct { char *name; struct struct_union_info *info; }      STRUCT;
    struct { char *name; struct struct_union_info *info; }      UNION;
    struct { char *name; struct enum_info *info; }              ENUM;
    struct { struct pp_type *ty; }                              PTR;
    struct { struct pp_type *ty; struct pp_expr *size; }        ARRAY;
    struct { char *name; struct annot_list *fields; }           ANON_STRUCT;
    struct { char *name; struct annot_list *fields; }           ANON_UNION;
    struct { char *name; struct pp_enum_list *names; }          ANON_ENUM;
    struct { struct pp_type *ret; struct annot_list *param; }   FUNCTION;
    struct { char *name; struct type_info *info; }              TYPE_ALIAS;
  } d;
};

struct pp_simple {
  enum { PP_COMPUTATION, PP_ASGN, PP_INCDEC } t;
  union {
    struct { struct pp_expr *arg; }                                             COMPUTATION;
    struct { enum AssignType op; struct pp_expr *left; struct pp_expr *right; } ASGN;
    struct { enum IncDecType op; struct pp_expr *arg; }                         INCDEC;
  } d;
};

struct pp_expr_list {
  struct pp_expr *head;
  struct pp_expr_list *tail;
};

struct annot {
  char *name;
  struct pp_pretype *type;
};

struct annot_list {
  struct annot *head;
  struct annot_list *tail;
};

struct pp_initializer {
  enum { PP_SINGLE_EXPR, PP_INIT_LIST } t;
  union {
    struct { struct pp_expr *expr; } SINGLE_EXPR;
    struct { struct pp_initializer_list *list; } INIT_LIST;
  } d;
};

struct pp_initializer_list {
  enum { PP_NEXT, PP_DESIG } t;
  union {
    struct { struct pp_initializer *init; } NEXT;
    struct { struct pp_designator *desig; struct pp_initializer *init; } DESIG;
  } d;
  struct pp_initializer_list *next;
};

struct pp_designator {
  enum { PP_AT_INDEX, PP_AT_MEMBER } t;
  union {
    struct { struct pp_expr *index; } AT_INDEX;
    struct { char *field; } AT_MEMBER;
  } d;
  struct pp_designator *next;
};

struct pp_enum_list {
  char *name;
  int value_valid;
  int neg;
  unsigned long long int value;
  struct pp_enum_list *next;
};

struct term_list {
  char *name;
  struct atype_list *qv;
  struct atype *body;
  struct term_list *next;
};

struct atype_list {
  char *name;
  struct kind *kind;
  struct atype_list *next;
};

struct lvar_list {
  char *name;
  struct atype *type;
  struct lvar_list *next;
};

struct pp_spec {
  struct atype_list *witht;
  struct lvar_list *with;
  struct RAssertion *pre;
  struct RAssertion *post;
  char *name;
  char *derived_by;
};

enum partial_program_type {
  PP_FIRST_DECL,
  PP_MORE_DECL,
  PP_SIMPLE,
  PP_BREAK,
  PP_CONTINUE,
  PP_RETURN,
  PP_WHILE, /* while () {} or do {} while() */
  PP_IF,
  PP_ELSE,
  PP_DO,
  PP_FOR,
  PP_SWITCH,
  PP_CASE,
  PP_DEFAULT,
  PP_BLOCK,
  PP_END,    /* } */
  PP_ASSERT,
  PP_INV,
  PP_WI,
  PP_PROOF,
  PP_MISSING_INV,
  PP_DO_STRATEGY,
  PP_SKIP,

  PP_STRUCT_DEF,
  PP_UNION_DEF,
  PP_ENUM_DEF,
  PP_STRUCT_DEC,
  PP_UNION_DEC,
  PP_ENUM_DEC,
  PP_SEPDEF,
  PP_FUNC_DEF,
  PP_FUNC_DEC,
  PP_COQ_TYPE_ALIAS,
  PP_COQ_DEC,
  PP_ATYPE_DEC,
  PP_PROJ_DEC,
  PP_RECORD_DEC
};

struct partial_program {
  enum partial_program_type t;
  union {
    struct {
      int is_end;
      int is_typedef;
      struct pp_pretype *pre;
      struct pp_initializer *init;
    } FIRST_DECL;
    struct {
      int is_end;
      struct pp_derivtype *deriv;
      struct pp_initializer *init;
    } MORE_DECL;
    struct { struct pp_simple *simple; } SIMPLE;
    struct { } BREAK;
    struct { } CONTINUE;
    struct { struct pp_expr *ret; } RETURN;
    struct { struct pp_expr *cond; } WHILE;
    struct { struct pp_expr *cond; } IF;
    struct { } ELSE;
    struct { } DO;
    struct {
      struct pp_simple *init;
      struct pp_expr *cond;
      struct pp_simple *step;
    } FOR;
    struct { struct pp_expr *cond; } SWITCH;
    struct { struct pp_expr *cond; } CASE;
    struct { } DEFAULT;
    struct { } BLOCK;
    struct { } END;
    struct { struct RAssertion *assert; char *mark; int partial; struct StringList *scopes; } ASSERT;
    struct { struct RAssertion *assert; int partial; struct StringList *scopes; } INV;
    struct { struct RAssertion *pre; struct StringList *pre_scopes; struct RAssertion *post; struct StringList *post_scopes; } WI;
    struct { char *name; } PROOF;
    struct { } MISSING_INV;
    struct { char *name; } DO_STRATEGY;
    struct { } SKIP;

    struct { char *name; struct annot_list *field; } STRUCT_DEF;
    struct { char *name; struct annot_list *field; } UNION_DEF;
    struct { char *name; struct pp_enum_list *rator; } ENUM_DEF;
    struct { char *name; } STRUCT_DEC;
    struct { char *name; } UNION_DEC;
    struct { char *name; } ENUM_DEC;
    struct {
      char *name;
      struct atype_list *witht;
      struct lvar_list *with;
      struct RAssertion *condition;
    } SEPDEF;
    struct {
      struct pp_pretype *func;
      struct pp_spec *spec;
    } FUNC_DEF;
    struct {
      struct pp_pretype *func;
      struct pp_spec *spec;
    } FUNC_DEC;
    struct {
      struct term_list *name;
    } COQ_DEC;
    struct {
      char *name;
      struct atype *type;
    } COQ_TYPE_ALIAS;
    struct {
      struct atype_list *name;
    } ATYPE_DEC;
    struct {
      struct term_list *projs;
    } PROJ_DEC;
    struct {
      struct atype_list *params;
      char *record_name;
      char *constr_name;
      struct lvar_list *fields;
    } RECORD_DEC;
  } d;
};

struct pp_trivtype *TRIVBasic(enum BasicType ty);
struct pp_trivtype *TRIVStruct(char *name);
struct pp_trivtype *TRIVUnion(char *name);
struct pp_trivtype *TRIVEnum(char *name);
struct pp_trivtype *TRIVAnonStruct(char *name, struct annot_list *fields);
struct pp_trivtype *TRIVAnonUnion(char *name, struct annot_list *fields);
struct pp_trivtype *TRIVAnonEnum(char *name, struct pp_enum_list *names);
struct pp_trivtype *TRIVTypeAlias(char *name);
struct pp_trivtype *TRIVExternOrStatic(struct pp_trivtype *triv);

struct pp_derivtype *DERIVEnd(char *name);
struct pp_derivtype *DERIVPtr(struct pp_derivtype *ty);
struct pp_derivtype *DERIVArray(struct pp_derivtype *ty, struct pp_expr *size);
struct pp_derivtype *DERIVFunction(struct pp_derivtype *ret, struct annot_list *param);

struct pp_pretype *PreType(struct pp_trivtype *triv, struct pp_derivtype *deriv);

struct annot *TAnnot(struct pp_pretype *ty);
struct annot_list *ALNil();
struct annot_list *ALCons(struct annot *a, struct annot_list *d);

struct pp_enum_list *pp_enum_list_cons(char *name, int value_valid, int neg, unsigned long long value, struct pp_enum_list *next);
struct term_list *term_list_cons(char *name, struct atype_list *qv, struct atype *body, struct term_list *next);
struct atype_list *atype_list_cons(char *name, struct kind *kind, struct atype_list *next);
struct lvar_list *lvar_list_cons(char *name, struct atype *type, struct lvar_list *next);
struct term_list *term_list_cons_multi(struct name_list *names, struct atype_list *qv, struct atype *body, struct term_list *next);
struct atype_list *atype_list_cons_multi(struct name_list *names, struct kind *kind, struct atype_list *next);
struct lvar_list *lvar_list_cons_multi(struct name_list *names, struct atype *type, struct lvar_list *next);
struct coq_module_path *coq_module_path_cons(char *mod, struct coq_module_path *next);

struct type_arg_list *ATypeArg(char *name, struct atype *type, struct type_arg_list *next);
struct pp_varg_list *PPVArg(char *name, struct RAssertion *val, struct pp_varg_list *next);

struct pp_type *PPBasic(enum BasicType ty);
struct pp_type *PPStruct(char *name);
struct pp_type *PPUnion(char *name);
struct pp_type *PPEnum(char *name);
struct pp_type *PPPtr(struct pp_type *ty);
struct pp_type *PPArray(struct pp_type *ty, struct pp_expr *size);
struct pp_type *PPAnonStruct(char *name, struct annot_list *fields);
struct pp_type *PPAnonUnion(char *name, struct annot_list *fields);
struct pp_type *PPAnonEnum(char *name, struct pp_enum_list *names);
struct pp_type *PPFunction(struct pp_type *ret, struct annot_list *param);
struct pp_type *PPTypeAlias(char *name);

struct pp_expr *PPConst(unsigned long long value, int hex, int l, int u);
struct pp_expr *PPString(char *str);
struct pp_expr *PPVar(char *name);
struct pp_expr *PPBinop(enum BinOpType op, struct pp_expr *left, struct pp_expr *right);
struct pp_expr *PPUnop(enum UnOpType op, struct pp_expr *arg);
struct pp_expr *PPDeref(struct pp_expr *arg);
struct pp_expr *PPAddress(struct pp_expr *arg);
struct pp_expr *PPCast(struct pp_pretype *ty, struct pp_expr *arg);
struct pp_expr *PPCall(struct pp_expr *func, struct pp_expr_list *args,
                       char *spec_name, struct StringList *scopes, struct type_arg_list *type_arg, struct pp_varg_list *vargs);
struct pp_expr *PPSizeofType(struct pp_pretype *ty);
struct pp_expr *PPIndex(struct pp_expr *arg, struct pp_expr *pos);
struct pp_expr *PPFieldof(struct pp_expr *arg, char *name);
struct pp_expr *PPFieldofptr(struct pp_expr *arg, char *name);
struct pp_expr *PPEnumLit(char *name);
struct pp_expr *PPCondition(struct pp_expr *cond, struct pp_expr *btrue, struct pp_expr *bfalse);

struct pp_expr_list *PELNil();
struct pp_expr_list *PELCons(struct pp_expr *head, struct pp_expr_list *tail);

struct pp_initializer *PPSingleExpr(struct pp_expr *expr);
struct pp_initializer *PPInitList(struct pp_initializer_list *list);
struct pp_initializer_list *PPNext(struct pp_initializer *init, struct pp_initializer_list *next);
struct pp_initializer_list *PPDesig(struct pp_designator *desig,
                                    struct pp_initializer *init,
                                    struct pp_initializer_list *next);
struct pp_designator *PPAtIndex(struct pp_expr *index, struct pp_designator *next);
struct pp_designator *PPAtMember(char *field, struct pp_designator *next);

struct pp_simple *PPComputation(struct pp_expr *arg);
struct pp_simple *PPAsgn(enum AssignType op, struct pp_expr *left, struct pp_expr *right);
struct pp_simple *PPIncDec(enum IncDecType op, struct pp_expr *arg);

struct partial_program *PPFirstDecl(int end, int is_typedef, struct pp_pretype *type, struct pp_initializer *init);
struct partial_program *PPMoreDecl(int end, struct pp_derivtype *deriv, struct pp_initializer *init);
struct partial_program *PPSimple(struct pp_simple *simple);
struct partial_program *PPBreak();
struct partial_program *PPContinue();
struct partial_program *PPReturn(struct pp_expr *ret);
struct partial_program *PPIf(struct pp_expr *cond);
struct partial_program *PPWhile(struct pp_expr *cond);
struct partial_program *PPElse();
struct partial_program *PPDo();
struct partial_program *PPFor(struct pp_simple *init, struct pp_expr *cond, struct pp_simple *step);
struct partial_program *PPSwitch(struct pp_expr *cond);
struct partial_program *PPCase(struct pp_expr *cond);
struct partial_program *PPDefault();
struct partial_program *PPBlock();
struct partial_program *PPEnd();
struct partial_program *PPAssert(struct RAssertion *assert, char *mark, int partial, struct StringList *scopes);
struct partial_program *PPInv(struct RAssertion *assert, int partial, struct StringList *scopes);
struct partial_program *PPWI(struct RAssertion *pre, struct StringList *pre_scopes, struct RAssertion *post, struct StringList *post_scopes);
struct partial_program *PPProof(char *name);
struct partial_program *PPMissingInv();
struct partial_program *PPDoStrategy(char *name);
struct partial_program *PPSkip();

struct partial_program *PPStructDef(char *name, struct annot_list *field);
struct partial_program *PPUnionDef(char *name, struct annot_list *field);
struct partial_program *PPEnumDef(char *name, struct pp_enum_list *rator);
struct partial_program *PPStructDec(char *name);
struct partial_program *PPUnionDec(char *name);
struct partial_program *PPEnumDec(char *name);
struct partial_program *PPSepdef(char *name, struct atype_list *witht, struct lvar_list *with, struct RAssertion *cond);

struct partial_program *PPCoqDec(struct term_list *names);
struct partial_program *PPCoqTypeAlias(char *name, struct atype *type);
struct partial_program *PPATypeDec(struct atype_list *names);
struct partial_program *PPProjDec(struct term_list *projs);
struct partial_program *PPRecordDec(struct atype_list *params,
                                    char *record_name, char *constr_name,
                                    struct lvar_list *fields);
struct partial_program *PPFuncDef(struct pp_pretype *func, struct pp_spec *spec);
struct partial_program *PPFuncDec(struct pp_pretype *func, struct pp_spec *spec);

struct pp_spec *PPSpec(char *name,
                       char *derived_by,
                       struct atype_list *witht,
                       struct lvar_list *with,
                       struct RAssertion *pre,
                       struct RAssertion *post);

/* pretty printing */

void print_pp_spec(struct pp_spec *spec);
void print_partial_program(struct partial_program *pp);
void print_pretype(struct pp_pretype *ty);
void print_pp_atype(struct atype *ty);
void print_pp_spec_File(FILE *f, struct pp_spec *spec);
void print_partial_program_File(FILE *f, struct partial_program *pp);
void print_pretype_File(FILE *f, struct pp_pretype *ty);
void print_pp_atype_File(FILE *f, struct atype *ty);

void free_pp_type(struct pp_type *ty);
void free_derivtype(struct pp_derivtype *deriv);
void free_pp_pretype(struct pp_pretype *pre);
void free_pp_expr(struct pp_expr *e);
void free_pp_spec(struct pp_spec *s);
void free_partial_program(struct partial_program *pp);
void free_annot_list(struct annot_list *al);
void free_pp_enum_list(struct pp_enum_list *l);

struct atype_list *clone_atype_list(struct atype_list *qv);
void deep_free_atype_list(struct atype_list *qv);

#endif
