#ifndef _LANG_H_INCLUDED
#define _LANG_H_INCLUDED

#include "../SymExec/Automation/PatternASTDef/PatternASTDef.h"
#include "../SymExec/Paras.h"

enum lang_UnOpType{
    lang_T_MINUS,        // -1(number)
};

enum lang_BinOpType {
    lang_T_EQ,    // ==
    lang_T_NEQ,  // !=
    lang_T_LE,
    lang_T_GE,
    lang_T_LT,
    lang_T_GT,
    lang_T_FIELDOFPTR,   // a->t
    lang_T_FIELDOF,  // a.t
    lang_T_OR,   // ||
    lang_T_ADD, // +
    lang_T_MUL, // *
    lang_T_SUB, // -
    lang_T_DIV // /
};

enum lang_VarType {
    NORMAL_VAR,
    EXISTS_VAR,
    ATOM_VAR,
    PATTERN_VAR
};

enum lang_Token {
    lang_T_UPPER_NULL,
    lang_T_LOWER_NULL,
    //patern_type
    lang_T_I8,
    lang_T_U8,
    lang_T_I16,
    lang_T_U16,
    lang_T_I32,
    lang_T_U32,
    lang_T_I64,
    lang_T_U64,
};

enum lang_LEFTRIGHT_Type {
    lang_T_RIGHT,
    lang_T_LEFT,
    lang_T_UNKNOWN
};

enum lang_ExprType {
    lang_T_CONST,
    lang_T_VAR,
    lang_T_ARRINX,
    lang_T_BINOP,
    lang_T_UNOP,
    lang_T_FUNC,
    lang_T_TOKEN,
    lang_T_SIZEOF,
    lang_T_DATA_AT,
    lang_T_UNDEF_DATA_AT
};

struct lang_expr_list;
struct lang_expr_list;
struct lang_action;
struct lang_action_list;
struct lang_rule_list;

struct lang_expr{
    enum lang_ExprType t;
    union{
        struct {
            unsigned long long value;
        } CONST;
        struct {
            enum lang_VarType vt;
            char *name;
            struct PatternPolyType *type;
        } VAR;
        struct {
            enum lang_BinOpType op;
            struct lang_expr *left;
            struct lang_expr *right;
        } BINOP;
        struct {
            struct lang_expr *name;
            struct lang_expr *index;
        } ARRINX;
        struct {
           struct PatternCType *type;
        } SIZEOF;
        struct {
            enum lang_UnOpType op;
            struct lang_expr *arg;
        } UNOP;
        struct {
            struct lang_expr *name;
            struct PatternPolyTypeList *types;
            struct lang_expr_list *args;
            int paraNumber;
            int typeNumber;
        } FUNC;
        struct {
          struct lang_expr *addr;
          struct PatternCType *type;
          struct lang_expr *value;
        } DATA_AT;
        struct {
          struct lang_expr *addr;
          struct PatternCType *type;
        } UNDEF_DATA_AT;
        struct {
            enum lang_Token tk;
        } TOKEN;
    } d;
};

struct lang_pattern {
   enum lang_LEFTRIGHT_Type t;
   struct lang_expr *expr;
   int at_number;  
};

struct lang_pattern_list {
  struct lang_pattern *head;
  struct lang_pattern_list *tail;
};

struct lang_priority {
    char * name;
    int prio;
};

struct lang_priority_list {
    struct lang_priority *head;
    struct lang_priority_list *tail;
};

struct lang_cmd {
   unsigned int ID;
   struct lang_priority_list *prio;
   struct lang_pattern_list *patterns;
   struct lang_action_list *actions;   
   struct lang_action_list *checks;
};

struct lang_action {
    char *name;
    struct lang_expr *arg;
};

struct lang_expr_list {
    struct lang_expr *head;
    struct lang_expr_list *tail;
};

struct lang_action_list {
    struct lang_action *head;
    struct lang_action_list *tail;
};

struct lang_rule_list{
    struct lang_cmd *head;
    struct lang_rule_list *tail;
};

struct lang_rule_file{
    struct StringList *Path;
    struct lang_rule_list *rules;
};

struct lang_expr *lang_TConst(unsigned long long value);
struct lang_expr *lang_TVar(char *name, struct PatternPolyType * type, enum lang_VarType vt);
struct lang_expr *lang_TBinOp(enum lang_BinOpType op,struct lang_expr *left,struct lang_expr *right);
struct lang_expr *lang_TUnOp(enum lang_UnOpType op,struct lang_expr *arg);
struct lang_expr *lang_TFunc(struct lang_expr *name,struct PatternPolyTypeList *types,struct lang_expr_list *args);
struct lang_expr *lang_TToken(enum lang_Token tk);
struct lang_expr *lang_TSizeof(struct PatternCType *type);
struct lang_expr *lang_TArrinx(struct lang_expr *name,struct lang_expr *index);
struct lang_expr *lang_TDataAt(struct lang_expr *addr,struct PatternCType *type,struct lang_expr *value);
struct lang_expr *lang_TUndefDataAt(struct lang_expr *addr,struct PatternCType *type);
struct lang_expr *lang_exprDeepCopy(struct lang_expr *e);

struct lang_cmd *lang_cmd(unsigned int ID,struct lang_priority_list *prio,struct lang_pattern_list *patterns,struct lang_action_list *actions,struct lang_action_list *checks);

struct lang_pattern *lang_TPattern(struct lang_expr *expr, int at_number);
struct lang_pattern_list *lang_TPatternList(struct lang_pattern_list *pat_list, enum lang_LEFTRIGHT_Type t);
struct lang_pattern_list *lang_TPatternListApp(struct lang_pattern_list *a,struct lang_pattern_list *d);
struct lang_pattern_list *lang_PTLNil();
struct lang_pattern_list *lang_PTLCons(struct lang_pattern *a,struct lang_pattern_list *d);

struct lang_priority *lang_PR(char *name,int prio);
struct lang_priority_list *lang_PRNil();
struct lang_priority_list *lang_PRCons(struct lang_priority *a,struct lang_priority_list *d);


struct lang_action *lang_TAction(char *name,struct lang_expr* arg);
struct lang_action_list *lang_ALNil();
struct lang_action_list *lang_ALCons(struct lang_action *a,struct lang_action_list *d);

struct lang_expr_list *lang_PLNil();
struct lang_expr_list *lang_PLCons(struct lang_expr *a,struct lang_expr_list *d);
struct lang_expr_list *lang_PLDeepCopy(struct lang_expr_list *e);

struct lang_rule_list *lang_RLNil();
struct lang_rule_list *lang_RLCons(struct lang_cmd *a,struct lang_rule_list *d);

struct lang_rule_file *lang_RF(struct StringList *include_paths,struct lang_rule_list *rules);

void lang_print_BinOp(enum lang_BinOpType op);
void lang_print_UnOp(enum lang_UnOpType op);
void lang_print_expr(struct lang_expr *e);
void lang_print_exprs(struct lang_expr_list *e);
void lang_print_action(struct lang_action *act);
void lang_print_actions(struct lang_action_list *acts);
void lang_print_pattern(struct lang_pattern *p);
void lang_print_patterns(struct lang_pattern_list *ps);
void lang_print_priority(struct lang_priority *p);
void lang_print_priorities(struct lang_priority_list *ps);
void lang_print_cmd(struct lang_cmd *c);
void lang_print_rules(struct lang_rule_list *rules);
void lang_print_include_paths(struct StringList *path);

void free_lang_expr(struct lang_expr *e);
void free_lang_expr_list(struct lang_expr_list *el);

struct PatternPolyType * AlterPatternPolyTypeVar(char *name);
struct PatternPolyType * AlterPatternPolyTypeConst(char *name);

unsigned long long lang_build_nat(char *c, int len, int Signed, int type);
unsigned int lang_build_hex(char *c, int len);
char * lang_new_str(char * str, int len);

# endif
