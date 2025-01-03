enum DeclType { T_BASIC, T_STRUCT, T_UNION, T_ENUM, T_PTR, T_ARRAY, T_ANON_STRUCT, T_ANON_UNION, T_ANON_ENUM };

enum DefType {
  T_FUNCDEC,
  T_FUNCDEF,
  T_SPEDEF,
  T_UNIONDEF,
  T_ENUMDEF,
  T_STRUCTDEF,
  T_UNIONDEC,
  T_ENUMDEC,
  T_STRUCTDEC,
  T_GLBVARDEF
};

enum BinOpType {
  T_PLUS,
  T_MINUS,
  T_MUL,
  T_DIV,
  T_MOD,
  T_LT,
  T_GT,
  T_LE,
  T_GE,
  T_EQ,
  T_NE,
  T_AND,
  T_OR,
  T_BAND,
  T_BOR,
  T_XOR,
  T_SHL,
  T_SHR
};

enum UnOpType {
  T_UMINUS,
  T_UPLUS,
  T_NOTBOOL,
  T_NOTINT
};

enum ExprType {
  T_CONST,
  T_VAR,
  T_BINOP,
  T_UNOP,
  T_CAST,
  T_CALL,
  T_DEREF,
  T_ADDRES,
  T_SIZEOFTYPE,
  T_INDEX,
  T_FIELDOF,
  T_FIELDOFPTR,
  T_ENUMLIT
};

enum CaseType { T_CASE, T_DEFAULT };

enum AssignType {
  T_ASSIGN,
  T_ADD_ASSIGN,
  T_SUB_ASSIGN,
  T_MUL_ASSIGN,
  T_DIV_ASSIGN,
  T_MOD_ASSIGN,
  T_BAND_ASSIGN,
  T_BOR_ASSIGN,
  T_XOR_ASSIGN,
  T_SHL_ASSIGN,
  T_SHR_ASSIGN
};

enum IncDecType {
  T_INC_F,
  T_INC_B,
  T_DEC_F,
  T_DEC_B
};

enum SimpleCmdType { T_COMPUTATION, T_ASGN, T_INCDEC };

enum CmdType {
  T_VARDECL,
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
  T_SKIP,
  T_BLOCK,
  T_PROOF
};

struct type;
struct expr;
struct expr_list;
struct cmd;
struct Case;
struct Case_list;
struct var_list;
struct def_list;
struct RAssertion;
struct RA_list;
struct func_def;
struct union_def;
struct enum_def;
struct struct_def;

struct annot {
  char *name;
  struct type *type;
  unsigned int id;
};

struct annot_list {
  struct annot *head;
  struct annot_list *tail;
};

struct uvar {
  char *name;
  unsigned int id;
  struct annot *ref;
};

struct field_dec_list;
struct enum_list;

struct type {
  enum DeclType t;
  union {
    struct {
      enum { T_VOID, T_CHAR, T_U8, T_SHORT, T_U16, T_INT, T_INT64, T_UINT, T_UINT64 } ty;
    } BASIC;
    struct {
      char *name;
      struct struct_def *ref;
    } STRUCT;
    struct {
      char *name;
      struct union_def *ref;
    } UNION;
    struct {
      char *name;
    } ENUM;
    struct {
      struct type *ty;
    } PTR;
    struct {
      struct type *ty;
      struct expr *size;
    } ARRAY;
    struct {
      struct field_dec_list *fields;
    } ANON_STRUCT;
    struct {
      struct field_dec_list *fields;
    } ANON_UNION;
    struct {
      struct enum_list *names;
    } ANON_ENUM;
  } d;
};
