#ifndef LANG_COMMON_H
#define LANG_COMMON_H

#include <stdio.h>

enum BasicType { T_VOID, T_CHAR, T_U8, T_SHORT, T_U16, T_INT, T_INT64, T_UINT, T_UINT64 };

enum BinOpType {
  T_PLUS,  // +
  T_MINUS, // -
  T_MUL,   // *
  T_DIV,   // /
  T_MOD,   // %
  T_LT,    // <
  T_GT,    // >
  T_LE,    // <=
  T_GE,    // >=
  T_EQ,    // ==
  T_NE,    // !=
  T_AND,   // &&
  T_OR,    // ||
  T_BAND,  // &
  T_BOR,   // |
  T_XOR,   // ^
  T_SHL,   // <<
  T_SHR    // >>
};

enum UnOpType {
  T_UMINUS,  // -
  T_UPLUS,   // +
  T_NOTBOOL, // !
  T_NOTINT   // ~
};

enum AssignType {
  T_ASSIGN,      // =
  T_ADD_ASSIGN,  // +=
  T_SUB_ASSIGN,  // -=
  T_MUL_ASSIGN,  // *=
  T_DIV_ASSIGN,  // /=
  T_MOD_ASSIGN,  // %=
  T_BAND_ASSIGN, // &=
  T_BOR_ASSIGN,  // |=
  T_XOR_ASSIGN,  // ^=
  T_SHL_ASSIGN,  // <<=
  T_SHR_ASSIGN   // >>=
};

enum IncDecType {
  T_INC_F, // ++e
  T_INC_B, // e++
  T_DEC_F, // --e
  T_DEC_B  // e--
};

struct name_list {
  char *head;
  struct name_list *tail;
};

extern int nspace;
void print_space();
void print_BinOp(enum BinOpType op);
void print_UnOp(enum UnOpType op);
void print_incdec(enum IncDecType op);
void print_AsgnOp(enum AssignType op);
void print_space_File(FILE *f);
void print_BinOp_File(FILE *f, enum BinOpType op);
void print_UnOp_File(FILE *f, enum UnOpType op);
void print_incdec_File(FILE *f, enum IncDecType op);
void print_AsgnOp_File(FILE *f, enum AssignType op);

void free_name_list(struct name_list *el);
struct name_list *NLNil();
struct name_list *NLCons(char *name, struct name_list *tail);
#endif
