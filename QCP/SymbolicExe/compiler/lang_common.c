#include "lang_common.h"
#include "utils.h"

int nspace = 0;

void print_space_File(FILE *f) {
  int i;
  fprintf(f,"");
  for (i = 0; i < nspace; i++)
    fprintf(f," ");
}

void print_space() {
  print_space_File(stdout);
}

void print_UnOp_File(FILE *f, enum UnOpType op) {
  switch (op) {
  case T_UMINUS:  fprintf(f,"-"); break;
  case T_UPLUS:   fprintf(f,"+"); break;
  case T_NOTBOOL: fprintf(f,"!"); break;
  case T_NOTINT:  fprintf(f,"~"); break;
  }
}

void print_UnOp(enum UnOpType op) {
  print_UnOp_File(stdout, op);
}

void print_BinOp_File(FILE *f, enum BinOpType op) {
  switch (op) {
  case T_PLUS:  fprintf(f,"+"); break;
  case T_MINUS: fprintf(f,"-"); break;
  case T_MUL:   fprintf(f,"*"); break;
  case T_DIV:   fprintf(f,"/"); break;
  case T_MOD:   fprintf(f,"%%"); break;
  case T_LT:    fprintf(f,"<"); break;
  case T_GT:    fprintf(f,">"); break;
  case T_LE:    fprintf(f,"<="); break;
  case T_GE:    fprintf(f,">="); break;
  case T_EQ:    fprintf(f,"=="); break;
  case T_NE:    fprintf(f,"!="); break;
  case T_AND:   fprintf(f,"&&"); break;
  case T_OR:    fprintf(f,"||"); break;
  case T_BAND:  fprintf(f,"&"); break;
  case T_BOR:   fprintf(f,"|"); break;
  case T_XOR:   fprintf(f,"^"); break;
  case T_SHL:   fprintf(f,"<<"); break;
  case T_SHR:   fprintf(f,">>"); break;
  }
}

void print_BinOp(enum BinOpType op) {
  print_BinOp_File(stdout, op);
}

void print_incdec_File(FILE *f, enum IncDecType op) {
  switch (op) {
  case T_INC_F: fprintf(f,"++"); break;
  case T_INC_B: fprintf(f,"++"); break;
  case T_DEC_F: fprintf(f,"--"); break;
  case T_DEC_B: fprintf(f,"--"); break;
  }
}

void print_incdec(enum IncDecType op) {
  print_incdec_File(stdout, op);
}

void print_AsgnOp_File(FILE *f, enum AssignType op) {
  switch (op) {
  case T_ASSIGN:      fprintf(f, " = "); break;
  case T_ADD_ASSIGN:  fprintf(f, " += "); break;
  case T_SUB_ASSIGN:  fprintf(f, " -= "); break;
  case T_MUL_ASSIGN:  fprintf(f, " *= "); break;
  case T_DIV_ASSIGN:  fprintf(f, " /= "); break;
  case T_MOD_ASSIGN:  fprintf(f, " %%= "); break;
  case T_BAND_ASSIGN: fprintf(f, " &= "); break;
  case T_BOR_ASSIGN:  fprintf(f, " |= "); break;
  case T_XOR_ASSIGN:  fprintf(f, " ^= "); break;
  case T_SHL_ASSIGN:  fprintf(f, " <<= "); break;
  case T_SHR_ASSIGN:  fprintf(f, " >>= "); break;
  }
}

void print_AsgnOp(enum AssignType op) {
  print_AsgnOp_File(stdout, op);
}

struct name_list *NLNil() { return NULL; }

struct name_list *NLCons(char *name, struct name_list *tail) {
  struct name_list *res = (struct name_list *)malloc(sizeof(struct name_list));
  res->head = name;
  res->tail = tail;
  return res;
}

void free_name_list(struct name_list *el) {
  if (el == NULL)
    return;
  struct name_list *tl = el->tail;
  free(el);
  free_name_list(tl);
}

