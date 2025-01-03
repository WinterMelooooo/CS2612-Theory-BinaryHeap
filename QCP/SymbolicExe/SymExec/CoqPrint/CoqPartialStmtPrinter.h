#ifndef COQ_PARTIAL_STMT_PRINTER_H
#define COQ_PARTIAL_STMT_PRINTER_H

#include "../CDef/PartialStmt.h"

void CoqPartialStmtPrinter(struct PartialStmt* partialStmt, struct environment * env, FILE * fp);

void CoqPartialStmtListPrinter(int id, struct PartialStmtList * stmt_list, struct environment * env, FILE * fp);

void CoqPreConditionPrinter(int id, struct AsrtList * precond, struct environment * env, FILE * fp);

void CoqPostConditionPrinter(int id, struct AsrtList * postcond, struct environment * env, FILE * fp);

#endif // COQ_PARTIAL_STMT_PRINTER_H