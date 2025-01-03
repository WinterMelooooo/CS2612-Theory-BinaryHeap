#ifndef PartialStmt_PRINTER_INCLUDED
#define PartialStmt_PRINTER_INCLUDED
#include "../CDef/PartialStmt.h"
#include "CexprPrinter.h"

void PrintAsgnOp(enum AssignType op);
void PrintPartialSimple(struct CSimpleCommand *comd, int end_of_line, struct environment * env);
void PrintPartialStmt(struct PartialStmt * stmt, struct environment * env);
void PrintPartialStmtList(struct PartialStmtList * stmts, struct environment * env);

#endif