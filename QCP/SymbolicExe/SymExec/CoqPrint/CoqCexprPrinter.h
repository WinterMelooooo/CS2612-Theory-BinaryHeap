#ifndef COQ_CEXPR_PRINTER_H
#define COQ_CEXPR_PRINTER_H

#include "../CDef/Cexpr.h"

void CoqUnOpTypePrinter(enum UnOpType op, FILE * fp);

void CoqBinOpTypePrinter(enum BinOpType op, FILE * fp);

void CoqCexprPrinter(struct Cexpr * expr, struct environment * env, FILE * fp);

void CoqASTExprPrinter(struct expr * expr, struct environment * env, FILE * fp);

#endif // COQ_CEXPR_PRINTER_H