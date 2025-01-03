#ifndef COQ_C_STATEMENT_PRINTER_H
#define COQ_C_STATEMENT_PRINTER_H

#include "../../compiler/lang.h"
#include "../../compiler/env.h"
#include "../AsrtDef/AssDef.h"
#include "../Utility/InnerAsrtCollector.h"

void CoqCStatementPrinter(struct cmd * cmd, int print_annotation, struct environment * env, FILE * fp);

#endif