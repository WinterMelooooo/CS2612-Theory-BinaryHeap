#ifndef COQ_INNER_ASRT_PRINTER_H
#define COQ_INNER_ASRT_PRINTER_H

#include "../../compiler/env.h"
#include "../AsrtDef/AssDef.h"
#include "../SymExec/StateDef.h"

void CoqPropListPrinter(struct PropList * prop_list, struct environment * env, FILE * fp);

void CoqInnerAsrtPrinter(struct Assertion * asrt, struct environment * env, FILE * fp);

void CoqInnerAsrtListPrinter(struct AsrtList * asrt, struct environment * env, FILE * fp);

void CoqFuncRetTypePrinter(struct FuncRetType * ret, struct environment * env, FILE * fp);

void CoqExecPostPrinter(int id, struct FuncRetType * ret, struct environment * env, FILE * fp);

#endif // COQ_INNER_ASRT_PRINTER_H