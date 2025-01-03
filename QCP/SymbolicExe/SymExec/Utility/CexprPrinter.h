#ifndef CEXPR_PRINTER_INCLUDED
#define CEXPR_PRINTER_INCLUDED
#include "../../compiler/env.h"
#include "../CDef/Cexpr.h"

void PrintCexpr(struct Cexpr * expr, struct environment * env);
void PrintCexprFile(struct Cexpr * expr, struct environment * env, FILE *fp);
void PrintSimpleCtype(struct SimpleCtype * ty, struct environment * env);
void PrintSimpleCtypeFile(struct SimpleCtype * ty, struct environment * env, FILE *fp);
void PrintSimpleCtypeList(struct SimpleCtypeList * list, struct environment * env);
void PrintSimpleCtypeListFile(struct SimpleCtypeList * list, struct environment * env, FILE *fp);
void PrintSimpleCtypeNoEnv(struct SimpleCtype * ty);
void PrintSimpleCtypeNoEnvFile(struct SimpleCtype * ty, FILE *fp);
void PrintSimpleCtypeListNoEnv(struct SimpleCtypeList * list);
void PrintSimpleCtypeListNoEnvFile(struct SimpleCtypeList * list, FILE *fp);
#endif