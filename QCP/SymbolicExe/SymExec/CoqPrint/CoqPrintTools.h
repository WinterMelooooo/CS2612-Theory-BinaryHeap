#ifndef COQ_PRINT_TOOLS_H
#define COQ_PRINT_TOOLS_H

#include "../AsrtDef/AssDef.h"
#include "../../compiler/env.h"

struct CoqAnnot {
    char *name;
    int id;
    int is_var;
    struct CoqAnnot *next;
};

struct CoqAnnot *CoqAnnotNil();

struct CoqAnnot *CoqAnnotCons(char *name, int id, int is_var, struct CoqAnnot *list);

struct CoqAnnot *CoqAnnotFind(char *name, struct CoqAnnot *list);

int CoqCollectAnnots(char *name, int id, int is_var);

void CoqPrintCollectedAnnots(struct environment * env, FILE * fp);

int CoqPrintRawAnnots(char *name, int id, int is_var, FILE *fp);

void CoqPrintIdent(int id, FILE * fp);

void CoqPrintVarName(char *name, int id, FILE * fp);

void CoqPrintIdent(int id, FILE * fp);

void CoqSignednessPrinter(enum Signedness s, FILE * fp);

void CoqSimpleCtypePrinter(struct SimpleCtype * type, struct environment * env, FILE * fp);

#endif // COQ_PRINT_TOOLS_H