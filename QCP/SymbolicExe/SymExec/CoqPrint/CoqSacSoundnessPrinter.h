#ifndef COQ_SAC_SOUNDNESS_PRINTER_H
#define COQ_SAC_SOUNDNESS_PRINTER_H

#include <stdio.h>
#include "../AsrtDef/AssDef.h"
#include "../../compiler/env.h"

void PrintWitnessHeader(FILE *fp);
void PrintAnnotsHeader(FILE *fp);
void PrintAnnots(FILE *fp);
void PrintHeaderExecSoundness(FILE * fp);
void PrintTransSoundness(int func_count, FILE *fp);
void PrintExecCorrectness(FILE *fp, struct environment *env);
void PrintHeaderMain(FILE *fp);
void PrintHeaderExecSoundness(FILE * fp);
void PrintTransSoundness(int func_count, FILE *fp);
void PrintExecCorrectness(FILE *fp, struct environment *env);

#endif