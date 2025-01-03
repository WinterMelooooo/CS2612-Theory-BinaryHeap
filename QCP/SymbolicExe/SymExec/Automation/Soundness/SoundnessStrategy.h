#ifndef __SOUNDNESS_STRATEGY_H__
#define __SOUNDNESS_STRATEGY_H__

#include "../StrategyLibDef/StrategyLib.h"
#include "RamifyDef.h"
#include "PatternPrintLib.h"
#include <stdlib.h>
#include <stdio.h>

void print_strategy_defs(struct StrategyLibRule * rule, FILE * fp, struct environment * env);
void print_strategy_lemmas(struct StrategyLibRule * rule, FILE * fp);
void print_strategy_soundness(struct StrategyLib * lib, FILE * defs_fp, FILE * proofs_fp, FILE * check_fp, char * filename, struct environment * env);

#endif