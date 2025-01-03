#ifndef PTRANS_H
#define PTRANS_H

#include "env.h"
#include "plang.h"
#include "../SymExec/CDef/PartialStmt.h"

void trans(struct partial_program *s, struct environment *env,
           void (*k_func_begin)(struct func_info *info, struct environment *env),
           void (*k_partial_statement)(struct PartialStmt *p, struct environment *env),
           void (*k_func_end)(struct func_info *info, struct environment *env));

#endif
