#ifndef EXPRTRNAS_INCLUDED
#define EXPRTRANS_INCLUDED
#include "../CDef/PartialStmt.h"
#include "../../compiler/lang.h"
#include "../../compiler/env.h"

struct VirtArg * VirtArgTrans(struct virt_arg * ori, struct environment * env);
struct Cexpr * PS_ExprTrans(struct expr * origin, struct environment * env);

#endif
