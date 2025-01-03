#ifndef __ASSERTION_UNIFY_H__
#define __ASSERTION_UNIFY_H__

#include "../../AsrtDef/AssDef.h"
#include "../Mapping/Mapping.h"
#include "../../SymExec/FuncCall.h"
#include "../../Paras.h"
#include "../../Utility/InnerAsrtPrinter.h"

struct EntailRetType * asrt_unify(struct Assertion * pre, struct Assertion * post, struct environment * env);

#endif