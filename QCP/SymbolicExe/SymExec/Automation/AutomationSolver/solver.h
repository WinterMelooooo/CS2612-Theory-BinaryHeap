#ifndef __SOLVER_H__
#define __SOLVER_H__

#include "LocalMatching.h"
#include "../../AsrtDef/AssDef.h"
#include "../../../compiler/env.h"
#include "../StrategyLibDef/StrategyLib.h"
// #include "../StrategyLibDef/ListStrategyLib.h"
// #include "../StrategyLibDef/PureStrategyLib.h"
#include "../../SymExec/FuncCall.h"
#include "../../Utility/InnerAsrtPrinter.h"
#include "../../Paras.h"

struct EntailRetType * solve(struct Assertion * pre, struct Assertion * post, struct StrategyLib * lib, struct environment * env);
// struct EntailRetType * list_solve(struct Assertion * pre, struct Assertion * post, struct environment * env);

#endif