#ifndef __STRATEGY_TYPE_INFERNECE_H__
#define __STRATEGY_TYPE_INFERNECE_H__

#include "../StrategyLibDef/StrategyLib.h"
#include "../PatternASTDef/PatternASTDef.h"
#include "../Mapping/Mapping.h"
#include "../../../compiler/env.h"
#include "../Util/Error.h"
#include "../../Paras.h"

struct StrategyLibRule * type_infer(struct StrategyLibRule * rule, struct environment * env);
struct PatternPolyType * type_infer_pattern_expr(struct PatternExpr * expr, struct charMapping * tm, struct environment * env);

#endif
