#ifndef __RAMIFY_DEF_H__
#define __RAMIFY_DEF_H__

#include "../../AsrtDef/AssDef.h"
#include "../PatternASTDef/PatternASTDef.h"
#include "../StrategyLibDef/StrategyLibRule.h"
#include "../Mapping/Mapping.h"
#include "../Util/Error.h"
#include "VarList.h"
#include "PatternPrintLib.h"
#include <stdlib.h>

/* owns resource */
struct RamifiedCondition {
    struct VarList * vl_forall, * vl_all, * vl_exists;
    struct PatternPropLList * sc, * a, * b, * c, * d;
    struct PatternSepLList * A, * B, * C, * D;
};

struct VarList * getVarListPatternExpr(struct PatternExpr * expr, struct charMapping * type_mapping, struct environment * env);
struct VarList * getVarListPatternExprList(struct PatternExprList * el, struct charMapping * type_mapping, struct environment * env);
struct VarList * getVarListPatternPolyType(struct PatternPolyType * type);
struct VarList * getVarListPatternPolyTypeList(struct PatternPolyTypeList * type);
struct VarList * getVarListPatternProp(struct PatternProp * prop, struct charMapping * type_mapping, struct environment * env);
struct VarList * getVarListPatternPropList(struct PatternPropList * pl, struct charMapping * type_mapping, struct environment * env);
struct VarList * getVarListPatternPropLList(struct PatternPropLList * pl, struct charMapping * type_mapping, struct VarList * fallback, struct environment * env);
struct VarList * getVarListPatternSep(struct PatternSep * sep, struct charMapping * type_mapping, struct environment * env);
struct VarList * getVarListPatternSepList(struct PatternSepList * sl, struct charMapping * type_mapping, struct environment * env);
struct VarList * getVarListPatternSepLList(struct PatternSepLList * sl, struct charMapping * type_mapping, struct VarList * fallback, struct environment * env);
struct VarList * getVarListPatternCType(struct PatternCType * type);

struct RamifiedCondition * gen_rc(struct StrategyLibRule * rule, struct environment * env);
void print_rc(FILE * fp, struct RamifiedCondition * rc, struct charMapping * type_mapping, struct environment * env);
void fini_rc(struct RamifiedCondition * rc);


#endif