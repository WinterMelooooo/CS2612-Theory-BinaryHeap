#ifndef __PATTERN_MATCH_H__
#define __PATTERN_MATCH_H__

#include "PatternExpr.h"
#include "PatternCType.h"
#include "PatternPolyType.h"
#include "PatternProp.h"
#include "PatternSep.h"
#include "../../AsrtDef/AssDef.h"
#include "../../../compiler/env.h"
#include "../Mapping/Mapping.h"

int matchCType(struct SimpleCtype * ctx,
                struct PatternCType * pat,
                struct charMapping * pat_mapping,
                struct environment * env);
int matchCTypeList(struct SimpleCtypeListNode * ctx,
                    struct PatternCTypeList * pat,
                    struct charMapping * pat_mapping,
                    struct environment * env);

struct SimpleCtype * instPatternCType(struct PatternCType * type,
                                      struct charMapping * mapping,
                                      struct environment * env);
struct SimpleCtypeList * instPatternCTypeList(struct PatternCTypeList * type_list,
                                              struct charMapping * mapping,
                                              struct environment * env);

int matchExprVal(struct ExprVal * ctx,
                 struct PatternExpr * pat,
                 struct charMapping * pat_mapping,
                 struct intMapping * exist_mapping,
                 struct environment * env);
int matchExprValList(struct ExprValListNode * cl,
                     struct PatternExprList * pl,
                     struct charMapping * pat_mapping,
                     struct intMapping * exist_mapping,
                     struct environment * env);

struct ExprVal * instPatternExpr(struct PatternExpr * expr,
                                 struct charMapping * pat_mapping,
                                 struct environment * env);
struct ExprValList * instPatternExprList(struct PatternExprList * expr_list,
                                         struct charMapping * pat_mapping,
                                         struct environment * env);

int matchPolyType(struct PolyType * ctx,
                  struct PatternPolyType * pat,
                  struct charMapping * pat_mapping,
                  struct intMapping * exist_mapping,
                  struct environment * env);
int matchPolyTypeList(struct PolyTypeListNode * cl,
                      struct PatternPolyTypeList * pl,
                      struct charMapping * pat_mapping,
                      struct intMapping * exist_mapping,
                      struct environment * env);

struct PolyType * instPatternPolyType(struct PatternPolyType * pat,
                                     struct charMapping * pat_mapping,
                                     struct environment * env);
struct PolyTypeList * instPatternPolyTypeList(struct PatternPolyTypeList * pl,
                                              struct charMapping * pat_mapping,
                                              struct environment * env);

int matchProposition(struct Proposition * ctx,
                     struct PatternProp * pat,
                     struct charMapping * pat_mapping,
                     struct intMapping * exist_mapping, 
                     struct environment * env);

struct Proposition * instPatternProp(struct PatternProp * prop,
                                     struct charMapping * pat_mapping,
                                     struct environment * env);

int matchSeparation(struct Separation * ctx,
                    struct PatternSep * pat,
                    struct charMapping * pat_mapping,
                    struct intMapping * exist_mapping, 
                    struct environment * env);

struct Separation * instPatternSep(struct PatternSep * sep,
                                   struct charMapping * pat_mapping,
                                   struct environment * env);

#endif

