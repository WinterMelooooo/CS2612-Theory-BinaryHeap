#ifndef __STRATEGY_LIB_H__
#define __STRATEGY_LIB_H__

#include <string.h>
#include "../../AsrtDef/AssDef.h"
#include "../PatternASTDef/PatternASTDef.h"
#include "../Util/Error.h"
#include "../Mapping/Mapping.h"
#include "../../Utility/LogicNameManager.h"
#include "../../Utility/InnerAsrtPrinter.h"
#include "../../Trans/PropToSmtPropTrans.h"
#include "../Soundness/VarList.h"
#include "StrategyLibRule.h"
#include "../../Paras.h"

struct StrategyLibRuleList {
    struct StrategyLibRule * rule;
    struct StrategyLibRuleList * next;
};

struct StrategyLibRuleList * initStrategyLibRuleList(struct StrategyLibRule * rule, struct StrategyLibRuleList * next);
void finiStrategyLibRuleList(struct StrategyLibRuleList * head);

struct StrategyLibRuleListCell {
    struct StrategyLibRuleList * head;
    struct StrategyLibRuleList * tail;
};

struct StrategyLibRuleListCell * initStrategyLibRuleListCell();
void insertStrategyLibRuleListCell(struct StrategyLibRuleListCell * cell, struct StrategyLibRule * rule);
void finiStrategyLibRuleListCell(struct StrategyLibRuleListCell * cell);

struct StrategyLib {
    struct StrategyLibRuleListCell * rules[STRATEGY_LIB_MAX_PRIORITY];
};

struct StrategyLib * initStrategyLib();
struct StrategyLib * addStrategyLibRule(struct StrategyLib * lib, struct StrategyLibRule * rule);
void finiStrategyLib(struct StrategyLib * lib);

int matchStrategyLibRule(struct StrategyLibRule * rule, struct Assertion * pre, struct Assertion * post,
                         struct intMapping * left_exist_mapping, struct intMapping * right_exist_mapping, struct environment * env);
int matchStrategyLib(struct StrategyLib * lib, struct Assertion * pre, struct Assertion * post,
                     struct intMapping * left_exist_mapping, struct intMapping * right_exist_mapping, struct environment * env);

#endif