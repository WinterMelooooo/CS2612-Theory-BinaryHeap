#ifndef __STRATEGY_LIB_RULE_H__
#define __STRATEGY_LIB_RULE_H__

#include "../PatternASTDef/PatternASTDef.h"
#include "../Mapping/Mapping.h"
#include "../Util/Error.h"
#include "../Soundness/VarList.h"
#include <stdlib.h>

enum StrategyLibPatternType {
    STRATEGY_LIB_PATTERN_PROP,
    STRATEGY_LIB_PATTERN_SEP
};

enum StrategyLibActionType {
    STRATEGY_LIB_ACTION_DEL_LEFT,
    STRATEGY_LIB_ACTION_DEL_RIGHT,

    STRATEGY_LIB_ACTION_ADD_LEFT,
    STRATEGY_LIB_ACTION_ADD_RIGHT,

    STRATEGY_LIB_ACTION_ADD_LEFT_EXIST,
    STRATEGY_LIB_ACTION_ADD_RIGHT_EXIST,

    STRATEGY_LIB_ACTION_INST,
    STRATEGY_LIB_ACTION_SUBST
};

enum StrategyLibCheckType {
    STRATEGY_LIB_CHECK_ABSENSE,
    STRATEGY_LIB_CHECK_INFER
};

struct StrategyLibPattern {
    enum StrategyLibPatternType ty;
    union {
        struct PatternProp * prop;
        struct PatternSep * sep;
    } pat;
};

struct StrategyLibPattern * initStrategyLibPatternProp(struct PatternProp * prop);
struct StrategyLibPattern * initStrategyLibPatternSep(struct PatternSep * sep);
void finiStrategyLibPattern(struct StrategyLibPattern * pat);

struct StrategyLibPatternList {
    struct StrategyLibPattern * pat;
    struct StrategyLibPatternList * next;
};

struct StrategyLibPatternList * initStrategyLibPatternList(struct StrategyLibPattern * pat, struct StrategyLibPatternList * next);
struct StrategyLibPatternList * appendStrategyLibPatternList(struct StrategyLibPatternList * a, struct StrategyLibPatternList * b);
void finiStrategyLibPatternList(struct StrategyLibPatternList * head);

struct StrategyLibPatternLList {
    int pos, left;
    struct StrategyLibPatternList * list;
    struct StrategyLibPatternLList * next;
};

struct StrategyLibPatternLList * initStrategyLibPatternLList(struct StrategyLibPatternList * list, struct StrategyLibPatternLList * next, int pos, int left);
void finiStrategyLibPatternLList(struct StrategyLibPatternLList * head);

struct StrategyLibActionMapping {
    char * var;
    struct PatternExpr * expr;
};

struct StrategyLibAction {
    enum StrategyLibActionType ty;
    union {
        // for DEL_LEFT || DEL_RIGHT
        int pos;
        // for ADD_LEFT || ADD_RIGHT
        struct StrategyLibPattern * expr;
        // for ADD_LEFT_EXIST || ADD_RIGHT_EXIST
        struct VarType * var;
        // for INST || SUBST
        struct StrategyLibActionMapping * mapping;
    } data;
};

struct StrategyLibAction * initStrategyLibActionDelLeft(int pos);
struct StrategyLibAction * initStrategyLibActionDelRight(int pos);
struct StrategyLibAction * initStrategyLibActionAddLeft(struct StrategyLibPattern * expr);
struct StrategyLibAction * initStrategyLibActionAddRight(struct StrategyLibPattern * expr);
struct StrategyLibAction * initStrategyLibActionAddLeftExist(struct VarType * var);
struct StrategyLibAction * initStrategyLibActionAddRightExist(struct VarType * var);
struct StrategyLibAction * initStrategyLibActionInst(char * var, struct PatternExpr * expr);
struct StrategyLibAction * initStrategyLibActionSubst(char * var, struct PatternExpr * expr);
void finiStrategyLibAction(struct StrategyLibAction * action);

struct StrategyLibActionList {
    struct StrategyLibAction * action;
    struct StrategyLibActionList * next;
};

struct StrategyLibActionList * initStrategyLibActionList(struct StrategyLibAction * action, struct StrategyLibActionList * next);
void finiStrategyLibActionList(struct StrategyLibActionList * head);

struct StrategyLibCheck {
    enum StrategyLibCheckType ty;
    union {
        // for ABSENSE || INFER
        struct PatternProp * prop;
    } data;
};

struct StrategyLibCheck * initStrategyLibCheckAbsense(struct PatternProp * prop);
struct StrategyLibCheck * initStrategyLibCheckInfer(struct PatternProp * prop);
void finiStrategyLibCheck(struct StrategyLibCheck * check);

struct StrategyLibCheckList {
    struct StrategyLibCheck * check;
    struct StrategyLibCheckList * next;
};

struct StrategyLibCheckList * initStrategyLibCheckList(struct StrategyLibCheck * check, struct StrategyLibCheckList * next);
void finiStrategyLibCheckList(struct StrategyLibCheckList * head);

struct StrategyLibRule {
    int cnt, priority, id;
    char * filename;
    struct StrategyLibPatternLList * pats;
    struct StrategyLibActionList * actions;
    struct StrategyLibCheckList * checks;
    struct charMapping * type_mapping;
};

struct StrategyLibRule * initStrategyLibRule(int id, int priority, char * filename, struct StrategyLibPatternLList * pats, struct StrategyLibActionList * actions, struct StrategyLibCheckList * checks,struct charMapping * type_mapping);
void finiStrategyLibRule(struct StrategyLibRule * rule);

#endif