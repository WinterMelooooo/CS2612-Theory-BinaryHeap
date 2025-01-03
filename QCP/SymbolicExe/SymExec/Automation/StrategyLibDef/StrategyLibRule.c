#include "StrategyLibRule.h"

struct StrategyLibPattern * initStrategyLibPatternProp(struct PatternProp * prop) {
    struct StrategyLibPattern * ret = malloc(sizeof(struct StrategyLibPattern));
    ret->ty = STRATEGY_LIB_PATTERN_PROP;
    ret->pat.prop = prop;
    return ret;
}

struct StrategyLibPattern * initStrategyLibPatternSep(struct PatternSep * sep) {
    struct StrategyLibPattern * ret = malloc(sizeof(struct StrategyLibPattern));
    ret->ty = STRATEGY_LIB_PATTERN_SEP;
    ret->pat.sep = sep;
    return ret;
}

void finiStrategyLibPattern(struct StrategyLibPattern * pat) {
    switch (pat->ty) {
    case STRATEGY_LIB_PATTERN_PROP: {
        finiPatternProp(pat->pat.prop);
        break;
    }
    case STRATEGY_LIB_PATTERN_SEP: {
        finiPatternSep(pat->pat.sep);
        break;
    }
    default: {
        ERROR("Not implemented in finiStrategyLibPattern()");
    }
    }
    free(pat);
}

struct StrategyLibPatternList * initStrategyLibPatternList(struct StrategyLibPattern * pat, struct StrategyLibPatternList * next) {
    struct StrategyLibPatternList * cell = malloc(sizeof(struct StrategyLibPatternList));
    cell->pat = pat;
    cell->next = next;
    return cell;
}

struct StrategyLibPatternList * appendStrategyLibPatternList(struct StrategyLibPatternList * a, struct StrategyLibPatternList * b) {
    if (a == NULL) return b;

    a->next = appendStrategyLibPatternList(a->next, b);
    return a;
}

void finiStrategyLibPatternList(struct StrategyLibPatternList * head) {
    if (head == NULL) return;
    finiStrategyLibPattern(head->pat);
    finiStrategyLibPatternList(head->next);
    free(head);
}

struct StrategyLibPatternLList * initStrategyLibPatternLList(struct StrategyLibPatternList * list, struct StrategyLibPatternLList * next,int pos, int left) {
    struct StrategyLibPatternLList * cell = malloc(sizeof(struct StrategyLibPatternLList));
    cell->pos = pos, cell->left = left;
    cell->list = list;
    cell->next = next;
    return cell;
}

void finiStrategyLibPatternLList(struct StrategyLibPatternLList * head) {
    if (head == NULL) return;
    finiStrategyLibPatternList(head->list);
    finiStrategyLibPatternLList(head->next);
    free(head);
}

struct StrategyLibAction * initStrategyLibActionDelLeft(int pos) {
    struct StrategyLibAction * ret = malloc(sizeof(struct StrategyLibAction));
    ret->ty = STRATEGY_LIB_ACTION_DEL_LEFT;
    ret->data.pos = pos;
    return ret;
}

struct StrategyLibAction * initStrategyLibActionDelRight(int pos) {
    struct StrategyLibAction * ret = malloc(sizeof(struct StrategyLibAction));
    ret->ty = STRATEGY_LIB_ACTION_DEL_RIGHT;
    ret->data.pos = pos;
    return ret;
}

struct StrategyLibAction * initStrategyLibActionAddLeft(struct StrategyLibPattern * expr) {
    struct StrategyLibAction * ret = malloc(sizeof(struct StrategyLibAction));
    ret->ty = STRATEGY_LIB_ACTION_ADD_LEFT;
    ret->data.expr = expr;
    return ret;
}

struct StrategyLibAction * initStrategyLibActionAddRight(struct StrategyLibPattern * expr) {
    struct StrategyLibAction * ret = malloc(sizeof(struct StrategyLibAction));
    ret->ty = STRATEGY_LIB_ACTION_ADD_RIGHT;
    ret->data.expr = expr;
    return ret;
}

struct StrategyLibAction * initStrategyLibActionAddLeftExist(struct VarType * var) {
    struct StrategyLibAction * ret = malloc(sizeof(struct StrategyLibAction));
    ret->ty = STRATEGY_LIB_ACTION_ADD_LEFT_EXIST;
    ret->data.var = var;
    return ret;
}

struct StrategyLibAction * initStrategyLibActionAddRightExist(struct VarType * var) {
    struct StrategyLibAction * ret = malloc(sizeof(struct StrategyLibAction));
    ret->ty = STRATEGY_LIB_ACTION_ADD_RIGHT_EXIST;
    ret->data.var = var;
    return ret;
}

struct StrategyLibAction * initStrategyLibActionInst(char * var, struct PatternExpr * expr) {
    struct StrategyLibAction * ret = malloc(sizeof(struct StrategyLibAction));
    ret->ty = STRATEGY_LIB_ACTION_INST;
    ret->data.mapping = malloc(sizeof(struct StrategyLibActionMapping));
    ret->data.mapping->var = var;
    ret->data.mapping->expr = expr;
    return ret;
}

struct StrategyLibAction * initStrategyLibActionSubst(char * var, struct PatternExpr * expr) {
    struct StrategyLibAction * ret = malloc(sizeof(struct StrategyLibAction));
    ret->ty = STRATEGY_LIB_ACTION_SUBST;
    ret->data.mapping = malloc(sizeof(struct StrategyLibActionMapping));
    ret->data.mapping->var = var;
    ret->data.mapping->expr = expr;
    return ret;
}

void finiStrategyLibAction(struct StrategyLibAction * action) {
    switch (action->ty) {
    case STRATEGY_LIB_ACTION_DEL_LEFT:
    case STRATEGY_LIB_ACTION_DEL_RIGHT: {
        break;
    }
    case STRATEGY_LIB_ACTION_ADD_LEFT:
    case STRATEGY_LIB_ACTION_ADD_RIGHT: {
        finiStrategyLibPattern(action->data.expr);
        break;
    }
    case STRATEGY_LIB_ACTION_ADD_LEFT_EXIST:
    case STRATEGY_LIB_ACTION_ADD_RIGHT_EXIST: {
        finiVarType(action->data.var);
        break;
    }
    case STRATEGY_LIB_ACTION_INST:
    case STRATEGY_LIB_ACTION_SUBST: {
        free(action->data.mapping->var);
        finiPatternExpr(action->data.mapping->expr);
        free(action->data.mapping);
        break;
    }
    default: {
        ERROR("Not implemented in finiStrategyLibAction()");
    }
    }
    free(action);
}


struct StrategyLibActionList * initStrategyLibActionList(struct StrategyLibAction * action,
                                                         struct StrategyLibActionList * next) {
    struct StrategyLibActionList * cell = malloc(sizeof(struct StrategyLibActionList));
    cell->action = action;
    cell->next = next;
    return cell;
}

void finiStrategyLibActionList(struct StrategyLibActionList * head) {
    if (head == NULL) return;
    finiStrategyLibAction(head->action);
    finiStrategyLibActionList(head->next);
    free(head);
}

struct StrategyLibCheck * initStrategyLibCheckAbsense(struct PatternProp * prop) {
    struct StrategyLibCheck * ret = malloc(sizeof(struct StrategyLibCheck));
    ret->ty = STRATEGY_LIB_CHECK_ABSENSE;
    ret->data.prop = prop;
    return ret;
}

struct StrategyLibCheck * initStrategyLibCheckInfer(struct PatternProp * prop) {
    struct StrategyLibCheck * ret = malloc(sizeof(struct StrategyLibCheck));
    ret->ty = STRATEGY_LIB_CHECK_INFER;
    ret->data.prop = prop;
    return ret;
}

void finiStrategyLibCheck(struct StrategyLibCheck * check) {
    switch (check->ty) {
    case STRATEGY_LIB_CHECK_ABSENSE:
    case STRATEGY_LIB_CHECK_INFER: {
        finiPatternProp(check->data.prop);
        break;
    }
    default: {
        ERROR("Not implemented in finiStrategyLibCheck()");
    }
    }
    free(check);
}

struct StrategyLibCheckList * initStrategyLibCheckList(struct StrategyLibCheck * check, struct StrategyLibCheckList * next) {
    struct StrategyLibCheckList * cell = malloc(sizeof(struct StrategyLibCheckList));
    cell->check = check;
    cell->next = next;
    return cell;
}

void finiStrategyLibCheckList(struct StrategyLibCheckList * head) {
    if (head == NULL) return;
    finiStrategyLibCheck(head->check);
    finiStrategyLibCheckList(head->next);
    free(head);
}

struct StrategyLibRule * initStrategyLibRule(int id, int priority, char * filename, struct StrategyLibPatternLList * pats, struct StrategyLibActionList * actions, struct StrategyLibCheckList * checks,struct charMapping * mapping) {
    struct StrategyLibRule * ret = malloc(sizeof(struct StrategyLibRule));
    int cnt = 0;
    ret->id = id;
    ret->priority = priority;
    ret->filename = filename;
    ret->pats = pats;
    for (struct StrategyLibPatternLList * cur = pats; cur != NULL; cur = cur->next)
        cnt++;
    ret->actions = actions;
    ret->checks = checks;
    ret->cnt = cnt;
    ret->type_mapping = mapping;
    return ret;
}

void finiStrategyLibRule(struct StrategyLibRule * rule) {
    finiStrategyLibPatternLList(rule->pats);
    finiStrategyLibActionList(rule->actions);
    finiStrategyLibCheckList(rule->checks);
    finiCharMapping(rule->type_mapping);
    free(rule->filename);
    free(rule);
}