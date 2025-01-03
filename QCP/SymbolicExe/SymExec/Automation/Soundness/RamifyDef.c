#include "RamifyDef.h"

struct VarList * getVarListPatternExpr(struct PatternExpr * expr, struct charMapping * type_mapping, struct environment * env) {
    if (expr == NULL) return NULL;
    switch (expr->ty) {
    case PATTERN_EXPR_GVAR: 
    case PATTERN_EXPR_CONST: {
        return NULL;
    }
    case PATTERN_EXPR_VAR:
    case PATTERN_EXPR_EVAR:
    case PATTERN_EXPR_SVAR: {
        struct mappingValue * type = charMappingFind(expr->data.var, type_mapping);
        if (type == NULL) {
            return initVarList(initVarType(strdup(expr->data.var), NULL), NULL);
        }
        struct VarList * ret = initVarList(initVarType(strdup(expr->data.var), PatternPolyTypeDeepCopy(type->val)), NULL);
        ret = VarListMerge(ret, getVarListPatternPolyType(type->val));
        return ret;
    }
    case PATTERN_EXPR_FIELD: {
        return getVarListPatternExpr(expr->data.field->expr, type_mapping, env);
    }
    case PATTERN_EXPR_APP: {
        return VarListMerge(getVarListPatternPolyTypeList(expr->data.app->type_list),
                            getVarListPatternExprList(expr->data.app->expr_list, type_mapping, env));
    }
    case PATTERN_EXPR_UNOP: {
        return getVarListPatternExpr(expr->data.unop->expr, type_mapping, env);
    }
    case PATTERN_EXPR_BINOP: {
        return VarListMerge(getVarListPatternExpr(expr->data.binop->left, type_mapping, env),
                            getVarListPatternExpr(expr->data.binop->right, type_mapping, env));
    }
    case PATTERN_EXPR_ARRIDX: {
        struct PatternPolyType * type = type_infer_pattern_expr(expr->data.arridx->array, type_mapping, env);
        if (type->ty != PATTERN_POLY_APP || strcmp(type->data.app->func, "list")) {
            fprintf(stderr, "ERROR: Type of ");
            printPatternExpr(expr->data.arridx->array, stderr, type_mapping, env);
            fprintf(stderr, " is ");
            PatternPolyTypePrint(stderr, type);
            fprintf(stderr, "\n");
            fprintf(stderr, "Expected type of form list_?A\n");
            ERROR("");
        }
        char * ts = PatternPolyTypeToChar(type->data.app->args->head);
        struct VarList * res = NULL;
        if (strcmp(ts, "Z") != 0) {
          char * var = malloc(10 + strlen(ts) + 1);
          sprintf(var, "__default_%s", ts);
          res = initVarList(initVarType(var, PatternPolyTypeDeepCopy(type->data.app->args->head)), NULL);
        }
        free(ts);
        PatternPolyTypeFree(type);
        return VarListMerge(res,
               VarListMerge(getVarListPatternExpr(expr->data.arridx->array, type_mapping, env),
                            getVarListPatternExpr(expr->data.arridx->index, type_mapping, env)));
    }
    case PATTERN_EXPR_SIZEOF: {
        return getVarListPatternCType(expr->data.sizeof_expr);
    }
    default: {
        ERROR("Not implemented in getVarListPatternExpr()");
    }
    }
}


struct VarList * getVarListPatternPolyType(struct PatternPolyType * type) {
    if (type == NULL) return NULL;
    switch (type->ty) {
    case PATTERN_POLY_CONST: {
        return NULL;
    }
    case PATTERN_POLY_VAR: {
        return initVarList(initVarType(strdup(type->data.var), initPatternPolyTypeConst(strdup("Type"))), NULL);
    }
    case PATTERN_POLY_APP: {
        return getVarListPatternPolyTypeList(type->data.app->args);
    }
    case PATTERN_POLY_ARROW: {
        return VarListMerge(getVarListPatternPolyType(type->data.arrow->left),
                            getVarListPatternPolyType(type->data.arrow->right));
    }
    default: {
        ERROR("getVarListPatternPolyType: unknown poly type");
    }
    }
}

struct VarList * getVarListPatternPolyTypeList(struct PatternPolyTypeList * type) {
    if (type == NULL) return NULL;
    struct VarList * vl1 = getVarListPatternPolyType(type->head);
    struct VarList * vl2 = getVarListPatternPolyTypeList(type->next);
    return VarListMerge(vl1, vl2);
}

struct VarList * getVarListPatternCType(struct PatternCType * type) {
    if (type == NULL) return NULL;
    switch (type->ty) {
    case PATTERN_CTYPE_VOID:
    case PATTERN_CTYPE_C8:
    case PATTERN_CTYPE_C16:
    case PATTERN_CTYPE_C32:
    case PATTERN_CTYPE_C64:
    case PATTERN_CTYPE_STRUCT:
    case PATTERN_CTYPE_UNION:
    case PATTERN_CTYPE_ENUM: {
        return NULL;
    }
    case PATTERN_CTYPE_PTR: {
        return getVarListPatternCType(type->data.tptr->type);
    }
    case PATTERN_CTYPE_ARR: {
        return getVarListPatternCType(type->data.tarr->type);
    }
    case PATTERN_CTYPE_VAR: {
        return initVarList(initVarType(strdup(type->data.var), NULL), NULL);
    }
    case PATTERN_CTYPE_FUNC: {
        ERROR("getVarListPatternCType: function type not supported");
        break;
    }
    default: {
        ERROR("getVarListPatternCType: unknown ctype type");
    }
    }
    return NULL;
}

struct VarList * getVarListPatternExprList(struct PatternExprList * el, struct charMapping * type_mapping, struct environment * env) {
    if (el == NULL) return NULL;
    struct VarList * vl1 = getVarListPatternExpr(el->expr, type_mapping, env);
    struct VarList * vl2 = getVarListPatternExprList(el->next, type_mapping, env);
    return VarListMerge(vl1, vl2);
}

struct VarList * getVarListPatternProp(struct PatternProp * prop, struct charMapping * type_mapping, struct environment * env) {
    if (prop == NULL) return NULL;
    switch (prop->ty) {
    case PATTERN_PROP_TRUE:
    case PATTERN_PROP_FALSE: {
        return NULL;
    }
    case PATTERN_PROP_UNOP: {
        return getVarListPatternProp(prop->data.unop->prop, type_mapping, env);
    }
    case PATTERN_PROP_BINOP: {
        return VarListMerge(getVarListPatternProp(prop->data.binop->left, type_mapping, env),
                            getVarListPatternProp(prop->data.binop->right, type_mapping, env));
    }
    case PATTERN_PROP_COMPARE: {
        return VarListMerge(getVarListPatternExpr(prop->data.comp->left, type_mapping, env),
                            getVarListPatternExpr(prop->data.comp->right, type_mapping, env));
    }
    case PATTERN_PROP_PRED: {
        return VarListMerge(getVarListPatternPolyTypeList(prop->data.pred->types),
                            getVarListPatternExprList(prop->data.pred->args, type_mapping, env));
    }
    case PATTERN_PROP_PATPRED: {
        struct VarList * ret = NULL;
        char * var = prop->data.ppred->var;
        struct mappingValue * mv = charMappingFind(var, type_mapping);
        if (mv == NULL) {
            ret = initVarList(initVarType(strdup(var), NULL), NULL);
        }
        else {
            ret = initVarList(initVarType(strdup(var), PatternPolyTypeDeepCopy(mv->val)), NULL);
            ret = VarListMerge(ret, getVarListPatternPolyType(mv->val));
        }
        return VarListMerge(ret, getVarListPatternExprList(prop->data.ppred->args, type_mapping, env));
    }
    default: {
        ERROR("getVarListPatternProp: unknown prop type");
    }
    }
}

struct VarList * getVarListPatternPropList(struct PatternPropList * pl, struct charMapping * type_mapping, struct environment * env) {
    if (pl == NULL) return NULL;
    struct VarList * vl1 = getVarListPatternProp(pl->head, type_mapping, env);
    struct VarList * vl2 = getVarListPatternPropList(pl->next, type_mapping, env);
    return VarListMerge(vl1, vl2);
}

struct VarList * getVarListPatternPropLList(struct PatternPropLList * pl, struct charMapping * type_mapping, struct VarList * fallback, struct environment * env) {
    if (pl == NULL) return fallback;
    struct VarList * vl1 = getVarListPatternPropList(pl->head, type_mapping, env);
    struct VarList * vl2 = getVarListPatternPropLList(pl->next, type_mapping, fallback, env);
    return VarListMerge(vl1, vl2);
}

struct VarList * getVarListPatternSep(struct PatternSep * sep, struct charMapping * type_mapping, struct environment * env) {
    if (sep == NULL) return NULL;
    switch (sep->ty) {
    case PATTERN_SEP_DATA_AT: {
        return VarListMerge(getVarListPatternExpr(sep->data.data_at->addr, type_mapping, env),
               VarListMerge(getVarListPatternCType(sep->data.data_at->ty),
                            getVarListPatternExpr(sep->data.data_at->data, type_mapping, env)));
    }
    case PATTERN_SEP_UNDEF: {
        return VarListMerge(getVarListPatternExpr(sep->data.undef_data_at->addr, type_mapping, env),
                            getVarListPatternCType(sep->data.undef_data_at->ty));
    }
    case PATTERN_SEP_ARR: {
        ERROR("getVarListPatternSep: array type not supported");
        break;
    }
    case PATTERN_SEP_PRED: {
        return VarListMerge(getVarListPatternPolyTypeList(sep->data.pred->types),
                            getVarListPatternExprList(sep->data.pred->args, type_mapping, env));
    }
    case PATTERN_SEP_PATPRED: {
        struct VarList * ret = NULL;
        char * var = sep->data.ppred->var;
        struct mappingValue * mv = charMappingFind(var, type_mapping);
        if (mv == NULL) {
            ret = initVarList(initVarType(strdup(var), NULL), NULL);
        }
        else {
            ret = initVarList(initVarType(strdup(var), PatternPolyTypeDeepCopy(mv->val)), NULL);
            ret = VarListMerge(ret, getVarListPatternPolyType(mv->val));
        }
        return VarListMerge(ret, getVarListPatternExprList(sep->data.ppred->args, type_mapping, env));
    }
    default: {
        ERROR("getVarListPatternSep: unknown sep type");
    }
    }
}

struct VarList * getVarListPatternSepList(struct PatternSepList * sl, struct charMapping * type_mapping, struct environment * env) {
    if (sl == NULL) return NULL;
    struct VarList * vl1 = getVarListPatternSep(sl->head, type_mapping, env);
    struct VarList * vl2 = getVarListPatternSepList(sl->next, type_mapping, env);
    return VarListMerge(vl1, vl2);
}

static int check(struct VarType * vt) {
    if (vt == NULL) return 0;
    if (vt->type == NULL) return 0;
    struct PatternPolyType * type = vt->type;
    if (type->ty == PATTERN_POLY_CONST && !strcmp(type->data.var, "Type")) return 1;
    return 0;
}

static struct VarList * rearrange(struct VarList * vl) {
    struct VarList * ret = NULL;
    for (struct VarList * cur = vl; cur != NULL; cur = cur->next) {
        if (!check(cur->head)) ret = initVarList(VarTypeDeepCopy(cur->head), ret);
    }
    for (struct VarList * cur = vl; cur != NULL; cur = cur->next) {
        if (check(cur->head)) ret = initVarList(VarTypeDeepCopy(cur->head), ret);
    }
    finiVarList(vl);
    return ret;
}

struct VarList * getVarListPatternSepLList(struct PatternSepLList * sl, struct charMapping * type_mapping, struct VarList * fallback, struct environment * env) {
    if (sl == NULL) return fallback;
    struct VarList * vl1 = getVarListPatternSepList(sl->head, type_mapping, env);
    struct VarList * vl2 = getVarListPatternSepLList(sl->next, type_mapping, fallback, env);
    return VarListMerge(vl1, vl2);
}

struct RamifiedCondition * gen_rc(struct StrategyLibRule * rule, struct environment * env) {
    struct RamifiedCondition * rc = malloc(sizeof(struct RamifiedCondition));
    rc->sc = rc->a = rc->b = rc->c = rc->d = NULL;
    rc->A = rc->B = rc->C = rc->D = NULL;
    rc->vl_exists = NULL;
    for (struct StrategyLibCheckList * cur = rule->checks; cur != NULL; cur = cur->next) {
        if (cur->check->ty == STRATEGY_LIB_CHECK_INFER) {
            rc->sc = initPatternPropLList(0, initPatternPropList(PatternPropDeepCopy(cur->check->data.prop), NULL), rc->sc);
        }
    }

    struct intMapping * vis = initIntMapping();
    struct intMapping * ast_mapping = initIntMapping();

    for (struct StrategyLibActionList * cur = rule->actions; cur != NULL; cur = cur->next) {
        if (cur->action->ty == STRATEGY_LIB_ACTION_DEL_LEFT || cur->action->ty == STRATEGY_LIB_ACTION_DEL_RIGHT) {
            int pos = cur->action->data.pos;
            intMappingInsert(pos, initPtrMappingValue(NULL), vis);
        }
    }

    for (struct StrategyLibPatternLList * cur = rule->pats; cur != NULL; cur = cur->next) {
        int ty = -1, left = cur->left, pos = cur->pos;
        intMappingInsert(pos, initPtrMappingValue(cur->list), ast_mapping);
        for (struct StrategyLibPatternList * icur = cur->list; icur != NULL; icur = icur->next) {
            if (icur->pat->ty == STRATEGY_LIB_PATTERN_PROP) {
                if (ty != 1) ty = 0; else ty = 2;
            }
            else {
                if (ty != 0) ty = 1; else ty = 2;
            }
        }
        if (ty == 2) {
            ERROR("Currently not supporting mixed sep & prop pattern types in || when generating soundness.");
        }
        if (left) {
            if (ty == 0) {
                struct PatternPropList * res = NULL;
                for (struct StrategyLibPatternList * icur = cur->list; icur != NULL; icur = icur->next) {
                    res = initPatternPropList(PatternPropDeepCopy(icur->pat->pat.prop), res);
                }
                if (PatternPropLListFind(rc->b, res) == 1) {
                    rc->b = PatternPropLListErase(rc->b, res);
                }
                else {
                    rc->a = initPatternPropLList(1, PatternPropListDeepCopy(res), rc->a);
                }
                rc->b = initPatternPropLList(1, res, rc->b);
            }
            else {
                struct PatternSepList * res = NULL;
                for (struct StrategyLibPatternList * icur = cur->list; icur != NULL; icur = icur->next) {
                    res = initPatternSepList(PatternSepDeepCopy(icur->pat->pat.sep), res);
                }
                if (PatternSepLListFind(rc->B, res) == 1) {
                    rc->B = PatternSepLListErase(rc->B, res);
                }
                else {
                    rc->A = initPatternSepLList(1, PatternSepListDeepCopy(res), rc->A);
                }
                rc->B = initPatternSepLList(1, res, rc->B);
            }
        } else {
            if (ty == 0) {
                struct PatternPropList * res = NULL;
                for (struct StrategyLibPatternList * icur = cur->list; icur != NULL; icur = icur->next) {
                    res = initPatternPropList(PatternPropDeepCopy(icur->pat->pat.prop), res);
                }
                if (PatternPropLListFind(rc->c, res) == 1) {
                    rc->c = PatternPropLListErase(rc->c, res);
                }
                else {
                    if (intMappingIn(pos, vis)) {
                        rc->d = initPatternPropLList(0, PatternPropListDeepCopy(res), rc->d);
                    }
                    else {
                        rc->d = initPatternPropLList(1, PatternPropListDeepCopy(res), rc->d);
                    }
                }
                rc->c = initPatternPropLList(1, res, rc->c);
            }
            else {
                struct PatternSepList * res = NULL;
                for (struct StrategyLibPatternList * icur = cur->list; icur != NULL; icur = icur->next) {
                    res = initPatternSepList(PatternSepDeepCopy(icur->pat->pat.sep), res);
                }
                if (PatternSepLListFind(rc->C, res) == 1) {
                    rc->C = PatternSepLListErase(rc->C, res);
                }
                else {
                    if (intMappingIn(pos, vis)) {
                        rc->D = initPatternSepLList(0, PatternSepListDeepCopy(res), rc->D);
                    }
                    else {
                        rc->D = initPatternSepLList(1, PatternSepListDeepCopy(res), rc->D);
                    }
                }
                rc->C = initPatternSepLList(1, res, rc->C);
            }
        }
    }

    for (struct StrategyLibActionList * cur = rule->actions; cur != NULL; cur = cur->next) {
        switch (cur->action->ty) {
        case STRATEGY_LIB_ACTION_DEL_LEFT: {
            int pos = cur->action->data.pos;
            struct StrategyLibPatternList * list = intMappingFind(pos, ast_mapping)->val;
            if (list->pat->ty == STRATEGY_LIB_PATTERN_PROP) {
                struct PatternPropList * res = NULL;
                for (struct StrategyLibPatternList * icur = list; icur != NULL; icur = icur->next) {
                    res = initPatternPropList(PatternPropDeepCopy(icur->pat->pat.prop), res);
                }
                if (PatternPropLListFind(rc->b, res) == 1) {
                    rc->b = PatternPropLListErase(rc->b, res);
                    finiPatternPropList(res);
                }
                else {
                    rc->a = initPatternPropLList(1, res, rc->a);
                }
            }
            else {
                struct PatternSepList * res = NULL;
                for (struct StrategyLibPatternList * icur = list; icur != NULL; icur = icur->next) {
                    res = initPatternSepList(PatternSepDeepCopy(icur->pat->pat.sep), res);
                }
                if (PatternSepLListFind(rc->B, res) == 1) {
                    rc->B = PatternSepLListErase(rc->B, res);
                    finiPatternSepList(res);
                }
                else {
                    rc->A = initPatternSepLList(1, res, rc->A);
                }
            }
            break;
        }
        case STRATEGY_LIB_ACTION_ADD_LEFT: {
            struct StrategyLibPattern * pat = cur->action->data.expr;
            if (pat->ty == STRATEGY_LIB_PATTERN_PROP) {
                rc->b = initPatternPropLList(1, initPatternPropList(PatternPropDeepCopy(pat->pat.prop), NULL), rc->b);
            }
            else {
                rc->B = initPatternSepLList(1, initPatternSepList(PatternSepDeepCopy(pat->pat.sep), NULL), rc->B);
            }
            break;
        }
        case STRATEGY_LIB_ACTION_ADD_RIGHT: {
            struct StrategyLibPattern * pat = cur->action->data.expr;
            if (pat->ty == STRATEGY_LIB_PATTERN_PROP) {
                rc->c = initPatternPropLList(1, initPatternPropList(PatternPropDeepCopy(pat->pat.prop), NULL), rc->c);
            }
            else {
                rc->C = initPatternSepLList(1, initPatternSepList(PatternSepDeepCopy(pat->pat.sep), NULL), rc->C);
            }
            break;
        }
        case STRATEGY_LIB_ACTION_DEL_RIGHT: {
            int pos = cur->action->data.pos;
            struct StrategyLibPatternList * list = intMappingFind(pos, ast_mapping)->val;
            if (list->pat->ty == STRATEGY_LIB_PATTERN_PROP) {
                struct PatternPropList * res = NULL;
                for (struct StrategyLibPatternList * icur = list; icur != NULL; icur = icur->next) {
                    res = initPatternPropList(PatternPropDeepCopy(icur->pat->pat.prop), res);
                }
                if (PatternPropLListFind(rc->c, res) == 1) {
                    rc->c = PatternPropLListErase(rc->c, res);
                    finiPatternPropList(res);
                }
                else {
                    rc->d = initPatternPropLList(0, res, rc->d);
                }
            }
            else {
                struct PatternSepList * res = NULL;
                for (struct StrategyLibPatternList * icur = list; icur != NULL; icur = icur->next) {
                    res = initPatternSepList(PatternSepDeepCopy(icur->pat->pat.sep), res);
                }
                if (PatternSepLListFind(rc->C, res) == 1) {
                    rc->C = PatternSepLListErase(rc->C, res);
                    finiPatternSepList(res);
                }
                else {
                    rc->D = initPatternSepLList(0, res, rc->D);
                }
            }
            break;
        }
        case STRATEGY_LIB_ACTION_ADD_LEFT_EXIST: {
            rc->vl_exists = initVarList(VarTypeDeepCopy(cur->action->data.var), rc->vl_exists);
            break;
        }
        default : { break; }
        }
    }
    finiIntMapping(vis);
    finiIntMapping(ast_mapping);
    struct VarList * vl0 = getVarListPatternPropLList(rc->sc, rule->type_mapping,
                             getVarListPatternPropLList(rc->a, rule->type_mapping,
                             getVarListPatternPropLList(rc->b, rule->type_mapping, NULL, env), env), env);
    struct VarList * vl1 = getVarListPatternSepLList(rc->A, rule->type_mapping,
                             getVarListPatternSepLList(rc->B, rule->type_mapping, NULL, env), env);
    struct VarList * vl2 = VarListMerge(vl0, vl1);

    struct VarList * vl3 = getVarListPatternPropLList(rc->c, rule->type_mapping,
                             getVarListPatternPropLList(rc->d, rule->type_mapping, NULL, env), env);
    struct VarList * vl4 = getVarListPatternSepLList(rc->C, rule->type_mapping,
                             getVarListPatternSepLList(rc->D, rule->type_mapping, NULL, env), env);
    struct VarList * vl5 = VarListMerge(vl3, vl4);

    // if (!strcmp(rule->filename, "poly_sll") && rule->id == 4) {
    //     for (struct charMappingNode * cur = rule->type_mapping->head; cur != NULL; cur = cur->next) {
    //         if (cur->val) printf("%s : !", cur->var);
    //     }
    // }

    rc->vl_forall = VarListMinus(vl2, rc->vl_exists);
    struct VarList * vl6 = VarListMerge(vl2, VarListDeepCopy(rc->vl_exists));
    rc->vl_all = VarListMinus(vl5, vl6);
    finiVarList(vl5);
    finiVarList(vl6);

    rc->vl_forall = rearrange(rc->vl_forall);
    rc->vl_exists = rearrange(rc->vl_exists);
    rc->vl_all = rearrange(rc->vl_all);
    return rc;
}

void print_rc(FILE * fp, struct RamifiedCondition * rc, struct charMapping * type_mapping, struct environment * env) {
    int num_tabs = 1;
    if (rc->vl_forall) {
        print_tabs(num_tabs, fp);
        fprintf(fp, "forall");
        for (struct VarList * cur = rc->vl_forall; cur != NULL; cur = cur->next) {
            if (cur->head->type == NULL) 
                fprintf(fp, " %s", cur->head->name);
        }
        for (struct VarList * cur = rc->vl_forall; cur != NULL; cur = cur->next) {
            if (cur->head->type) {
                fprintf(fp, " (%s : ", cur->head->name);
                printPatternPolyType(cur->head->type, fp);
                fprintf(fp, ")");
            }
        }
        fprintf(fp, ",\n");
        num_tabs += 1;
    }

    struct PatternPropLList * temp = PatternPropLListApp(PatternPropLListDeepCopy(rc->sc), PatternPropLListDeepCopy(rc->a));

    printPatternPropLList(temp, fp, num_tabs, type_mapping, env);
    finiPatternPropLList(temp);
    fprintf(fp, " &&\n");
    printPatternSepLList(rc->A, fp, num_tabs, type_mapping, env);

    fprintf(fp, "\n");
    print_tabs(num_tabs, fp);
    fprintf(fp, "|--\n");

    if (rc->vl_exists) {
        print_tabs(num_tabs, fp);
        fprintf(fp, "EX");
        for (struct VarList * cur = rc->vl_exists; cur != NULL; cur = cur->next) {
            if (cur->head->type == NULL) 
                fprintf(fp, " %s", cur->head->name);
        }
        for (struct VarList * cur = rc->vl_exists; cur != NULL; cur = cur->next) {
            if (cur->head->type) {
                fprintf(fp, " (%s : ", cur->head->name);
                printPatternPolyType(cur->head->type, fp);
                fprintf(fp, ")");
            }
        }
        fprintf(fp, ",\n");
        num_tabs += 1;
    }

    print_tabs(num_tabs, fp);
    fprintf(fp, "(\n");
    printPatternPropLList(rc->b, fp, num_tabs, type_mapping, env);
    fprintf(fp, " &&\n");
    printPatternSepLList(rc->B, fp, num_tabs, type_mapping, env);
    fprintf(fp, "\n");
    print_tabs(num_tabs, fp);
    fprintf(fp, ") ** (\n");

    if (rc->vl_all) {
        print_tabs(num_tabs, fp);
        fprintf(fp, "ALL");
        for (struct VarList * cur = rc->vl_all; cur != NULL; cur = cur->next) {
            if (cur->head->type == NULL) 
                fprintf(fp, " %s", cur->head->name);
        }
        for (struct VarList * cur = rc->vl_all; cur != NULL; cur = cur->next) {
            if (cur->head->type) {
                fprintf(fp, " (%s : ", cur->head->name);
                printPatternPolyType(cur->head->type, fp);
                fprintf(fp, ")");
            }
        }
        fprintf(fp, ",\n");
        num_tabs += 1;
    }

    printPatternPropLList(rc->c, fp, num_tabs, type_mapping, env);
    fprintf(fp, " &&\n");
    printPatternSepLList(rc->C, fp, num_tabs, type_mapping, env);
    fprintf(fp, " -*\n");

    printPatternPropLList(rc->d, fp, num_tabs, type_mapping, env);
    fprintf(fp, " &&\n");
    printPatternSepLList(rc->D, fp, num_tabs, type_mapping, env);
    fprintf(fp, "\n");
    print_tabs(num_tabs, fp);
    fprintf(fp, ")");
}

void fini_rc(struct RamifiedCondition * rc) {
    finiVarList(rc->vl_forall), finiVarList(rc->vl_all), finiVarList(rc->vl_exists);
    finiPatternPropLList(rc->sc);
    finiPatternPropLList(rc->a);
    finiPatternPropLList(rc->b);
    finiPatternPropLList(rc->c);
    finiPatternPropLList(rc->d);
    finiPatternSepLList(rc->A);
    finiPatternSepLList(rc->B);
    finiPatternSepLList(rc->C);
    finiPatternSepLList(rc->D);
}