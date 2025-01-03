#include "StrategyLib.h"

static int * pre_prop_vis, * pre_sep_vis, * post_prop_vis, * post_sep_vis;
static struct StrategyLibRule * crule;
static struct Assertion * cpre, * cpost;

struct StrategyLibRuleList * initStrategyLibRuleList(struct StrategyLibRule * rule,
                                                     struct StrategyLibRuleList * next) {
    struct StrategyLibRuleList * cell = malloc(sizeof(struct StrategyLibRuleList));
    cell->rule = rule;
    cell->next = next;
    return cell;
}

void finiStrategyLibRuleList(struct StrategyLibRuleList * head) {
    if (head == NULL) return;
    finiStrategyLibRule(head->rule);
    finiStrategyLibRuleList(head->next);
    free(head);
}

struct StrategyLibRuleListCell * initStrategyLibRuleListCell() {
    struct StrategyLibRuleListCell * ret = malloc(sizeof(struct StrategyLibRuleListCell));
    ret->head = ret->tail = NULL;
    return ret;
}

void insertStrategyLibRuleListCell(struct StrategyLibRuleListCell * cell, struct StrategyLibRule * rule) {
    if (cell->head == NULL) {
        cell->head = cell->tail = initStrategyLibRuleList(rule, NULL);
    }
    else {
        struct StrategyLibRuleList * temp = initStrategyLibRuleList(rule, NULL);
        cell->tail->next = temp;
        cell->tail = temp;
    }
}

void finiStrategyLibRuleListCell(struct StrategyLibRuleListCell * cell) {
    finiStrategyLibRuleList(cell->head);
    free(cell);
}

struct StrategyLib * initStrategyLib() {
    struct StrategyLib * ret = malloc(sizeof(struct StrategyLib));
    for (int i = 0; i < STRATEGY_LIB_MAX_PRIORITY; i++)
        ret->rules[i] = initStrategyLibRuleListCell();
    return ret;
}

struct StrategyLib * addStrategyLibRule(struct StrategyLib * lib, struct StrategyLibRule * rule) {
    if (rule->priority < 0 || rule->priority >= STRATEGY_LIB_MAX_PRIORITY) {
        ERROR("Priority out of range in addStrategyLibRule()");
    }
    insertStrategyLibRuleListCell(lib->rules[rule->priority], rule);
    return lib;
}

void finiStrategyLib(struct StrategyLib * lib) {
    for (int i = 0; i < STRATEGY_LIB_MAX_PRIORITY; i++)
        finiStrategyLibRuleListCell(lib->rules[i]);
    free(lib);
}

static int checkRule(struct StrategyLibCheckList * cl,
                     struct charMapping * pat_mapping,
                     struct Assertion * pre,
                     struct environment * env) {
    struct StrategyLibCheckList * cur = cl;
    int ret = 1;
    while (cur != NULL) {
        struct StrategyLibCheck * check = cur->check;
        switch (check->ty) {
        case STRATEGY_LIB_CHECK_ABSENSE: {
            struct Proposition * prop = instPatternProp(check->data.prop, pat_mapping, env);
            for (struct PropList * cur = pre->prop_list; cur != NULL; cur = cur->next) {
                if (PropositionCheckEqual(cur->head, prop)) {
                    ret = 0;
                    break;
                }
            }
            PropFree(prop);
            break;
        }
        case STRATEGY_LIB_CHECK_INFER: {
            struct PropList * pl = PropListCons(instPatternProp(check->data.prop, pat_mapping, env), PropListNil());

            struct Prop_solver_return * res = PropEntail(pre->prop_list, pl, env);
            ret &= res->result == 1;
            PropListFree(pl);
            PropListFree(res->res_prop);
            free(res);

            break;
        }
        default: {
            ERROR("Not implemented in checkRule()");
        }
        }
        cur = cur->next;
    }
    return ret;
}

static void deleteProposition(struct PropList ** pl, struct Proposition * prop) {
    struct PropList * cur = *pl;
    if (cur == NULL) return;
    if (cur->head == prop) {
        struct PropList * temp = cur->next;
        PropFree(cur->head);
        free(cur);
        *pl = temp;
        return;
    }
    while (cur->next != NULL) {
        if (cur->next->head == prop) {
            struct PropList * tmp = cur->next;
            cur->next = tmp->next;
            PropFree(tmp->head);
            free(tmp);
            return;
        }
        cur = cur->next;
    }
}

static void deleteSeparation(struct SepList ** sl, struct Separation * sep) {
    struct SepList * cur = *sl;
    if (cur == NULL) return;
    if (cur->head == sep) {
        struct SepList * temp = cur->next;
        SepFree(cur->head);
        free(cur);
        *sl = temp;
        return;
    }
    
    while (cur->next != NULL) {
        if (cur->next->head == sep) {
            struct SepList * tmp = cur->next;
            cur->next = tmp->next;
            SepFree(tmp->head);
            free(tmp);
            return;
        }
        cur = cur->next;
    }
}

static void substPolyType(struct PolyType ** type, int id, struct PolyType * val) {
    if (*type == NULL) return;
    struct PolyType * cur = *type;
    switch (cur->t) {
    case POLY_VAR: {
        if (cur->d.VAR.id == id) {
            PolyTypeFree(cur);
            *type = PolyTypeDeepCopy(val);
        }
        break;
    }
    case POLY_FUNCAPP: {
        struct PolyTypeListNode * list = cur->d.FUNCAPP.args->head;
        while (list != NULL) {
            substPolyType(&(list->data), id, val);
            list = list->next;
        }
        break;
    }
    case POLY_ARROW: {
        substPolyType(&(cur->d.ARROW.left), id, val);
        substPolyType(&(cur->d.ARROW.right), id, val);
        break;
    }
    default: {
        ERROR("Not implemented in substPolyType()");
    }
    }
}

static void substExprVal(struct ExprVal ** expr, int id, struct ExprVal * val) {
    if (*expr == NULL) return;
    struct ExprVal * cur = *expr;
    switch (cur->t) {
    case EZ_VAL: {
        break;
    }
    case VUOP: {
        substExprVal((struct ExprVal **)&(cur->d.VUOP.expr), id, val);
        break;
    }
    case VBOP: {
        substExprVal((struct ExprVal **)&(cur->d.VBOP.expr1), id, val);
        substExprVal((struct ExprVal **)&(cur->d.VBOP.expr2), id, val);
        break;
    }
    case FUNCAPP: {
        if (cur->d.FUNCAPP.id == id) {
            ExprValFree(cur);
            *expr = ExprValDeepCopy(val);
        }
        else {
            struct PolyTypeListNode * tl = cur->d.FUNCAPP.types->head;
            while (tl != NULL) {
                substPolyType(&(tl->data), id, (struct PolyType *)val);
                tl = tl->next;
            }
            struct ExprValListNode * list = cur->d.FUNCAPP.args->head;
            while (list != NULL) {
                substExprVal((struct ExprVal **)&(list->data), id, val);
                list = list->next;
            }
        }
        break;
    }
    case VFIELD_ADDRESS: {
        substExprVal((struct ExprVal **)&(cur->d.VFIELD_ADDRESS.expr), id, val);
        break;
    }
    case LINDEX: {
        substExprVal((struct ExprVal **)&(cur->d.LINDEX.list), id, val);
        substExprVal((struct ExprVal **)&(cur->d.LINDEX.index), id, val);
        break;
    }
    case TIME_COST: {
        break;
    }
    case SIZE_OF: {
        break;
    }
    default: {
        ERROR("Not implemented in substExprVal()");
    }
    }
}

static void substProp(struct Proposition * prop, int id, struct ExprVal * expr) {
    if (prop == NULL) return;
    switch (prop->t) {
    case T_PROP_TRUE:
    case T_PROP_FALSE:
        break;
    case T_PROP_UNARY: {
        substProp(prop->d.UNARY.prop, id, expr);
        break;
    }
    case T_PROP_BINARY: {
        substProp(prop->d.BINARY.prop1, id, expr);
        substProp(prop->d.BINARY.prop2, id, expr);
        break;
    }
    case T_PROP_PTR: {
        substExprVal((struct ExprVal **)&prop->d.PTR.expr, id, expr);
        break;
    }
    case T_PROP_COMPARE: {
        substExprVal((struct ExprVal **)&prop->d.COMPARE.expr1, id, expr);
        substExprVal((struct ExprVal **)&prop->d.COMPARE.expr2, id, expr);
        break;
    }
    case T_PROP_QUANTIFIER: {
        substProp(prop->d.QUANTIFIER.prop, id, expr);
        break;
    }
    case T_PROP_OTHER: {
        struct PolyTypeListNode * tl = prop->d.OTHER.types->head;
        while (tl != NULL) {
            substPolyType(&tl->data, id, (struct PolyType *)expr);
            tl = tl->next;
        }
        struct ExprValListNode * list = prop->d.OTHER.args->head;
        while (list != NULL) {
            substExprVal((struct ExprVal **)&list->data, id, expr);
            list = list->next;
        }
        break;
    }
    default: {
        ERROR("Not implemented in substProp()");
    }
    }
}

static void substSep(struct Separation * sep, int id, struct ExprVal * expr) {
    if (sep == NULL) return;
    switch (sep->t) {
    case T_DATA_AT: {
        substExprVal((struct ExprVal **)&sep->d.DATA_AT.left, id, expr);
        substExprVal((struct ExprVal **)&sep->d.DATA_AT.right, id, expr);
        break;
    }
    case T_UNDEF_DATA_AT: {
        substExprVal((struct ExprVal **)&sep->d.UNDEF_DATA_AT.left, id, expr);
        break;
    }
    case T_OTHER: {
        struct ExprValListNode * cur = sep->d.OTHER.exprs->head;
        while (cur != NULL) {
            substExprVal((struct ExprVal **)&cur->data, id, expr);
            cur = cur->next;
        }
        break;
    }
    case T_ARR: {
        substExprVal((struct ExprVal **)&sep->d.ARR.addr, id, expr);
        substExprVal((struct ExprVal **)&sep->d.ARR.value, id, expr);
        substExprVal((struct ExprVal **)&sep->d.ARR.size, id, expr);
        break;
    }
    default: {
        ERROR("Not implemented in substSep()");
    }
    }
}

static void substPropList(struct PropList * prop_list, int id, struct ExprVal * expr) {
    if (prop_list == NULL) return;
    struct PropList * cur = prop_list;
    while (cur != NULL) {
        substProp(cur->head, id, expr);
        cur = cur->next;
    }
}

static void substSepList(struct SepList * sep_list, int id, struct ExprVal * expr) {
    if (sep_list == NULL) return;
    struct SepList * cur = sep_list;
    while (cur != NULL) {
        substSep(cur->head, id, expr);
        cur = cur->next;
    }
}

static void substMapping(struct intMapping * mapping, int id, struct ExprVal * expr) {
    if (mapping == NULL) return;
    struct intMappingNode * cur = mapping->head;
    while (cur != NULL) {
        if (cur->id != id)
            substExprVal((struct ExprVal **)&cur->val->val, id, expr);
        cur = cur->next;
    }
}

static int findVarPolyType(struct PolyType * type, int id) {
    if (type == NULL) return 0;
    int ret = 0;
    switch (type->t) {
    case POLY_VAR: {
        ret = type->d.VAR.id == id;
        break;
    }
    case POLY_FUNCAPP: {
        struct PolyTypeListNode * list = type->d.FUNCAPP.args->head;
        while (list != NULL) {
            ret = ret || findVarPolyType(list->data, id);
            list = list->next;
        }
        break;
    }
    case POLY_ARROW: {
        ret = findVarPolyType(type->d.ARROW.left, id) || findVarPolyType(type->d.ARROW.right, id);
        break;
    }
    default: {
        ERROR("Not implemented in findVarPolyType()");
    }
    }
    return ret;
}

static int findVarExprVal(struct ExprVal * expr, int id) {
    if (expr == NULL) return 0;
    int ret = 0;
    switch (expr->t) {
    case EZ_VAL: {
        break;
    }
    case VUOP: {
        ret = findVarExprVal(expr->d.VUOP.expr, id);
        break;
    }
    case VBOP: {
        ret = findVarExprVal(expr->d.VBOP.expr1, id) || findVarExprVal(expr->d.VBOP.expr2, id);
        break;
    }
    case FUNCAPP: {
        struct PolyTypeListNode * tl = expr->d.FUNCAPP.types->head;
        while (tl != NULL) {
            ret = ret || findVarPolyType(tl->data, id);
            tl = tl->next;
        }
        struct ExprValListNode * list = expr->d.FUNCAPP.args->head;
        while (list != NULL) {
            ret = ret || findVarExprVal(list->data, id);
            list = list->next;
        }
        break;
    }
    case VFIELD_ADDRESS: {
        ret = findVarExprVal(expr->d.VFIELD_ADDRESS.expr, id);
        break;
    }
    case LINDEX: {
        ret = findVarExprVal(expr->d.LINDEX.list, id) || findVarExprVal(expr->d.LINDEX.index, id);
        break;
    }
    case TIME_COST: {
        break;
    }
    case SIZE_OF: {
        break;
    }
    default: {
        ERROR("Not implemented in findVarExprVal()");
    }
    }
    return ret;
}

static int findVarProp(struct Proposition * prop, int id) {
    if (prop == NULL) return 0;
    int ret = 0;
    switch (prop->t) {
    case T_PROP_TRUE:
    case T_PROP_FALSE:
        break;
    case T_PROP_UNARY: {
        ret = findVarProp(prop->d.UNARY.prop, id);
        break;
    }
    case T_PROP_BINARY: {
        ret = findVarProp(prop->d.BINARY.prop1, id) || findVarProp(prop->d.BINARY.prop2, id);
        break;
    }
    case T_PROP_PTR: {
        ret = findVarExprVal(prop->d.PTR.expr, id);
        break;
    }
    case T_PROP_COMPARE: {
        ret = findVarExprVal(prop->d.COMPARE.expr1, id) || findVarExprVal(prop->d.COMPARE.expr2, id);
        break;
    }
    case T_PROP_QUANTIFIER: {
        ret = findVarProp(prop->d.QUANTIFIER.prop, id);
        break;
    }
    case T_PROP_OTHER: {
        struct PolyTypeListNode * tl = prop->d.OTHER.types->head;
        while (tl != NULL) {
            ret = ret || findVarPolyType(tl->data, id);
            tl = tl->next;
        }
        struct ExprValListNode * list = prop->d.OTHER.args->head;
        while (list != NULL) {
            ret = ret || findVarExprVal(list->data, id);
            list = list->next;
        }
        break;
    }
    default: {
        ERROR("Not implemented in findVarProp()");
    }
    }
    return ret;
}

static int findVarSep(struct Separation * sep, int id) {
    if (sep == NULL) return 0;
    int ret = 0;
    switch (sep->t) {
    case T_DATA_AT: {
        ret = findVarExprVal(sep->d.DATA_AT.left, id) || findVarExprVal(sep->d.DATA_AT.right, id);
        break;
    }
    case T_UNDEF_DATA_AT: {
        ret = findVarExprVal(sep->d.UNDEF_DATA_AT.left, id);
        break;
    }
    case T_OTHER: {
        struct ExprValListNode * cur = sep->d.OTHER.exprs->head;
        while (cur != NULL) {
            ret = ret || findVarExprVal(cur->data, id);
            cur = cur->next;
        }
        break;
    }
    case T_ARR: {
        ret = findVarExprVal(sep->d.ARR.addr, id) || findVarExprVal(sep->d.ARR.value, id) || findVarExprVal(sep->d.ARR.size, id);
        break;
    }
    default: {
        ERROR("Not implemented in findVarSep()");
    }
    }
    return ret;
}

static int findVarAsrt(struct Assertion * asrt, int id) {
    if (asrt == NULL) return 0;
    int ret = 0;
    struct PropList * pl = asrt->prop_list;
    while (pl != NULL) {
        ret = ret || findVarProp(pl->head, id);
        pl = pl->next;
    }
    struct SepList * sl = asrt->sep_list;
    while (sl != NULL) {
        ret = ret || findVarSep(sl->head, id);
        sl = sl->next;
    }
    return ret;
}


static void clearExistList(struct Assertion * asrt) {
    struct ExistList * list = asrt->exist_list;
    while (list != NULL) {
        int id = list->id;
        struct ExistList * temp = list->next;
        if (!findVarAsrt(asrt, id)) {
            asrt->exist_list = ExistListRemove(id, asrt->exist_list);
        }
        list = temp;
    }
}

static struct atype * getAtypeFromPolyType(struct PolyType * type, struct environment * env) {
    if (type == NULL) return NULL;
    switch (type->t) {
    case POLY_VAR: {
        return ATAtom(find_atype_by_id(type->d.VAR.id, &env->persist));
    }
    case POLY_FUNCAPP: {
        struct atype * f = ATAtom(find_atype_by_id(type->d.FUNCAPP.func, &env->persist));
        for (struct PolyTypeListNode * cur = type->d.FUNCAPP.args->head; cur != NULL; cur = cur->next)
            f = ATApp(f, getAtypeFromPolyType(cur->data, env));
        return f;
    }
    case POLY_ARROW: {
        struct atype * left = getAtypeFromPolyType(type->d.ARROW.left, env);
        struct atype * right = getAtypeFromPolyType(type->d.ARROW.right, env);
        return ATArrow(left, right);
    }
    default: {
        ERROR("Not implemented in getAtypeFromPolyType()");
    }
    }
    return NULL;
}   

static struct atype * getAtypeFromPattern(struct PatternPolyType * type, struct charMapping * pat_mapping, struct environment * env) {
    if (type == NULL) return NULL;
    switch (type->ty) {
    case PATTERN_POLY_VAR: {
        struct mappingValue * val = charMappingFind(type->data.var, pat_mapping);
        if (val == NULL) {
            fprintf(stderr, "Pattern variable %s is not assigned a context value.\n", type->data.var);
            ERROR("");
        }
        struct atype * ret = getAtypeFromPolyType(val->val, env);
        return ret;
    }
    case PATTERN_POLY_CONST: {
        return ATAtom(find_atype_by_name(type->data.var, &env->ephemer));
    }
    case PATTERN_POLY_APP: {
        struct atype * f = ATAtom(find_atype_by_name(type->data.app->func, &env->ephemer));
        for (struct PatternPolyTypeList * cur = type->data.app->args; cur != NULL; cur = cur->next) {
            f = ATApp(f, getAtypeFromPattern(cur->head, pat_mapping, env));
        }
        return f;
    }
    case PATTERN_POLY_ARROW: {
        struct atype * left = getAtypeFromPattern(type->data.arrow->left, pat_mapping, env);
        struct atype * right = getAtypeFromPattern(type->data.arrow->right, pat_mapping, env);
        return ATArrow(left, right);
    }
    default: {
        ERROR("Not implemented in getAtypeFromPattern()");
    }
    }
    return NULL;
}

static int matchStrategyLibRulePats(struct StrategyLibPatternLList * cur,
                                    struct charMapping ** pat_mapping,
                                    struct intMapping * exist_mapping,
                                    struct intMapping * ast_mapping,
                                    struct environment * env) {
    if (cur == NULL) return checkRule(crule->checks, *pat_mapping, cpre, env);
    int left = cur->left, pos = cur->pos;
    struct StrategyLibPatternList * pats = cur->list;
    while (pats != NULL) {
        struct StrategyLibPattern * pat = pats->pat;
        int ctxpos = 0;
        int * prop_vis = left ? pre_prop_vis : post_prop_vis;
        int * sep_vis = left ? pre_sep_vis : post_sep_vis;
        struct Assertion * asrt = left ? cpre : cpost;
        if (pat->ty == STRATEGY_LIB_PATTERN_PROP) {
            for (struct PropList * prop = asrt->prop_list; prop != NULL; prop = prop->next, ++ctxpos) {
                if (prop_vis[ctxpos]) continue;
                struct charMapping * new_pat_mapping = charMappingCopy(*pat_mapping);
                if (matchProposition(prop->head, pat->pat.prop, new_pat_mapping, exist_mapping, env)) {
                    intMappingInsert(pos, initPtrMappingValue(prop->head), ast_mapping);
                    prop_vis[ctxpos] = 1;
                    if (matchStrategyLibRulePats(cur->next, &new_pat_mapping, exist_mapping, ast_mapping, env)) {
                        finiCharMapping(*pat_mapping);
                        *pat_mapping = new_pat_mapping;
                        return 1;
                    }
                    prop_vis[ctxpos] = 0;
                }
                finiCharMapping(new_pat_mapping);
            }
        }
        else {
            for (struct SepList * sep = asrt->sep_list; sep != NULL; sep = sep->next, ++ctxpos) {
                if (sep_vis[ctxpos]) continue;
                struct charMapping * new_pat_mapping = charMappingCopy(*pat_mapping);
                if (matchSeparation(sep->head, pat->pat.sep, new_pat_mapping, exist_mapping, env)) {
                    intMappingInsert(pos, initPtrMappingValue(sep->head), ast_mapping);
                    sep_vis[ctxpos] = 1;
                    if (matchStrategyLibRulePats(cur->next, &new_pat_mapping, exist_mapping, ast_mapping, env)) {
                        finiCharMapping(*pat_mapping);
                        *pat_mapping = new_pat_mapping;
                        return 1;
                    }
                    sep_vis[ctxpos] = 0;
                }
                finiCharMapping(new_pat_mapping);
            }
        }
        pats = pats->next;
    }
    return 0;
}

int matchStrategyLibRule(struct StrategyLibRule * rule, struct Assertion * pre, struct Assertion * post,
                         struct intMapping * left_exist_mapping, struct intMapping * right_exist_mapping, struct environment * env) {
    if (rule == NULL) return 0;
    crule = rule, cpre = pre, cpost = post;
    struct charMapping * pat_mapping = initCharMapping(0);
    struct intMapping * ast_mapping = initIntMapping();
    int pre_prop_cnt = 0, pre_sep_cnt = 0, post_prop_cnt = 0, post_sep_cnt = 0;
    for (struct PropList * list = pre->prop_list; list != NULL; list = list->next) pre_prop_cnt++;
    for (struct SepList * list = pre->sep_list; list != NULL; list = list->next) pre_sep_cnt++;
    for (struct PropList * list = post->prop_list; list != NULL; list = list->next) post_prop_cnt++;
    for (struct SepList * list = post->sep_list; list != NULL; list = list->next) post_sep_cnt++;
    pre_prop_vis = calloc(pre_prop_cnt, sizeof(int));
    pre_sep_vis = calloc(pre_sep_cnt, sizeof(int));
    post_prop_vis = calloc(post_prop_cnt, sizeof(int));
    post_sep_vis = calloc(post_sep_cnt, sizeof(int));
    if (!matchStrategyLibRulePats(rule->pats, &pat_mapping, right_exist_mapping, ast_mapping, env)) {
        free(pre_prop_vis);
        free(pre_sep_vis);
        free(post_prop_vis);
        free(post_sep_vis);
        finiCharMapping(pat_mapping);
        finiIntMapping(ast_mapping);
        return 0;
    }
    struct charMapping * _pat_mapping = charMappingDeepCopy(pat_mapping);
    finiCharMapping(pat_mapping);
    pat_mapping = _pat_mapping;
    struct StrategyLibActionList * cur = rule->actions;
    if (exec_info) {
      printf("applying rule (%s, %d)\n", rule->filename, rule->id);
    }
    while (cur != NULL) {
        // PrintAsrt(pre, 0);
        // puts("");
        switch (cur->action->ty) {
        case STRATEGY_LIB_ACTION_DEL_LEFT: {
            int pos = cur->action->data.pos;
            void * ptr = intMappingFind(pos, ast_mapping)->val;
            deleteProposition(&pre->prop_list, ptr);
            deleteSeparation(&pre->sep_list, ptr);
            break;
        }
        case STRATEGY_LIB_ACTION_DEL_RIGHT: {
            int pos = cur->action->data.pos;
            void * ptr = intMappingFind(pos, ast_mapping)->val;
            deleteProposition(&post->prop_list, ptr);
            deleteSeparation(&post->sep_list, ptr);
            break;
        }
        case STRATEGY_LIB_ACTION_ADD_LEFT: {
            if (cur->action->data.expr->ty == STRATEGY_LIB_PATTERN_PROP)
                pre->prop_list = PropListCons(instPatternProp(cur->action->data.expr->pat.prop, pat_mapping, env), pre->prop_list);
            else
                pre->sep_list = SepListCons(instPatternSep(cur->action->data.expr->pat.sep, pat_mapping, env), pre->sep_list);
            break;
        }
        case STRATEGY_LIB_ACTION_ADD_RIGHT: {
            if (cur->action->data.expr->ty == STRATEGY_LIB_PATTERN_PROP)
                post->prop_list = PropListCons(instPatternProp(cur->action->data.expr->pat.prop, pat_mapping, env), post->prop_list);
            else
                post->sep_list = SepListCons(instPatternSep(cur->action->data.expr->pat.sep, pat_mapping, env), post->sep_list);
            break;
        }
        case STRATEGY_LIB_ACTION_ADD_LEFT_EXIST: {
            char * var = cur->action->data.var->name;
            int id = GetNewLogicVar();
            int len_id = 1;
            for (int _id = id / 10; _id  > 0; _id /= 10) len_id++;
            char * name = malloc(strlen(var) + 1 + len_id + 1);
            sprintf(name, "%s_%d", var, id);
            struct logic_var_info * var_info = add_anonymous_var_with_id(LOGIC_GEN_EXISTS, name, id, &env->persist);
            struct atype * type_info = getAtypeFromPattern(cur->action->data.var->type, pat_mapping, env);
            if (type_info == NULL) {
                var_info->atype = ATZ(&env->persist);
            }
            else {
                ASSIGN_ATYPE(var_info->atype, type_info);
            }
            var_info->renaming = renaming_info_free_var(name);
            struct ExprVal * expr = ExprVal_V_VARI(id);
            pre->exist_list = ExistListCons(id, pre->exist_list);
            charMappingInsert(strdup(var), initExprValMappingValue(expr, 1), pat_mapping);
            intMappingInsert(id, initExprValMappingValue(NULL, 0), left_exist_mapping);
            break;
        }
        case STRATEGY_LIB_ACTION_ADD_RIGHT_EXIST: {
            char * var = cur->action->data.var->name;
            int id = GetNewLogicVar();
            int len_id = 1;
            for (int _id = id / 10; _id  > 0; _id /= 10) len_id++;
            char * name = malloc(strlen(var) + 1 + len_id + 1);
            sprintf(name, "%s_%d", var, id);
            struct logic_var_info * var_info = add_anonymous_var_with_id(LOGIC_GEN_EXISTS, name, id, &env->persist);
            struct atype * type_info = getAtypeFromPattern(cur->action->data.var->type, pat_mapping, env);
            if (type_info == NULL) {
                var_info->atype = ATZ(&env->persist);
            }
            else {
                ASSIGN_ATYPE(var_info->atype, type_info);
            }
            var_info->renaming = renaming_info_free_var(name);
            struct ExprVal * expr = ExprVal_V_VARI(id);
            post->exist_list = ExistListCons(id, post->exist_list);
            charMappingInsert(strdup(var), initExprValMappingValue(expr, 1), pat_mapping);
            intMappingInsert(id, initExprValMappingValue(NULL, 0), right_exist_mapping);
            break;
        }
        case STRATEGY_LIB_ACTION_INST: {
            struct ExprVal * expr = charMappingFind(cur->action->data.mapping->var, pat_mapping)->val;
            if (expr->t != FUNCAPP || !ExprValListIsEmpty(expr->d.FUNCAPP.args)) {
                fprintf(stdout, "Pattern variable %s is assigned a non-atomic value.\n", cur->action->data.mapping->var);
                fprintf(stdout, "The assigned context is ");
                PrintExprVal(expr, env);
                puts("");
                ERROR("");
            }
            int id = expr->d.FUNCAPP.id;
            if (!intMappingIn(id, right_exist_mapping)) {
                fprintf(stdout, "Pattern variable %s is assigned to a non-existential variable.\n", cur->action->data.mapping->var);
                fprintf(stdout, "The assigned context is ");
                PrintExprVal(expr, env);
                puts("");
                ERROR("Suggest using ``exists`` annotation in strategies.");
            }
            struct ExprVal * new_expr = instPatternExpr(cur->action->data.mapping->expr, pat_mapping, env);
            substPropList(post->prop_list, id, new_expr);
            substSepList(post->sep_list, id, new_expr);
            substMapping(right_exist_mapping, id, new_expr);
            // for (struct charMappingNode * cur = right_exist_mapping->head; cur != NULL; cur = cur->next);
            intMappingInsert(id, initExprValMappingValue(new_expr, 1), right_exist_mapping);
            post->exist_list = ExistListRemove(id, post->exist_list);
            break;
        }
        case STRATEGY_LIB_ACTION_SUBST: {
            struct ExprVal * expr = charMappingFind(cur->action->data.mapping->var, pat_mapping)->val;
            if (expr->t != FUNCAPP || !ExprValListIsEmpty(expr->d.FUNCAPP.args)) {
                fprintf(stdout, "Pattern variable %s is assigned a non-atomic value.\n", cur->action->data.mapping->var);
                fprintf(stdout, "The assigned context is ");
                PrintExprVal(expr, env);
                puts("");
                ERROR("");
            }
            int id = expr->d.FUNCAPP.id;
            struct ExprVal * new_expr = instPatternExpr(cur->action->data.mapping->expr, pat_mapping, env);
            substPropList(pre->prop_list, id, new_expr);
            substSepList(pre->sep_list, id, new_expr);
            substPropList(post->prop_list, id, new_expr);
            substSepList(post->sep_list, id, new_expr);
            pre->exist_list = ExistListRemove(id, pre->exist_list);
            intMappingErase(id, left_exist_mapping);
            break;
        }
        default: {
            ERROR("Not implemented in matchStrategyLibRule()");
        }
        }
        cur = cur->next;
    }
    // clearExistList(post);
    // printf("Before applying rule %d\n", rule->id);
    // PrintAsrt(pre, env);
    // puts("|--");
    // PrintAsrt(post, env);
    free(pre_prop_vis);
    free(pre_sep_vis);
    free(post_prop_vis);
    free(post_sep_vis);
    finiCharMapping(pat_mapping);
    finiIntMapping(ast_mapping);
    return 1;
}

int matchStrategyLib(struct StrategyLib * lib, struct Assertion * pre, struct Assertion * post,
                     struct intMapping * left_exist_mapping, struct intMapping * right_exist_mapping, struct environment * env) {
    for (int i = 0; i < STRATEGY_LIB_MAX_PRIORITY; i++)
        for (struct StrategyLibRuleList * cur = lib->rules[i]->head; cur != NULL; cur = cur->next)
            if (matchStrategyLibRule(cur->rule, pre, post, left_exist_mapping, right_exist_mapping, env)) return 1;
    return 0;
}
