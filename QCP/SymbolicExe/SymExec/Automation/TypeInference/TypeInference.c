#include "TypeInference.h"

static struct charMapping * type_mapping, * unk_mapping;
static int cnt = 1;

static int has_unk(struct PatternPolyType * t) {
    if (t == NULL) return 0;
    switch (t->ty) {
    case PATTERN_POLY_CONST:
    case PATTERN_POLY_VAR: {
        return 0;
    }
    case PATTERN_POLY_UNK: {
        return 1;
    }
    case PATTERN_POLY_APP: {
        for (struct PatternPolyTypeList * lcur = t->data.app->args; lcur != NULL; lcur = lcur->next) {
            if (has_unk(lcur->head)) return 1;
        }
        return 0;
    }
    case PATTERN_POLY_ARROW: {
        return has_unk(t->data.arrow->left) || has_unk(t->data.arrow->right);
    }
    }
    return 0;
}

static int get_len(int x) {
    int ret = 0;
    if (x == 0) return 1;
    while (x) {
        x /= 10;
        ret++;
    }
    return ret;
}

static void Print_PolyType_mapping(FILE * fp) {
    fprintf(fp, "Current type environment:\n");
    for (struct charMappingNode * cur = type_mapping->head; cur != NULL; cur = cur->next) {
        fprintf(fp, "%s -> ", cur->var);
        PatternPolyTypePrint(fp, cur->val->val);
        fprintf(fp, "\n");
    }
}

static void check_type_mapping() {
    for (struct charMappingNode * cur = type_mapping->head; cur != NULL; cur = cur->next) {
        if (cur->val->val == NULL) {
            fprintf(stderr, "Type inference error: type of pattern variable is not inferred in type environment\n");
            fprintf(stderr, "%s -> NULL\n", cur->var);
            ERROR("");
        }
        if (has_unk(cur->val->val)) {
            fprintf(stderr, "Type inference error: unresolved unification variable in type environment\n");
            fprintf(stderr, "%s -> ", cur->var);
            PatternPolyTypePrint(stderr, cur->val->val);
            fprintf(stderr, "\n");
            ERROR("");
        }
    }
}

static void print_unk_mapping(FILE * fp) {
    fprintf(fp, "Current unification variable environment:\n");
    for (struct charMappingNode * cur = unk_mapping->head; cur != NULL; cur = cur->next) {
        fprintf(fp, "?%s -> ", cur->var);
        PatternPolyTypePrint(fp, cur->val->val);
        fprintf(fp, "\n");
    }
}

static struct PatternPolyType * get_ret_type(struct PatternPolyType * t) {
    struct PatternPolyType * ret = t;
    while (ret != NULL && ret->ty == PATTERN_POLY_ARROW)
        ret = ret->data.arrow->right;
    return ret;
}

static void unify_error(struct PatternPolyType * t1, struct PatternPolyType * t2) {
    fprintf(stderr, "Type inference error: cannot unify ");
    PatternPolyTypePrint(stderr, t1);
    fprintf(stderr, " with ");
    PatternPolyTypePrint(stderr, t2);
    fprintf(stderr, "\n");
    Print_PolyType_mapping(stderr);
    print_unk_mapping(stderr);
    ERROR("");
}

static void substitute(char * var, struct PatternPolyType ** t, struct PatternPolyType * val) {
    struct PatternPolyType * tcur = *t;
    if (tcur == NULL) return;
    switch (tcur->ty) {
    case PATTERN_POLY_CONST:
    case PATTERN_POLY_VAR: {
        break;
    }
    case PATTERN_POLY_UNK: {
        if (!strcmp(var, tcur->data.var)) {
            PatternPolyTypeFree(tcur);
            *t = PatternPolyTypeDeepCopy(val);
            break;
        }
        break;
    }
    case PATTERN_POLY_APP: {
        for (struct PatternPolyTypeList * lcur = tcur->data.app->args; lcur != NULL; lcur = lcur->next) {
            substitute(var, &lcur->head, val);
        }
        break;
    }
    case PATTERN_POLY_ARROW: {
        substitute(var, &tcur->data.arrow->left, val);
        substitute(var, &tcur->data.arrow->right, val);
        break;
    }
    }
}

int find_unk(char * var, struct PatternPolyType * t) {
    if (t == NULL) return 0;
    switch (t->ty) {
    case PATTERN_POLY_CONST:
    case PATTERN_POLY_VAR: {
        return 0;
    }
    case PATTERN_POLY_UNK: {
        return !strcmp(var, t->data.var);
    }
    case PATTERN_POLY_APP: {
        for (struct PatternPolyTypeList * lcur = t->data.app->args; lcur != NULL; lcur = lcur->next) {
            if (find_unk(var, lcur->head)) return 1;
        }
        return 0;
    }
    case PATTERN_POLY_ARROW: {
        return find_unk(var, t->data.arrow->left) || find_unk(var, t->data.arrow->right);
    }
    }
    return 0;

}

static void subst(char * var, struct PatternPolyType * val) {
    for (struct charMappingNode * cur = type_mapping->head; cur != NULL; cur = cur->next) {
        substitute(var, (struct PatternPolyType **)&cur->val->val, val);
    }
    for (struct charMappingNode * cur = unk_mapping->head; cur != NULL; cur = cur->next) {
        substitute(var, (struct PatternPolyType **)&cur->val->val, val);
        if (find_unk(cur->var, cur->val->val)) {
            fprintf(stderr, "Type inference error: circular assigment\n");
            fprintf(stderr, "Assign ?%s to ", cur->var);
            PatternPolyTypePrint(stderr, cur->val->val);
            ERROR("");
        }
    }
}

static int unify(struct PatternPolyType * t1, struct PatternPolyType * t2) {
    if (t1 == NULL && t2 == NULL) return 1;
    if (t1 == NULL || t2 == NULL) return 0;
    if (t1->ty == PATTERN_POLY_UNK && t2->ty == PATTERN_POLY_UNK) {
        if (!strcmp(t1->data.var, t2->data.var)) return 1;
    }
    if (t1->ty == PATTERN_POLY_UNK) {
        struct mappingValue * mv = charMappingFind(t1->data.var, unk_mapping);
        if (mv == NULL) {
            charMappingInsert(t1->data.var, initPatternPolyTypeMappingValue(PatternPolyTypeDeepCopy(t2), 1), unk_mapping);
            subst(t1->data.var, t2);
            return 1;
        }
        else {
            struct PatternPolyType * x1 = PatternPolyTypeDeepCopy(mv->val);
            if (!unify(x1, t2)) {
                PatternPolyTypeFree(x1);
                return 0;
            }
        }
        return 1;
    }
    if (t2->ty == PATTERN_POLY_UNK) return unify(t2, t1);
    if (t1->ty != t2->ty) return 0;
    switch (t1->ty) {
    case PATTERN_POLY_CONST:
    case PATTERN_POLY_VAR: {
        return !strcmp(t1->data.var, t2->data.var);
    }
    case PATTERN_POLY_APP: {
        if (strcmp(t1->data.app->func, t2->data.app->func)) return 0;
        struct PatternPolyTypeList * l1 = t1->data.app->args, * l2 = t2->data.app->args;
        while (l1 != NULL && l2 != NULL) {
            if (!unify(l1->head, l2->head)) return 0;
            l1 = l1->next;
            l2 = l2->next;
        }
        return l1 == NULL && l2 == NULL;
    }
    case PATTERN_POLY_ARROW: {
        return unify(t1->data.arrow->left, t2->data.arrow->left) && unify(t1->data.arrow->right, t2->data.arrow->right);
    }
    default : {
      
    }
    }
    return 0;
}

struct PatternPolyType * instantiate(struct atype * t, struct qvar_list * qv, struct PatternPolyTypeList * args) {
    if (t == NULL) return NULL;
    switch (t->t) {
    case AT_ATOM: {
        struct atype_info * info = t->d.ATOM.info;
        return initPatternPolyTypeConst(strdup(info->name));
    }
    case AT_TVAR: {
        ERROR("Type inference error: AT_TVAR should not appear in instantiation");
        break;
    }
    case AT_ARROW: {
        struct PatternPolyType * from = instantiate(t->d.ARROW.from, qv, args);
        struct PatternPolyType * to = instantiate(t->d.ARROW.to, qv, args);
        return initPatternPolyTypeArrow(from, to);
    }
    case AT_APP: {
        struct PatternPolyType * l = instantiate(t->d.APP.tfn, qv, args);
        struct PatternPolyType * r = instantiate(t->d.APP.rand, qv, args);
        if (l->ty == PATTERN_POLY_CONST) {
            char * name = l->data.var;
            struct PatternPolyType * ret = initPatternPolyTypeApp(strdup(name), initPatternPolyTypeList(r, NULL));
            PatternPolyTypeFree(l);
            return ret;
        }
        else if (l->ty == PATTERN_POLY_APP) {
            struct PatternPolyTypeList * lcur = l->data.app->args;
            while (lcur->next != NULL) lcur = lcur->next;
            lcur->next = initPatternPolyTypeList(r, NULL);
            return l;
        }
        else {
            fprintf(stderr, "Type inference error: cannot instantiate type AT_APP\n");
            fprintf(stderr, "The app_l type is ");
            PatternPolyTypePrint(stderr, l);
            fprintf(stderr, "\n");
            fprintf(stderr, "The app_r type is ");
            PatternPolyTypePrint(stderr, r);
            fprintf(stderr, "\n");
            ERROR("");
        }
        break;
    }
    case AT_QVAR: {
        struct qvar_list * qcur = qv;
        struct PatternPolyTypeList * acur = args;
        while (qcur != NULL && acur != NULL) {
            if (qcur->qv == t) return PatternPolyTypeDeepCopy(acur->head);
            qcur = qcur->next, acur = acur->next;
        }
        fprintf(stderr, "Type inference error: cannot find type variable %s in atype instantiation\n", t->d.QVAR.name);
        ERROR("");
        break;
    }
    }
    return NULL;
}

static struct PatternPolyType * try_instantiate(struct atype * t, struct qvar_list * qv, struct PatternPolyTypeList * args) {
    // printf("!!!\n");
    // if (t) print_atype(t); else printf("NULL\n");
    // printf("!!!\n");
    if (t == NULL) return NULL;
    switch (t->t) {
    case AT_ATOM: {
        struct atype_info * info = t->d.ATOM.info;
        return initPatternPolyTypeConst(strdup(info->name));
    }
    case AT_TVAR: {
        return try_instantiate(t->d.TVAR.link, qv, args);
    }
    case AT_ARROW: {
        struct PatternPolyType * from = try_instantiate(t->d.ARROW.from, qv, args);
        if (!from) return NULL;
        struct PatternPolyType * to = try_instantiate(t->d.ARROW.to, qv, args);
        if (!to) { PatternPolyTypeFree(from); return NULL; }
        return initPatternPolyTypeArrow(from, to);
    }
    case AT_APP: {
        struct PatternPolyType * l = try_instantiate(t->d.APP.tfn, qv, args);
        if (l == NULL) return NULL;
        struct PatternPolyType * r = try_instantiate(t->d.APP.rand, qv, args);
        if (r == NULL) { PatternPolyTypeFree(l); return NULL; }
        if (l->ty == PATTERN_POLY_CONST) {
            char * name = l->data.var;
            struct PatternPolyType * ret = initPatternPolyTypeApp(strdup(name), initPatternPolyTypeList(r, NULL));
            PatternPolyTypeFree(l);
            return ret;
        }
        else if (l->ty == PATTERN_POLY_APP) {
            struct PatternPolyTypeList * lcur = l->data.app->args;
            while (lcur->next != NULL) lcur = lcur->next;
            lcur->next = initPatternPolyTypeList(r, NULL);
            return l;
        }
        else {
            return NULL;
        }
        break;
    }
    case AT_QVAR: {
        struct qvar_list * qcur = qv;
        struct PatternPolyTypeList * acur = args;
        while (qcur != NULL && acur != NULL) {
            if (qcur->qv == t) return PatternPolyTypeDeepCopy(acur->head);
            qcur = qcur->next, acur = acur->next;
        }
        return NULL;
        break;
    }
    }
    return NULL;
}

static struct PatternPolyType * apply(struct PatternPolyType * f, struct PatternExprList * tl, struct environment * env);

static struct PatternPolyType * type_infer_expr_list(struct PatternExprList * el, struct environment * env, struct PatternPolyType * ret_type);

// static struct PatternPolyType * try_apply(struct PatternPolyType * f, struct PatternExprList * el, struct environment * env);

static struct PatternPolyType * type_infer_expr(struct PatternExpr * expr, struct environment * env) {
    switch (expr->ty) {
    case PATTERN_EXPR_CONST: {
        return initPatternPolyTypeConst(strdup("Z"));
    }
    case PATTERN_EXPR_VAR:
    case PATTERN_EXPR_SVAR:
    case PATTERN_EXPR_EVAR: 
    case PATTERN_EXPR_GVAR: {
        struct mappingValue * mv = charMappingFind(expr->data.var, type_mapping);
        if (mv == NULL || mv->val == NULL) {
            int len = strlen(expr->data.var);
            char * unk_var = malloc(len + 6);
            sprintf(unk_var, "%s_type", expr->data.var);
            struct PatternPolyType * ret = initPatternPolyTypeUnk(unk_var);
            charMappingInsert(expr->data.var, initPatternPolyTypeMappingValue(ret, 1), type_mapping);
            return PatternPolyTypeDeepCopy(ret);
        }
        else return PatternPolyTypeDeepCopy(mv->val);
    }
    case PATTERN_EXPR_UNOP: {
        struct PatternPolyType * tz = initPatternPolyTypeConst(strdup("Z"));
        struct PatternPolyType * t = type_infer_expr(expr->data.unop->expr, env);
        if (!unify(t, tz)) unify_error(t, tz);
        PatternPolyTypeFree(t);
        return tz;
    }
    case PATTERN_EXPR_BINOP: {
        struct PatternPolyType * tz = initPatternPolyTypeConst(strdup("Z"));
        struct PatternPolyType * t1 = type_infer_expr(expr->data.binop->left, env);
        struct PatternPolyType * t2 = type_infer_expr(expr->data.binop->right, env);
        if (!unify(t1, tz)) unify_error(t1, tz);
        if (!unify(t2, tz)) unify_error(t2, tz);
        PatternPolyTypeFree(t1);
        PatternPolyTypeFree(t2);
        return tz;
    }
    case PATTERN_EXPR_ARRIDX: {
        struct PatternPolyType * tz = initPatternPolyTypeConst(strdup("Z"));
        char * var = malloc(4 + get_len(cnt));
        if (exec_info) {
          printf("%d, unk%d\n", cnt, cnt);
        }
        sprintf(var, "unk%d", cnt); cnt += 1;
        struct PatternPolyType * ut = initPatternPolyTypeUnk(var);
        struct PatternPolyType * t = initPatternPolyTypeApp(strdup("list"), initPatternPolyTypeList(PatternPolyTypeDeepCopy(ut), NULL));
        struct PatternPolyType * t1 = type_infer_expr(expr->data.arridx->array, env);
        struct PatternPolyType * t2 = type_infer_expr(expr->data.arridx->index, env);
        if (!unify(t1, t)) unify_error(t1, t);
        if (!unify(t2, tz)) unify_error(t2, tz);
        PatternPolyTypeFree(t1);
        PatternPolyTypeFree(t2);
        PatternPolyTypeFree(t);
        PatternPolyTypeFree(tz);
        return ut;
    }
    case PATTERN_EXPR_FIELD: {
        struct PatternPolyType * tz = initPatternPolyTypeConst(strdup("Z"));
        struct PatternPolyType * t = type_infer_expr(expr->data.field->expr, env);
        if (!unify(t, tz)) unify_error(t, tz);
        PatternPolyTypeFree(t);
        return tz;
    }
    case PATTERN_EXPR_SIZEOF: {
        return initPatternPolyTypeConst(strdup("Z"));
    }
    case PATTERN_EXPR_APP: {
        struct projection_info * pinfo = find_projection_by_name(expr->data.app->func, &env->ephemer);
        struct PatternPolyType * ret_type;
        if (pinfo == NULL) {
            struct var_scope_union * scope = find_logic_var_by_name(expr->data.app->func, &env->ephemer);
            if (scope == NULL) {
                scope = find_prog_var_by_name(expr->data.app->func, &env->ephemer);
                if (scope == NULL) {
                  fprintf(stderr, "Type inference error: cannot find type info for function %s\n", expr->data.app->func);
                  ERROR("Function with type argument cannot be patterned\n");
                }
                return initPatternPolyTypeConst(strdup("Z"));
            }
            struct logic_var_info * info = scope->d.logic_var;
            if (expr->data.app->id == -1) expr->data.app->id = info->id;
            struct PatternPolyType * t = instantiate(info->atype, info->qv, expr->data.app->type_list);
            ret_type = apply(t, expr->data.app->expr_list, env);
            PatternPolyTypeFree(t);
            return ret_type;
        }
        else {
            struct PatternExprList * params = expr->data.app->expr_list;
            if (params == NULL) {
                fprintf(stderr, "Type inference error: field function %s should have at least one argument\n", pinfo->name);
                ERROR("");
            }
            struct PatternPolyType * first_type = type_infer_expr(params->expr, env);
            if (has_unk(first_type)) {
                fprintf(stderr, "Type inference error: the type of 1st argument of field function %s should be explicitly annotated\n", pinfo->name);
                ERROR("");
            }
            while (pinfo != NULL) {
                struct PatternPolyType * record_t = try_instantiate(pinfo->var->atype, pinfo->qv, expr->data.app->type_list);
                if (!record_t || record_t->ty != PATTERN_POLY_ARROW || !unify(first_type, record_t->data.arrow->left)) {
                  // printf("first_type : ");
                  // PatternPolyTypePrint(stdout, first_type);
                  // printf("record_t : ");
                  // if (record_t && record_t->ty == PATTERN_POLY_ARROW)
                  // PatternPolyTypePrint(stdout, record_t->data.arrow->left);
                  // else printf("UNKNOWN\n");
                  // puts("");
                  PatternPolyTypeFree(record_t);
                  pinfo = pinfo->next;
                  continue;
                }
                if (expr->data.app->id == -1) expr->data.app->id = pinfo->var->id;
                struct PatternPolyType * t = record_t->data.arrow->right;
                ret_type = apply(t, params->next, env);
                PatternPolyTypeFree(record_t);
                PatternPolyTypeFree(first_type);
                return ret_type;
            }
            fprintf(stderr, "Type inference error: cannot find a corresponding type for field function %s", expr->data.app->func);
            ERROR("");
        }
    }
    case PATTERN_EXPR_PATAPP: {
        struct mappingValue * mv = charMappingFind(expr->data.papp->var, type_mapping);
        if (mv == NULL || mv->val == NULL) {
            int len = strlen(expr->data.papp->var);
            char * unk_ret_var = malloc(len + 5);
            sprintf(unk_ret_var, "%s_ret", expr->data.papp->var);
            struct PatternPolyType * ret = initPatternPolyTypeUnk(unk_ret_var);
            struct PatternPolyType * t = type_infer_expr_list(expr->data.papp->expr_list, env, PatternPolyTypeDeepCopy(ret));
            charMappingInsert(expr->data.papp->var, initPatternPolyTypeMappingValue(t, 1), type_mapping);
            return ret;
        }
        return apply(mv->val, expr->data.papp->expr_list, env);
    }
    }
    return NULL;
}

static struct PatternPolyType * apply(struct PatternPolyType * f, struct PatternExprList * el, struct environment * env) {
    if (el == NULL) return PatternPolyTypeDeepCopy(f);
    if (f->ty != PATTERN_POLY_ARROW) {
        fprintf(stderr, "Type inference error: cannot apply non-arrow type\n");
        PatternPolyTypePrint(stderr, f);
        ERROR("");
    }
    struct PatternPolyType * res = type_infer_expr(el->expr, env);
    if (!unify(f->data.arrow->left, res)) unify_error(f->data.arrow->left, res);
    PatternPolyTypeFree(res);
    return apply(f->data.arrow->right, el->next, env);
}

// static struct PatternPolyType * try_apply(struct PatternPolyType * f, struct PatternExprList * el, struct environment * env) {
//     if (el == NULL) return PatternPolyTypeDeepCopy(f);
//     if (f->ty != PATTERN_POLY_ARROW) return NULL;
//     struct PatternPolyType * res = type_infer_expr(el->expr, env);
//     if (!unify(f->data.arrow->left, res)) {
//         PatternPolyTypeFree(res);
//         return NULL;
//     }
//     PatternPolyTypeFree(res);
//     return try_apply(f->data.arrow->right, el->next, env);
// }

static struct PatternPolyType * type_infer_expr_list(struct PatternExprList * el, struct environment * env, struct PatternPolyType * ret_type) {
    if (el == NULL) return ret_type;
    struct PatternPolyType * t = type_infer_expr(el->expr, env);
    return initPatternPolyTypeArrow(t, type_infer_expr_list(el->next, env, ret_type));
}

static struct PatternPolyType *type_infer_prop(struct PatternProp * prop, struct environment * env) {
    struct PatternPolyType * ret = initPatternPolyTypeConst(strdup("Prop"));
    switch (prop->ty) {
    case PATTERN_PROP_TRUE:
    case PATTERN_PROP_FALSE: {
        break;
    }
    case PATTERN_PROP_UNOP: {
        struct PatternPolyType * t = type_infer_prop(prop->data.unop->prop, env);
        if (!unify(t, ret)) unify_error(t, ret);
        PatternPolyTypeFree(t);
        break;
    }
    case PATTERN_PROP_BINOP: {
        struct PatternPolyType * t1 = type_infer_prop(prop->data.binop->left, env);
        struct PatternPolyType * t2 = type_infer_prop(prop->data.binop->right, env);
        if (!unify(t1, ret)) unify_error(t1, ret);
        if (!unify(t2, ret)) unify_error(t2, ret);
        PatternPolyTypeFree(t1);
        PatternPolyTypeFree(t2);
        break;
    }
    case PATTERN_PROP_PTR: {
        ERROR("Currently pointer-prop-type is not supported");
        return NULL;
    }
    case PATTERN_PROP_COMPARE: {
        struct PatternPolyType * t1 = type_infer_expr(prop->data.comp->left, env);
        struct PatternPolyType * t2 = type_infer_expr(prop->data.comp->right, env);
        if (prop->data.comp->op == PROP_EQ || prop->data.comp->op == PROP_NEQ) {
            if (!unify(t1, t2)) unify_error(t1, t2);
            PatternPolyTypeFree(t1);
            PatternPolyTypeFree(t2);
            break;
        } else {
            struct PatternPolyType * t3 = initPatternPolyTypeConst(strdup("Z"));
            if (!unify(t1, t3)) unify_error(t1, t3);
            if (!unify(t2, t3)) unify_error(t2, t3);
            PatternPolyTypeFree(t1);
            PatternPolyTypeFree(t2);
            PatternPolyTypeFree(t3);
            break;
        }
    }
    case PATTERN_PROP_PRED: {
        struct projection_info * pinfo = find_projection_by_name(prop->data.pred->name, &env->ephemer);
        if (pinfo == NULL) {
            struct var_scope_union * scope = find_logic_var_by_name(prop->data.pred->name, &env->ephemer);
            if (scope == NULL) {
                fprintf(stderr, "Type inference error: cannot find type info for predicate %s\n", prop->data.pred->name);
                ERROR("Predicate with type argument cannot be patterned\n");
            }
            struct logic_var_info * info = scope->d.logic_var;
            if (prop->data.pred->id == -1) prop->data.pred->id = info->id;
            struct PatternPolyType * t = instantiate(info->atype, info->qv, prop->data.pred->types);
            struct PatternPolyType * ret_type = get_ret_type(t);
            struct PatternPolyType * t1 = type_infer_expr_list(prop->data.pred->args, env, PatternPolyTypeDeepCopy(ret_type));
            if (!unify(t, t1)) unify_error(t, t1);
            PatternPolyTypeFree(t);
            PatternPolyTypeFree(t1);
            break;
        }
        else {
            struct PatternExprList * params = prop->data.pred->args;
            if (params == NULL) {
                fprintf(stderr, "Type inference error: field function %s should have at least one argument\n", pinfo->name);
                ERROR("");
            }
            struct PatternPolyType * first_type = type_infer_expr(params->expr, env);
            if (has_unk(first_type)) {
                fprintf(stderr, "Type inference error: the type of 1st argument of field function %s should be explicitly annotated\n", pinfo->name);
                ERROR("");
            }
            int find = 0;
            while (pinfo != NULL) {
                struct PatternPolyType * record_t = try_instantiate(pinfo->var->atype, pinfo->qv, prop->data.pred->types);
                if (!record_t || record_t->ty != PATTERN_POLY_ARROW || !unify(first_type, record_t->data.arrow->left)) {
                  // printf("first_type : ");
                  // PatternPolyTypePrint(stdout, first_type);
                  // printf("record_t : ");
                  // PatternPolyTypePrint(stdout, record_t->data.arrow->left);
                  // puts("");
                  PatternPolyTypeFree(record_t);
                  pinfo = pinfo->next;
                  continue;
                }
                if (prop->data.pred->id == -1) prop->data.pred->id = pinfo->var->id;
                struct PatternPolyType * ret_type = get_ret_type(record_t->data.arrow->right);
                struct PatternPolyType * t1 = type_infer_expr_list(params->next, env, PatternPolyTypeDeepCopy(ret_type));
                if (!unify(record_t->data.arrow->right, t1)) unify_error(record_t->data.arrow->right, t1);
                PatternPolyTypeFree(record_t);
                PatternPolyTypeFree(t1);
                PatternPolyTypeFree(first_type);
                find = 1;
                break;
            }
            if (find) break;
            else {
                fprintf(stderr, "Type inference error: cannot find a corresponding type for field predicate %s", prop->data.pred->name);
                ERROR("");
            }
        }
    }
    case PATTERN_PROP_PATPRED: {
        struct mappingValue * mv = charMappingFind(prop->data.ppred->var, type_mapping);
        if (mv == NULL || mv->val == NULL) {
            int len = strlen(prop->data.ppred->var);
            char * unk_ret_var = malloc(len + 5);
            sprintf(unk_ret_var, "%s_ret", prop->data.ppred->var);
            struct PatternPolyType * ret = initPatternPolyTypeUnk(unk_ret_var);
            struct PatternPolyType * t = type_infer_expr_list(prop->data.ppred->args, env, PatternPolyTypeDeepCopy(ret));
            charMappingInsert(prop->data.ppred->var, initPatternPolyTypeMappingValue(t, 1), type_mapping);
            return ret;
        }
        struct PatternPolyType * t = mv->val;
        struct PatternPolyType * ret = PatternPolyTypeDeepCopy(get_ret_type(t));
        struct PatternPolyType * t1 = type_infer_expr_list(prop->data.ppred->args, env, PatternPolyTypeDeepCopy(ret));
        if (!unify(t, t1)) unify_error(t, t1);
        PatternPolyTypeFree(t1);
        return ret;
    }
    }
    return ret;
}

static struct PatternPolyType * type_infer_sep(struct PatternSep * sep, struct environment * env) {
    struct PatternPolyType * ret = initPatternPolyTypeConst(strdup("Assertion"));
    switch (sep->ty) {
    case PATTERN_SEP_DATA_AT: {
        struct PatternPolyType * tz = initPatternPolyTypeConst(strdup("Z"));
        struct PatternPolyType * t = type_infer_expr(sep->data.data_at->addr, env);
        if (!unify(t, tz)) unify_error(t, tz);
        struct PatternPolyType * t1 = type_infer_expr(sep->data.data_at->data, env);
        if (!unify(t1, tz)) unify_error(t1, tz);
        PatternPolyTypeFree(t);
        PatternPolyTypeFree(t1);
        break;
    }
    case PATTERN_SEP_UNDEF: {
        struct PatternPolyType * tz = initPatternPolyTypeConst(strdup("Z"));
        struct PatternPolyType * t = type_infer_expr(sep->data.undef_data_at->addr, env);
        if (!unify(t, tz)) unify_error(t, tz);
        PatternPolyTypeFree(t);
        break;
    }
    case PATTERN_SEP_ARR: {
        ERROR("Currently array-sep-type is not supported in type inference");
        break;
    }
    case PATTERN_SEP_PRED: {
        struct projection_info * pinfo = find_projection_by_name(sep->data.pred->name, &env->ephemer);
        if (pinfo == NULL) {
            struct var_scope_union * scope = find_logic_var_by_name(sep->data.pred->name, &env->ephemer);
            if (scope == NULL) {
                fprintf(stderr, "Type inference error: cannot find type info for predicate %s\n", sep->data.pred->name);
                ERROR("Predicate with type argument cannot be patterned\n");
            }
            struct logic_var_info * info = scope->d.logic_var;
            if (sep->data.pred->id == -1) sep->data.pred->id = info->id;
            struct PatternPolyType * t = instantiate(info->atype, info->qv, sep->data.pred->types);
            struct PatternPolyType * ret_type = get_ret_type(t);
            struct PatternPolyType * t1 = type_infer_expr_list(sep->data.pred->args, env, PatternPolyTypeDeepCopy(ret_type));
            if (!unify(t, t1)) unify_error(t, t1);
            PatternPolyTypeFree(t);
            PatternPolyTypeFree(t1);
            break;
        }
        else {
            struct PatternExprList * params = sep->data.pred->args;
            if (params == NULL) {
                fprintf(stderr, "Type inference error: field function %s should have at least one argument\n", pinfo->name);
                ERROR("");
            }
            struct PatternPolyType * first_type = type_infer_expr(params->expr, env);
            if (has_unk(first_type)) {
                fprintf(stderr, "Type inference error: the type of 1st argument of field function %s should be explicitly annotated\n", pinfo->name);
                ERROR("");
            }
            int find = 0;
            while (pinfo != NULL) {
                struct PatternPolyType * record_t = try_instantiate(pinfo->var->atype, pinfo->qv, sep->data.pred->types);
                if (!record_t || record_t->ty != PATTERN_POLY_ARROW || !unify(first_type, record_t->data.arrow->left)) {
                  // printf("first_type : ");
                  // PatternPolyTypePrint(stdout, first_type);
                  // printf("record_t : ");
                  // PatternPolyTypePrint(stdout, record_t->data.arrow->left);
                  // puts("");
                  PatternPolyTypeFree(record_t);
                  pinfo = pinfo->next;
                  continue;
                }
                if (sep->data.pred->id == -1) sep->data.pred->id = pinfo->var->id;
                struct PatternPolyType * t = record_t->data.arrow->right;
                struct PatternPolyType * ret_type = get_ret_type(t);
                struct PatternPolyType * t1 = type_infer_expr_list(params->next, env, PatternPolyTypeDeepCopy(ret_type));
                if (!unify(t, t1)) unify_error(t, t1);
                PatternPolyTypeFree(record_t);
                PatternPolyTypeFree(t1);
                PatternPolyTypeFree(first_type);
                find = 1;
                break;
            }
            if (find) break;
            else {
                fprintf(stderr, "Type inference error: cannot find a corresponding type for field predicate %s", sep->data.pred->name);
                ERROR("");
            }
        }
    }
    case PATTERN_SEP_PATPRED: {
        struct mappingValue * mv = charMappingFind(sep->data.ppred->var, type_mapping);
        if (mv == NULL || mv->val == NULL) {
            struct PatternPolyType * t = type_infer_expr_list(sep->data.ppred->args, env, PatternPolyTypeDeepCopy(ret));
            charMappingInsert(sep->data.ppred->var, initPatternPolyTypeMappingValue(t, 1), type_mapping);
            break;
        }
        struct PatternPolyType * t = mv->val;
        struct PatternPolyType * ret = get_ret_type(t);
        struct PatternPolyType * t1 = type_infer_expr_list(sep->data.ppred->args, env, PatternPolyTypeDeepCopy(ret));
        if (!unify(t, t1)) unify_error(t, t1);
        PatternPolyTypeFree(t1);
        break;
    }
    }
    return ret;
}

struct StrategyLibRule * type_infer(struct StrategyLibRule * rule, struct environment * env) {
    type_mapping = rule->type_mapping;
    unk_mapping = initCharMapping(1);
    cnt = 1;
    for (struct StrategyLibPatternLList * lcur = rule->pats; lcur != NULL; lcur = lcur->next) {
        for (struct StrategyLibPatternList * cur = lcur->list; cur != NULL; cur = cur->next) {
            struct StrategyLibPattern * pat = cur->pat;
            if (pat->ty == STRATEGY_LIB_PATTERN_PROP) PatternPolyTypeFree(type_infer_prop(pat->pat.prop, env));
            else PatternPolyTypeFree(type_infer_sep(pat->pat.sep, env));
        }
    }
    for (struct StrategyLibCheckList * cur = rule->checks; cur != NULL; cur = cur->next) {
        struct PatternPolyType * t = type_infer_prop(cur->check->data.prop, env);
        struct PatternPolyType * tp = initPatternPolyTypeConst(strdup("Prop"));
        if (!unify(t, tp)) unify_error(t, tp);
        PatternPolyTypeFree(t);
        PatternPolyTypeFree(tp);
    }
    for (struct StrategyLibActionList * cur = rule->actions; cur != NULL; cur = cur->next) {
        struct StrategyLibAction * action = cur->action;
        switch (action->ty) {
        case STRATEGY_LIB_ACTION_DEL_LEFT:
        case STRATEGY_LIB_ACTION_DEL_RIGHT: {
            break;
        }
        case STRATEGY_LIB_ACTION_ADD_LEFT:
        case STRATEGY_LIB_ACTION_ADD_RIGHT: {
            if (action->data.expr->ty == STRATEGY_LIB_PATTERN_PROP) PatternPolyTypeFree(type_infer_prop(action->data.expr->pat.prop, env));
            else PatternPolyTypeFree(type_infer_sep(action->data.expr->pat.sep, env));
            break;
        }
        case STRATEGY_LIB_ACTION_ADD_LEFT_EXIST:
        case STRATEGY_LIB_ACTION_ADD_RIGHT_EXIST: {
            break;
        }
        case STRATEGY_LIB_ACTION_INST:
        case STRATEGY_LIB_ACTION_SUBST: {
            char * x = action->data.mapping->var;
            struct PatternExpr * e = action->data.mapping->expr;
            struct PatternPolyType * t = type_infer_expr(e, env);
            struct mappingValue * mv = charMappingFind(x, type_mapping);
            if (mv == NULL || mv->val == NULL) {
                charMappingInsert(x, initPatternPolyTypeMappingValue(t, 1), type_mapping);
            }
            else {
                if (!unify(mv->val, t)) unify_error(mv->val, t);
            }
        }
        }
    }
    if (exec_info) {
      printf("Type inference result for strategy (%s, %d):\n", rule->filename, rule->id);
      Print_PolyType_mapping(stdout);
      print_unk_mapping(stdout);
    }
    check_type_mapping();

    int debug_id = 0;

    for (struct StrategyLibPatternLList * lcur = rule->pats; lcur != NULL; lcur = lcur->next) {
        for (struct StrategyLibPatternList * cur = lcur->list; cur != NULL; cur = cur->next) {
            struct StrategyLibPattern * pat = cur->pat;
            if (pat->ty == STRATEGY_LIB_PATTERN_PROP) {
                struct PatternPolyType * res = type_infer_prop(pat->pat.prop, env);
                if (res->ty != PATTERN_POLY_CONST) {
                    fprintf(stderr, "Type inference error: left pattern should be of type Prop or Assertion\n");
                    PatternPolyTypePrint(stderr, res);
                    ERROR("");
                }
                if (res->ty == PATTERN_POLY_CONST && strcmp(res->data.var, "Prop") && strcmp(res->data.var, "Assertion")) {
                    fprintf(stderr, "Type inference error: left pattern should be of type Prop or Assertion\n");
                    PatternPolyTypePrint(stderr, res);
                    ERROR("");
                }
                if (!strcmp(res->data.var, "Assertion")) {
                    if (exec_info)
                      printf("Pattern %d is Assertion\n", debug_id);
                    pat->ty = STRATEGY_LIB_PATTERN_SEP;
                    struct PatternProp * temp = pat->pat.prop;
                    pat->pat.sep = initPatternSepPatPred(temp->data.ppred->var, temp->data.ppred->args);
                    free(temp);
                }
                PatternPolyTypeFree(res);
            }
        }
        debug_id += 1;
    }

    debug_id = 0;
    for (struct StrategyLibActionList * cur = rule->actions; cur != NULL; cur = cur->next) {
        struct StrategyLibAction * action = cur->action;
        switch (action->ty) {
          case STRATEGY_LIB_ACTION_ADD_LEFT:
          case STRATEGY_LIB_ACTION_ADD_RIGHT: {
            if (action->data.expr->ty == STRATEGY_LIB_PATTERN_PROP) {
                struct PatternPolyType * res = type_infer_prop(action->data.expr->pat.prop, env);
                if (res->ty != PATTERN_POLY_CONST) {
                    fprintf(stderr, "Type inference error: action add pattern should be of type Prop or Assertion\n");
                    ERROR("");
                }
                if (res->ty == PATTERN_POLY_CONST && strcmp(res->data.var, "Prop") && strcmp(res->data.var, "Assertion")) {
                    fprintf(stderr, "Type inference error: action add pattern should be of type Prop or Assertion\n");
                    ERROR("");
                }
                if (!strcmp(res->data.var, "Assertion")) {
                    if (exec_info)
                        printf("Action %d is Assertion\n", debug_id);
                    action->data.expr->ty = STRATEGY_LIB_PATTERN_SEP;
                    struct PatternProp * temp = action->data.expr->pat.prop;
                    action->data.expr->pat.sep = initPatternSepPatPred(temp->data.ppred->var, temp->data.ppred->args);
                    free(temp);
                }
                PatternPolyTypeFree(res);
            }
            break;
          }
          case STRATEGY_LIB_ACTION_ADD_LEFT_EXIST: 
          case STRATEGY_LIB_ACTION_ADD_RIGHT_EXIST:{
            struct mappingValue * mv = charMappingFind(action->data.var->name, type_mapping);
            if (mv == NULL || mv ->val == NULL) {
              fprintf(stderr, "Type inference error: type of pattern variable %s is not inferred in type environment\n", action->data.var->name);
              ERROR("");
            }
            if (action->data.var->type != NULL && !PatternPolyTypeEqual(mv->val, action->data.var->type)) {
              fprintf(stderr, "Type inference error: type of pattern variable %s is not consistent with the type in type environment\n", action->data.var->name);
              fprintf(stderr, "The original type is : ");
              PatternPolyTypePrint(stderr, action->data.var->type);
              fprintf(stderr, "\n");
              fprintf(stderr, "The type in type environment is : ");
              PatternPolyTypePrint(stderr, mv->val);
              fprintf(stderr, "\n");
              ERROR("");
            }
            action->data.var->type = PatternPolyTypeDeepCopy(mv->val);
          }
          default : {

          }
        }
        debug_id += 1;
    }

    finiCharMapping(unk_mapping);
    return rule;
}

struct PatternPolyType * type_infer_pattern_expr(struct PatternExpr * expr, struct charMapping * tm, struct environment * env) {
    type_mapping = tm;
    unk_mapping = initCharMapping(1);
    cnt = 1;
    struct PatternPolyType * ret = type_infer_expr(expr, env);
    finiCharMapping(unk_mapping);
    return ret;
}