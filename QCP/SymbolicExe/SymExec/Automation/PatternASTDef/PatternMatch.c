#include "PatternMatch.h"

struct SimpleCtype * instPatternCType(struct PatternCType * type,
                                      struct charMapping * mapping,
                                      struct environment * env) {
    switch (type->ty) {
    case PATTERN_CTYPE_VOID: return SimpleCtypeVoid();
    case PATTERN_CTYPE_C8: return SimpleCtypeInt8(type->data.ti->s);
    case PATTERN_CTYPE_C16: return SimpleCtypeInt16(type->data.ti->s);
    case PATTERN_CTYPE_C32: return SimpleCtypeInt32(type->data.ti->s);
    case PATTERN_CTYPE_C64: return SimpleCtypeInt64(type->data.ti->s);
    case PATTERN_CTYPE_PTR: return SimpleCtypePointer(instPatternCType(type->data.tptr->type, mapping, env));
    case PATTERN_CTYPE_ARR: return SimpleCtypeArray(instPatternCType(type->data.tarr->type, mapping, env), type->data.tarr->length);
    case PATTERN_CTYPE_FUNC: return SimpleCtypeFunction(instPatternCType(type->data.tfunc->ret_type, mapping, env), instPatternCTypeList(type->data.tfunc->arg_list, mapping, env));
    case PATTERN_CTYPE_STRUCT: {
        int id = find_struct_or_union_by_name(type->data.tstruct->struct_name, &env->ephemer)->id;
        return SimpleCtypeStruct(id);
    }
    case PATTERN_CTYPE_UNION: {
        int id = find_struct_or_union_by_name(type->data.tunion->union_name, &env->ephemer)->id;
        return SimpleCtypeUnion(id);
    }
    case PATTERN_CTYPE_ENUM: {
        int id = find_enum_by_name(type->data.tenum->enum_name, &env->ephemer)->id;
        return SimpleCtypeEnum(id);
    }
    case PATTERN_CTYPE_VAR: {
        struct mappingValue * mv = charMappingFind(type->data.var, mapping);
        if (mv == NULL) {
            fprintf(stderr, "Pattern variable %s is not assigned a context in instPatternCType()\n", type->data.var);
            ERROR("");
        }
        return SimpleCtypeDeepCopy(mv->val);
    }
    default: {
        ERROR("Unknown type in instPatternCType");
    }
    }
}

int matchCType(struct SimpleCtype * ctx,
                struct PatternCType * pat,
                struct charMapping * pat_mapping,
                struct environment * env) {
    if (ctx == NULL && pat == NULL) return 1;
    if (ctx == NULL || pat == NULL) return 0;
    switch (pat->ty) {
    case PATTERN_CTYPE_VAR: {
        struct mappingValue * mv = charMappingFind(pat->data.var, pat_mapping);
        if (mv == NULL) {
            charMappingInsert(pat->data.var, initCTypeMappingValue(ctx, 0), pat_mapping);
            return 1;
        }
        else if (!SimpleCtypeCheckAcceptable(mv->val, ctx)) return 0;
        return 1;
    }
    case PATTERN_CTYPE_VOID: {
        if (ctx->t != C_void) return 0;
        return 1;
    }
    case PATTERN_CTYPE_C8: {
        if (ctx->t != C_int8 || ctx->d.CINT8.s != pat->data.ti->s) return 0;
        return 1;
    }
    case PATTERN_CTYPE_C16: {
        if (ctx->t != C_int16 || ctx->d.CINT16.s != pat->data.ti->s) return 0;
        return 1;
    }
    case PATTERN_CTYPE_C32: {
        if (ctx->t != C_int32 || ctx->d.CINT32.s != pat->data.ti->s) return 0;
        return 1;
    }
    case PATTERN_CTYPE_C64: {
        if (ctx->t != C_int64 || ctx->d.CINT64.s != pat->data.ti->s) return 0;
        return 1;
    }
    case PATTERN_CTYPE_PTR: {
        if (ctx->t != C_pointer) return 0;
        return matchCType(ctx->d.CPOINTER.type, pat->data.tptr->type, pat_mapping, env);
    }
    case PATTERN_CTYPE_ARR: {
        if (ctx->t != C_array) return 0;
        if (ctx->d.CARRAY.length != pat->data.tarr->length) return 0;
        return matchCType(ctx->d.CARRAY.type, pat->data.tarr->type, pat_mapping, env);
    }
    case PATTERN_CTYPE_FUNC: {
        if (ctx->t != C_function) return 0;
        if (!matchCType(ctx->d.CFUNC.ret_type, pat->data.tfunc->ret_type, pat_mapping, env)) return 0;
        return matchCTypeList(ctx->d.CFUNC.arg_list->head, pat->data.tfunc->arg_list, pat_mapping, env);
    }
    case PATTERN_CTYPE_STRUCT: {
        if (ctx->t != C_struct) return 0;
        struct struct_union_info * info = find_struct_by_id(ctx->d.CSTRUCT.struct_id, &env->persist);
        if (strcmp(info->name, pat->data.tstruct->struct_name)) return 0;
        return 1;
    }
    case PATTERN_CTYPE_UNION: {
        if (ctx->t != C_union) return 0;
        struct struct_union_info * info = find_union_by_id(ctx->d.CUNION.union_id, &env->persist);
        if (strcmp(info->name, pat->data.tunion->union_name)) return 0;
        return 1;
    }
    case PATTERN_CTYPE_ENUM: {
        if (ctx->t != C_enum) return 0;
        struct enum_info * info = find_enum_by_id(ctx->d.CENUM.enum_id, &env->persist);
        if (strcmp(info->name, pat->data.tenum->enum_name)) return 0;
        return 1;
    }
    default: {
        ERROR("Unknown type in matchCType");
    }
    }
    return 0;
}

int matchCTypeList(struct SimpleCtypeListNode * cl,
                   struct PatternCTypeList * pl,
                   struct charMapping * pat_mapping,
                   struct environment * env) {
    if (cl == NULL && pl == NULL) return 1;
    if (cl == NULL || pl == NULL) return 0;
    if (!matchCType(cl->data, pl->type, pat_mapping, env)) return 0;
    return matchCTypeList(cl->next, pl->next, pat_mapping, env);
}

struct SimpleCtypeList * instPatternCTypeList(struct PatternCTypeList * type_list,
                                              struct charMapping * mapping,
                                              struct environment * env) {
    if (type_list == NULL) return SimpleCtypeListNil();
    return SimpleCtypeListCons(instPatternCType(type_list->type, mapping, env), instPatternCTypeList(type_list->next, mapping, env));
}


int matchExprVal(struct ExprVal * ctx,
                 struct PatternExpr * pat,
                 struct charMapping * pat_mapping,
                 struct intMapping * exist_mapping,
                 struct environment * env) {
    if (ctx == NULL && pat == NULL) return 1;
    if (ctx == NULL || pat == NULL) return 0;
    switch (pat->ty) {
    case PATTERN_EXPR_CONST: {
        if (ctx->t != EZ_VAL || ctx->d.EZ_VAL.number!= pat->data.num)  return 0;
        return 1;
    }
    case PATTERN_EXPR_VAR: {
        char * var = pat->data.var;
        struct mappingValue * expr = charMappingFind(var, pat_mapping);
        if (expr == NULL) {
            charMappingInsert(var, initExprValMappingValue(ctx, 0), pat_mapping);
            return 1;
        }
        else if (!ExprValCheckEqual(expr->val, ctx)) return 0;
        return 1;
    }
    case PATTERN_EXPR_EVAR: {
        if (ctx->t != FUNCAPP || !ExprValListIsEmpty(ctx->d.FUNCAPP.args)) return 0;
        if (!intMappingIn(ctx->d.FUNCAPP.id, exist_mapping)) return 0;
        char * var = pat->data.var;
        struct mappingValue * expr = charMappingFind(var, pat_mapping);
        if (expr == NULL) {
            charMappingInsert(var, initExprValMappingValue(ctx, 0), pat_mapping);
            return 1;
        }
        else if (!ExprValCheckEqual(expr->val, ctx)) return 0;
        return 1;
    }
    case PATTERN_EXPR_SVAR: {
        if (ctx->t != FUNCAPP || !ExprValListIsEmpty(ctx->d.FUNCAPP.args)) return 0;
        char * var = pat->data.var;
        struct mappingValue * expr = charMappingFind(var, pat_mapping);
        if (expr == NULL) {
            charMappingInsert(var, initExprValMappingValue(ctx, 0), pat_mapping);
            return 1;
        }
        else if (!ExprValCheckEqual(expr->val, ctx)) return 0;
        return 1;
    }
    case PATTERN_EXPR_GVAR: {
        if (ctx->t != FUNCAPP) return 0;
        struct var_scope_union * global_var = find_prog_var_by_name(pat->data.var, &env->ephemer);
        if (global_var == NULL) return 0;
        if (global_var->d.prog_var->address->id != ctx->d.FUNCAPP.id) return 0;
        return 1;
    }
    case PATTERN_EXPR_UNOP: {
        if (ctx->t != VUOP) return 0;
        if (pat->data.unop->op != ctx->d.VUOP.op) return 0;
        if (!matchExprVal(ctx->d.VUOP.expr, pat->data.unop->expr, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    case PATTERN_EXPR_BINOP: {
        if (ctx->t != VBOP) return 0;
        if (pat->data.binop->op != ctx->d.VBOP.op) return 0;
        if (!matchExprVal(ctx->d.VBOP.expr1, pat->data.binop->left, pat_mapping, exist_mapping, env)) return 0;
        if (!matchExprVal(ctx->d.VBOP.expr2, pat->data.binop->right, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    case PATTERN_EXPR_APP: {
        if (ctx->t != FUNCAPP) return 0;
        if (pat->data.app->id != ctx->d.FUNCAPP.id) return 0;
        if (!matchPolyTypeList(ctx->d.FUNCAPP.types->head, pat->data.app->type_list, pat_mapping, exist_mapping, env)) return 0;
        if (!matchExprValList(ctx->d.FUNCAPP.args->head, pat->data.app->expr_list, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    case PATTERN_EXPR_PATAPP: {
        if (ctx->t != FUNCAPP) return 0;
        char * var = pat->data.papp->var;
        struct mappingValue * mv = charMappingFind(var, pat_mapping);
        struct ExprVal * e = ExprVal_FUNCAPP(ctx->d.FUNCAPP.id,
                                             PolyTypeListDeepCopy(ctx->d.FUNCAPP.types),
                                             ExprValListNil());
        if (mv == NULL) {
            charMappingInsert(var, initExprValMappingValue(e, 1), pat_mapping);
        }
        else {
            if (!ExprValCheckEqual(mv->val, e)) {
                ExprValFree(e);
                return 0;
            }
            ExprValFree(e);    
        }
        if (!matchExprValList(ctx->d.FUNCAPP.args->head, pat->data.papp->expr_list, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    case PATTERN_EXPR_FIELD: {
        if (ctx->t != VFIELD_ADDRESS) return 0;
        struct field_info * f = find_field_by_id(ctx->d.VFIELD_ADDRESS.field_id, &env->persist);
        char * struct_name = f->parent->name;
        char * field_name = f->name;
        if (strcmp(field_name, pat->data.field->field_name) != 0) return 0;
        if (strcmp(struct_name, pat->data.field->struct_name) != 0) return 0;
        if (!matchExprVal(ctx->d.VFIELD_ADDRESS.expr, pat->data.field->expr, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    case PATTERN_EXPR_ARRIDX : {
        if (ctx->t != LINDEX) return 0;
        if (!matchExprVal(ctx->d.LINDEX.list, pat->data.arridx->array, pat_mapping, exist_mapping, env)) return 0;
        if (!matchExprVal(ctx->d.LINDEX.index, pat->data.arridx->index, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    case PATTERN_EXPR_SIZEOF: {
        if (ctx->t != SIZE_OF) return 0;
        if (!matchCType(ctx->d.SIZE_OF.type, pat->data.sizeof_expr, pat_mapping, env)) return 0;
        return 1;
    }
    default: {
        ERROR("Not implemented in matchExprVal()");
    }
    }
}

int matchExprValList(struct ExprValListNode * cl,
                     struct PatternExprList * pl,
                     struct charMapping * pat_mapping,
                     struct intMapping * exist_mapping, 
                     struct environment * env) {
    if (cl == NULL && pl == NULL) return 1;
    if (cl == NULL || pl == NULL) return 0;
    if (!matchExprVal(cl->data, pl->expr, pat_mapping, exist_mapping, env)) return 0;
    return matchExprValList(cl->next, pl->next, pat_mapping, exist_mapping, env);
}

struct ExprVal * instPatternExpr(struct PatternExpr * expr,
                                 struct charMapping * pat_mapping,
                                 struct environment * env) {
    if (expr == NULL) return NULL;
    if (expr->ty == PATTERN_EXPR_VAR ||
        expr->ty == PATTERN_EXPR_EVAR ||
        expr->ty == PATTERN_EXPR_SVAR) {
        struct mappingValue * mv = charMappingFind(expr->data.var, pat_mapping);
        if (mv == NULL) {
            fprintf(stderr, "Pattern variable %s is not assigned a context in instPatternExpr()\n", expr->data.var);
            ERROR("");
        }
        return ExprValDeepCopy(mv->val);
    }
    struct ExprVal * ret = (struct ExprVal *) malloc(sizeof(struct ExprVal));
    switch (expr->ty) {
    case PATTERN_EXPR_CONST: {
        ret->t = EZ_VAL;
        ret->d.EZ_VAL.number = expr->data.num;
        break;
    }
    case PATTERN_EXPR_GVAR: {
        ret->t = FUNCAPP;
        struct var_scope_union * global_var = find_prog_var_by_name(expr->data.var, &env->ephemer);
        if (global_var == NULL) {
            fprintf(stderr, "Can't find global variable %s in environment\n", expr->data.var);
            ERROR("");
        }
        ret->d.FUNCAPP.id = global_var->d.prog_var->address->id;
        ret->d.FUNCAPP.args = ExprValListNil();
        ret->d.FUNCAPP.types = PolyTypeListNil();
        break;
    }
    case PATTERN_EXPR_UNOP: {
        ret->t = VUOP;
        ret->d.VUOP.op = expr->data.unop->op;
        ret->d.VUOP.expr = instPatternExpr(expr->data.unop->expr, pat_mapping, env);
        break;
    }
    case PATTERN_EXPR_BINOP: {
        ret->t = VBOP;
        ret->d.VBOP.op = expr->data.binop->op;
        ret->d.VBOP.expr1 = instPatternExpr(expr->data.binop->left, pat_mapping, env);
        ret->d.VBOP.expr2 = instPatternExpr(expr->data.binop->right, pat_mapping, env);
        break;
    }
    case PATTERN_EXPR_APP: {
        ret->t = FUNCAPP;
        ret->d.FUNCAPP.id = expr->data.app->id;
        ret->d.FUNCAPP.args = instPatternExprList(expr->data.app->expr_list, pat_mapping, env);
        ret->d.FUNCAPP.types = instPatternPolyTypeList(expr->data.app->type_list, pat_mapping, env);
        break;
    }
    case PATTERN_EXPR_PATAPP: {
        char * var = expr->data.papp->var;
        struct mappingValue * mv = charMappingFind(var, pat_mapping);
        if (mv == NULL) {
            fprintf(stderr, "Function pattern variable %s is not assigned a context variable\n", var);
            ERROR("");
        }
        struct ExprVal * real_expr = mv->val;
        ret->t = FUNCAPP;
        ret->d.FUNCAPP.id = real_expr->d.FUNCAPP.id;
        ret->d.FUNCAPP.types = PolyTypeListDeepCopy(real_expr->d.FUNCAPP.types);
        ret->d.FUNCAPP.args = instPatternExprList(expr->data.papp->expr_list, pat_mapping, env);
        break;
    }
    case PATTERN_EXPR_FIELD: {
        ret->t = VFIELD_ADDRESS;
        ret->d.VFIELD_ADDRESS.field_id = -1;
        struct struct_union_info * info = find_struct_or_union_by_name(expr->data.field->struct_name, &env->ephemer);
        if (info == NULL) {
            fprintf(stderr, "Can't find %s in environment\n", expr->data.field->struct_name);
            ERROR("");
        }
        for (struct field_info * f = info->first_field; f; f = f->next) {
            if (!strcmp(f->name, expr->data.field->field_name)) {
                ret->d.VFIELD_ADDRESS.field_id = f->id;
                break;
            }
        }
        if (!~ret->d.VFIELD_ADDRESS.field_id) {
            fprintf(stderr, "Field %s not found in instPatternExpr()\n", expr->data.field->field_name);
            ERROR("");
        }
        ret->d.VFIELD_ADDRESS.expr = instPatternExpr(expr->data.field->expr, pat_mapping, env);
        break;
    }
    case PATTERN_EXPR_ARRIDX: {
        ret->t = LINDEX;
        ret->d.LINDEX.list = instPatternExpr(expr->data.arridx->array, pat_mapping, env);
        ret->d.LINDEX.index = instPatternExpr(expr->data.arridx->index, pat_mapping, env);
        break;
    }
    case PATTERN_EXPR_SIZEOF: {
        ret->t = SIZE_OF;
        ret->d.SIZE_OF.type = instPatternCType(expr->data.sizeof_expr, pat_mapping, env);
        break;
    }
    default: {
        ERROR("Not implemented in instPatternExprVal()");
    }
    }
    return ret;
}

struct ExprValList * instPatternExprList(struct PatternExprList * expr_list,
                                         struct charMapping * pat_mapping,
                                         struct environment * env) {
    if (expr_list == NULL) return ExprValListNil();
    return ExprValListCons(instPatternExpr(expr_list->expr, pat_mapping, env),
                           instPatternExprList(expr_list->next, pat_mapping, env));
}


int matchPolyTypeList(struct PolyTypeListNode * cl,
                      struct PatternPolyTypeList * pl,
                      struct charMapping * pat_mapping,
                      struct intMapping * exist_mapping,
                      struct environment * env) {
    if (cl == NULL && pl == NULL) return 1;
    if (cl == NULL || pl == NULL) return 0;
    if (!matchPolyType(cl->data, pl->head, pat_mapping, exist_mapping, env)) return 0;
    return matchPolyTypeList(cl->next, pl->next, pat_mapping, exist_mapping, env);
}

int matchPolyType(struct PolyType * ctx,
                  struct PatternPolyType * pat,
                  struct charMapping * pat_mapping,
                  struct intMapping * exist_mapping,
                  struct environment * env) {
    if (ctx == NULL && pat == NULL) return 1;
    if (ctx == NULL || pat == NULL) return 0;
    switch (pat->ty) {
    case PATTERN_POLY_CONST: {
        if (ctx->t == POLY_VAR) {
            char * name = find_atype_by_id(ctx->d.VAR.id, &env->persist)->name;
            if (strcmp(name, pat->data.var)) return 0;
        } else if (ctx->t == POLY_FUNCAPP) {
            char * name = find_atype_by_id(ctx->d.FUNCAPP.func, &env->persist)->name;
            if (strcmp(name, pat->data.var) || !PolyTypeListIsEmpty(ctx->d.FUNCAPP.args)) return 0;
        }
        return 1;
    }
    case PATTERN_POLY_VAR: {
        char * var = pat->data.var;
        struct mappingValue * val = charMappingFind(var, pat_mapping);
        if (val == NULL) {
            charMappingInsert(var, initPolyTypeMappingValue(ctx, 0), pat_mapping);
            return 1;
        }
        else if (!PolyTypeCheckEqual(val->val, ctx)) return 0;
        return 1;
    }
    case PATTERN_POLY_APP: {
        if (ctx->t != POLY_FUNCAPP) return 0;
        char * name = find_atype_by_id(ctx->d.FUNCAPP.func, &env->persist)->name;
        if (strcmp(name, pat->data.app->func)) return 0;
        struct PolyTypeListNode * ctx_args = ctx->d.FUNCAPP.args->head;
        struct PatternPolyTypeList * pat_args = pat->data.app->args;
        if (!matchPolyTypeList(ctx_args, pat_args, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    case PATTERN_POLY_ARROW: {
        if (ctx->t != POLY_ARROW) return 0;
        if (!matchPolyType(ctx->d.ARROW.left, pat->data.arrow->left, pat_mapping, exist_mapping, env)) return 0;
        if (!matchPolyType(ctx->d.ARROW.right, pat->data.arrow->right, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    default: {
        ERROR("Not implemented in matchPolyType()");
    }
    }
}

struct PolyTypeList * instPatternPolyTypeList(struct PatternPolyTypeList * pl,
                                              struct charMapping * pat_mapping,
                                              struct environment * env) {
    if (pl == NULL) return PolyTypeListNil();
    return PolyTypeListCons(instPatternPolyType(pl->head, pat_mapping, env),
                            instPatternPolyTypeList(pl->next, pat_mapping, env));
}

struct PolyType *instPatternPolyType(struct PatternPolyType * pat,
                                     struct charMapping * pat_mapping,
                                     struct environment * env) {
    if (pat == NULL) return NULL;
    switch (pat->ty) {
    case PATTERN_POLY_CONST: {
        int id = find_atype_by_name(pat->data.var, &env->ephemer)->id;
        return PolyTypeFuncApp(id, PolyTypeListNil());
    }
    case PATTERN_POLY_VAR: {
        struct mappingValue * val = charMappingFind(pat->data.var, pat_mapping);
        if (val == NULL) {
            fprintf(stderr, "Pattern variable %s is not assigned a context in instPatternPolyType()\n", pat->data.var);
            ERROR("");
        }
        return PolyTypeDeepCopy(val->val);
    }
    case PATTERN_POLY_APP: {
        struct PolyTypeList * args = instPatternPolyTypeList(pat->data.app->args, pat_mapping, env);
        int id = find_atype_by_name(pat->data.app->func, &env->ephemer)->id;
        return PolyTypeFuncApp(id, args);
    }
    case PATTERN_POLY_ARROW: {
        struct PolyType * left = instPatternPolyType(pat->data.arrow->left, pat_mapping, env);
        struct PolyType * right = instPatternPolyType(pat->data.arrow->right, pat_mapping, env);
        return PolyTypeArrow(left, right);
    }
    default: {
        ERROR("Not implemented in instPatternPolyType()");
    }
    }
}

int matchProposition(struct Proposition * ctx,
                     struct PatternProp * pat,
                     struct charMapping * pat_mapping,
                     struct intMapping * exist_mapping,
                     struct environment * env) {
    if (ctx == NULL && pat == NULL) return 1;
    if (ctx == NULL || pat == NULL) return 0;
    switch (pat->ty) {
    case PATTERN_PROP_TRUE: {
        return ctx->t == T_PROP_TRUE;
    }
    case PATTERN_PROP_FALSE: {
        return ctx->t == T_PROP_FALSE;
    }
    case PATTERN_PROP_UNOP: {
        if (ctx->t != T_PROP_UNARY) return 0;
        if (ctx->d.UNARY.op != pat->data.unop->op) return 0;
        if (!matchProposition(ctx->d.UNARY.prop, pat->data.unop->prop, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    case PATTERN_PROP_BINOP: {
        if (ctx->t != T_PROP_BINARY) return 0;
        if (ctx->d.BINARY.op != pat->data.binop->op) return 0;
        if (!matchProposition(ctx->d.BINARY.prop1, pat->data.binop->left, pat_mapping, exist_mapping, env)) return 0;
        if (!matchProposition(ctx->d.BINARY.prop2, pat->data.binop->right, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    case PATTERN_PROP_PTR: {
        if (ctx->t != T_PROP_PTR) return 0;
        if (ctx->d.PTR.op != pat->data.ptr->op) return 0;
        if (!matchExprVal(ctx->d.PTR.expr, pat->data.ptr->expr, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    case PATTERN_PROP_COMPARE: {
        if (ctx->t != T_PROP_COMPARE) return 0;
        if (ctx->d.COMPARE.op != pat->data.comp->op) return 0;
        if (!matchExprVal(ctx->d.COMPARE.expr1, pat->data.comp->left, pat_mapping, exist_mapping, env)) return 0;
        if (!matchExprVal(ctx->d.COMPARE.expr2, pat->data.comp->right, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    case PATTERN_PROP_PRED: {
        if (ctx->t != T_PROP_OTHER) return 0;
        if (ctx->d.OTHER.predicate != pat->data.pred->id) return 0;
        if (!matchPolyTypeList(ctx->d.OTHER.types->head, pat->data.pred->types, pat_mapping, exist_mapping, env)) return 0;
        if (!matchExprValList(ctx->d.OTHER.args->head, pat->data.pred->args, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    case PATTERN_PROP_PATPRED: {
        if (ctx->t != T_PROP_OTHER) return 0;
        char * var = pat->data.ppred->var;
        struct mappingValue * mv = charMappingFind(var, pat_mapping);
        struct ExprVal * e = ExprVal_FUNCAPP(ctx->d.OTHER.predicate,
                                             PolyTypeListDeepCopy(ctx->d.OTHER.types),
                                             ExprValListNil());
        if (mv == NULL) {
            charMappingInsert(var, initExprValMappingValue(e, 1), pat_mapping);
        }
        else {
            if (!ExprValCheckEqual(mv->val, e)) {
                ExprValFree(e);
                return 0;
            }
            ExprValFree(e);
        }
        if (!matchExprValList(ctx->d.OTHER.args->head, pat->data.ppred->args, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    default: {
        ERROR("Not implemented in matchProposition()");
    }
    }
}

struct Proposition * instPatternProp(struct PatternProp * prop,
                                     struct charMapping * pat_mapping,
                                     struct environment * env) {
    if (prop == NULL) return NULL;
    struct Proposition * ret = (struct Proposition *) malloc(sizeof(struct Proposition));
    switch (prop->ty) {
    case PATTERN_PROP_TRUE: {
        ret->t = T_PROP_TRUE;
        break;
    }
    case PATTERN_PROP_FALSE: {
        ret->t = T_PROP_FALSE;
        break;
    }
    case PATTERN_PROP_UNOP: {
        ret->t = T_PROP_UNARY;
        ret->d.UNARY.op = prop->data.unop->op;
        ret->d.UNARY.prop = instPatternProp(prop->data.unop->prop, pat_mapping, env);
        break;
    }
    case PATTERN_PROP_BINOP: {
        ret->t = T_PROP_BINARY;
        ret->d.BINARY.op = prop->data.binop->op;
        ret->d.BINARY.prop1 = instPatternProp(prop->data.binop->left, pat_mapping, env);
        ret->d.BINARY.prop2 = instPatternProp(prop->data.binop->right, pat_mapping, env);
        break;
    }
    case PATTERN_PROP_PTR: {
        ret->t = T_PROP_PTR;
        ret->d.PTR.op = prop->data.ptr->op;
        ret->d.PTR.expr = instPatternExpr(prop->data.ptr->expr, pat_mapping, env);
        break;
    }
    case PATTERN_PROP_COMPARE: {
        ret->t = T_PROP_COMPARE;
        ret->d.COMPARE.op = prop->data.comp->op;
        ret->d.COMPARE.expr1 = instPatternExpr(prop->data.comp->left, pat_mapping, env);
        ret->d.COMPARE.expr2 = instPatternExpr(prop->data.comp->right, pat_mapping, env);
        break;
    }
    case PATTERN_PROP_PRED: {
        ret->t = T_PROP_OTHER;
        ret->d.OTHER.predicate = prop->data.pred->id;
        ret->d.OTHER.types = instPatternPolyTypeList(prop->data.pred->types, pat_mapping, env);
        ret->d.OTHER.args = instPatternExprList(prop->data.pred->args, pat_mapping, env);
        break;
    }
    case PATTERN_PROP_PATPRED: {
        ret->t = T_PROP_OTHER;
        char * var = prop->data.ppred->var;
        struct mappingValue * mv = charMappingFind(prop->data.ppred->var, pat_mapping);
        if (mv == NULL) {
            fprintf(stderr, "Prop function pattern variable %s is not assigned a context\n", var);
            ERROR("");
        }
        struct ExprVal * e = mv->val;
        ret->d.OTHER.predicate = e->d.FUNCAPP.id;
        ret->d.OTHER.types = PolyTypeListDeepCopy(e->d.FUNCAPP.types);
        ret->d.OTHER.args = instPatternExprList(prop->data.ppred->args, pat_mapping, env);
        break;
    }
    default: {
        ERROR("Not implemented in instPatternProp()");
    }
    }
    return ret;
}

int matchSeparation(struct Separation * ctx,
                    struct PatternSep * pat,
                    struct charMapping * pat_mapping,
                    struct intMapping * exist_mapping,
                    struct environment * env) {
    if (ctx == NULL && pat == NULL) return 1;
    if (ctx == NULL || pat == NULL) return 0;
    switch (pat->ty) {
    case PATTERN_SEP_DATA_AT: {
        if (ctx->t != T_DATA_AT) return 0;
        if (!matchExprVal(ctx->d.DATA_AT.left, pat->data.data_at->addr, pat_mapping, exist_mapping, env)) return 0;
        if (!matchCType(ctx->d.DATA_AT.ty, pat->data.data_at->ty, pat_mapping, env)) return 0;
        if (!matchExprVal(ctx->d.DATA_AT.right, pat->data.data_at->data, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    case PATTERN_SEP_UNDEF: {
        if (ctx->t != T_UNDEF_DATA_AT) return 0;
        if (!matchExprVal(ctx->d.UNDEF_DATA_AT.left, pat->data.undef_data_at->addr, pat_mapping, exist_mapping, env)) return 0;
        if (!matchCType(ctx->d.UNDEF_DATA_AT.ty, pat->data.undef_data_at->ty, pat_mapping, env)) return 0;
        return 1;
    }
    case PATTERN_SEP_PRED: {
        if (ctx->t != T_OTHER) return 0;
        if (ctx->d.OTHER.sep_id != pat->data.pred->id) return 0;
        if (!matchPolyTypeList(ctx->d.OTHER.types->head, pat->data.pred->types, pat_mapping, exist_mapping, env)) return 0;
        if (!matchExprValList(ctx->d.OTHER.exprs->head, pat->data.pred->args, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    case PATTERN_SEP_ARR: {
        if (ctx->t != T_ARR) return 0;
        if (!matchExprVal(ctx->d.ARR.addr, pat->data.arr->addr, pat_mapping, exist_mapping, env)) return 0;
        if (!matchCType(ctx->d.ARR.ty, pat->data.arr->ty, pat_mapping, env)) return 0;
        if (!matchExprVal(ctx->d.ARR.value, pat->data.arr->val, pat_mapping, exist_mapping, env)) return 0;
        if (!matchExprVal(ctx->d.ARR.size, pat->data.arr->size, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    case PATTERN_SEP_PATPRED: {
        if (ctx->t != T_OTHER) return 0;
        char * var = pat->data.ppred->var;
        struct ExprVal * e = ExprVal_FUNCAPP(ctx->d.OTHER.sep_id,
                                             PolyTypeListDeepCopy(ctx->d.OTHER.types),
                                             ExprValListNil());
        struct mappingValue * mv = charMappingFind(var, pat_mapping);
        if (mv == NULL) {
            charMappingInsert(var, initExprValMappingValue(e, 1), pat_mapping);
        }
        else {
            if (!ExprValCheckEqual(mv->val, e)) {
                ExprValFree(e);
                return 0;
            }
            ExprValFree(e);
        }
        if (!matchExprValList(ctx->d.OTHER.exprs->head, pat->data.ppred->args, pat_mapping, exist_mapping, env)) return 0;
        return 1;
    }
    default: {
        ERROR("Not implemented in matchSeparation()");
    }
    }
}

struct Separation * instPatternSep(struct PatternSep * sep,
                                   struct charMapping * pat_mapping,
                                   struct environment * env) {
    if (sep == NULL) return NULL;
    struct Separation * ret = (struct Separation *) malloc(sizeof(struct Separation));
    // printf("DEBUG: %d\n", sep->ty == PATTERN_SEP_PATPRED);
    switch (sep->ty) {
    case PATTERN_SEP_DATA_AT: {
        ret->t = T_DATA_AT;
        ret->d.DATA_AT.left = instPatternExpr(sep->data.data_at->addr, pat_mapping, env);
        ret->d.DATA_AT.ty = instPatternCType(sep->data.data_at->ty, pat_mapping, env);
        ret->d.DATA_AT.right = instPatternExpr(sep->data.data_at->data, pat_mapping, env);
        break;
    }
    case PATTERN_SEP_UNDEF: {
        ret->t = T_UNDEF_DATA_AT;
        ret->d.UNDEF_DATA_AT.ty = instPatternCType(sep->data.undef_data_at->ty, pat_mapping, env);
        ret->d.UNDEF_DATA_AT.left = instPatternExpr(sep->data.undef_data_at->addr, pat_mapping, env);
        break;
    }
    case PATTERN_SEP_PRED: {
        ret->t = T_OTHER;
        ret->d.OTHER.sep_id = sep->data.pred->id;
        ret->d.OTHER.types = instPatternPolyTypeList(sep->data.pred->types, pat_mapping, env);
        ret->d.OTHER.exprs = instPatternExprList(sep->data.pred->args, pat_mapping, env);
        break;
    }
    case PATTERN_SEP_ARR: {
        ret->t = T_ARR;
        ret->d.ARR.addr = instPatternExpr(sep->data.arr->addr, pat_mapping, env);
        ret->d.ARR.ty = instPatternCType(sep->data.arr->ty, pat_mapping, env);
        ret->d.ARR.value = instPatternExpr(sep->data.arr->val, pat_mapping, env);
        ret->d.ARR.size = instPatternExpr(sep->data.arr->size, pat_mapping, env);
        break;
    }
    case PATTERN_SEP_PATPRED: {
        ret->t = T_OTHER;
        char * var = sep->data.ppred->var;
        struct mappingValue * mv = charMappingFind(var, pat_mapping);
        if (mv == NULL) {
            fprintf(stderr, "Sep function pattern variable %s is not assigned a context\n", var);
            ERROR("");
        }
        struct ExprVal * e = mv->val;
        ret->d.OTHER.sep_id = e->d.FUNCAPP.id;
        ret->d.OTHER.types = PolyTypeListDeepCopy(e->d.FUNCAPP.types);
        ret->d.OTHER.exprs = instPatternExprList(sep->data.ppred->args, pat_mapping, env);
        break;
    }
    default: {
        ERROR("Not implemented in instPatternSep()");
    }
    }
    return ret;
}