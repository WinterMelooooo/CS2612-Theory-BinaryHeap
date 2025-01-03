#include "PatternPrintLib.h"

void print_tabs(int num_tabs, FILE * fp) {
    for (int i = 0; i < num_tabs; i++)
       fprintf(fp, TAB);
}

void printPatternExpr(struct PatternExpr * expr, FILE * fp, struct charMapping * type_mapping, struct environment * env) {
    if (expr == NULL) return;
    switch (expr->ty) {
    case PATTERN_EXPR_VAR:
    case PATTERN_EXPR_SVAR:
    case PATTERN_EXPR_EVAR: {
        fprintf(fp, "%s", expr->data.var);
        break;
    }
    case PATTERN_EXPR_GVAR: {
        fprintf(fp, " &(\"%s\") ", expr->data.var);
        break;
    }
    case PATTERN_EXPR_UNOP: {
        switch (expr->data.unop->op) {
        case Oneg: {
            fprintf(fp, "(Z.opp ");
            break;
        }
        case Onint:
        case Onot: {
            fprintf(fp, "(Z.lnot ");
            break;
        }
        default: {
            ERROR("Unknown unary operator in printPatternExpr()");
        }
        }
        printPatternExpr(expr->data.unop->expr, fp, type_mapping, env);
        fprintf(fp, ")");
        break;
    }
    case PATTERN_EXPR_BINOP: {
        switch (expr->data.binop->op) {
        case Oadd: {
            fprintf(fp, "(Z.add ");
            break;
        }
        case Osub: {
            fprintf(fp, "(Z.sub ");
            break;
        }
        case Omul: {
            fprintf(fp, "(Z.mul ");
            break;
        }
        case Odiv: {
            fprintf(fp, "(Z.div ");
            break;
        }
        case Omod: {
            fprintf(fp, "(Z.rem ");
            break;
        }
        case Oand: {
            fprintf(fp, "(Z.land ");
            break;
        }
        case Oor: {
            fprintf(fp, "(Z.lor ");
            break;
        }
        case Oxor: {
            fprintf(fp, "(Z.lxor ");
            break;
        }
        case Oshl: {
            fprintf(fp, "(Z.shiftl ");
            break;
        }
        case Oshr: {
            fprintf(fp, "(Z.shiftr ");
            break;
        }
        default: {
            ERROR("Unknown binary operator in printPatternExpr()");
        }
        }
        printPatternExpr(expr->data.binop->left, fp, type_mapping, env);
        fprintf(fp, " ");
        printPatternExpr(expr->data.binop->right, fp, type_mapping, env);
        fprintf(fp, ")");
        break;
    }
    case PATTERN_EXPR_CONST: {
        fprintf(fp, "%llu", expr->data.num);
        break;
    }
    case PATTERN_EXPR_FIELD: {
        fprintf(fp, "&( ");
        fprintf(fp, "((");
        printPatternExpr(expr->data.field->expr, fp, type_mapping, env);
        fprintf(fp, "))");
        fprintf(fp, " # \"%s\" ->ₛ \"%s\")", expr->data.field->struct_name, expr->data.field->field_name);
        break;
    }
    case PATTERN_EXPR_APP: {
        if (expr->data.app->type_list == NULL && expr->data.app->expr_list == NULL) {
            fprintf(fp, "(%s)", expr->data.app->func);
            break;
        }
        fprintf(fp, "(@%s", expr->data.app->func);
        printPatternPolyTypeList(expr->data.app->type_list, fp);
        printPatternExprList(expr->data.app->expr_list, fp, type_mapping, env);
        fprintf(fp, ")");
        break;
    }
    case PATTERN_EXPR_SIZEOF: {
        fprintf(fp, "(@sizeof_front_end_type ");
        printPatternCType(expr->data.sizeof_expr, fp);
        fprintf(fp, ")");
        break;
    }
    case PATTERN_EXPR_ARRIDX: {
        fprintf(fp, "(Znth ");
        printPatternExpr(expr->data.arridx->index, fp, type_mapping, env);
        fprintf(fp, " ");
        printPatternExpr(expr->data.arridx->array, fp, type_mapping, env);
        fprintf(fp, " ");
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
        PatternPolyTypeFree(type);
        if (strcmp(ts, "Z") == 0) {
          fprintf(fp, " 0)");
          free(ts);
          break;
        }
        char * var = malloc(10 + strlen(ts) + 1);
        sprintf(var, "__default_%s", ts);
        fprintf(fp, " %s)", var);
        free(ts);
        free(var);
        break;
    }
    default: {
        ERROR("Not implemented in printPatternExpr()");
    }
    }
}

void printPatternExprList(struct PatternExprList * expr, FILE * fp, struct charMapping * type_mapping, struct environment * env) {
    for (struct PatternExprList * p = expr; p != NULL; p = p->next) {
        fprintf(fp, " ");
        printPatternExpr(p->expr, fp, type_mapping, env);
    }
}

void printPatternPolyType(struct PatternPolyType * type, FILE * fp) {
    if (type == NULL) return;
    switch (type->ty) {
    case PATTERN_POLY_VAR: {
        fprintf(fp, "%s", type->data.var);
        break;
    }
    case PATTERN_POLY_APP: {
        if (type->data.app->args == NULL) {
            fprintf(fp, "%s", type->data.app->func);
        }
        else fprintf(fp, "(@%s", type->data.app->func);
        printPatternPolyTypeList(type->data.app->args, fp);
        fprintf(fp, ")");
        break;
    }
    case PATTERN_POLY_ARROW: {
        fprintf(fp, "(");
        printPatternPolyType(type->data.arrow->left, fp);
        fprintf(fp, " -> ");
        printPatternPolyType(type->data.arrow->right, fp);
        fprintf(fp, ")");
        break;
    }
    case PATTERN_POLY_CONST: {
        fprintf(fp, "%s", type->data.var);
        break;
    }
    default: {
        ERROR("Not implemented in printPatternPolyType()");
    }
    }
}

void printPatternPolyTypeList(struct PatternPolyTypeList * tl, FILE * fp) {
    for (struct PatternPolyTypeList * p = tl; p != NULL; p = p->next) {
        fprintf(fp, " ");
        printPatternPolyType(p->head, fp);
    }
}

void printPatternCType(struct PatternCType * type, FILE * fp) {
    if (type == NULL) return;
    switch (type->ty) {
    case PATTERN_CTYPE_C8: {
        switch (type->data.ti->s) {
        case Signed: { fprintf(fp, "FET_char"); break; }
        case Unsigned: { fprintf(fp, "FET_uchar"); break; }
        }
        break;
    }
    case PATTERN_CTYPE_C16: {
        switch (type->data.ti->s) {
        case Signed: { fprintf(fp, "FET_short"); break; }
        case Unsigned: { fprintf(fp, "FET_ushort"); break; }
        }
        break;
    }
    case PATTERN_CTYPE_C32: {
        switch (type->data.ti->s) {
        case Signed: { fprintf(fp, "FET_int"); break; }
        case Unsigned: { fprintf(fp, "FET_uint"); break; }
        }
        break;
    }
    case PATTERN_CTYPE_C64: {
        switch (type->data.ti->s) {
        case Signed: { fprintf(fp, "FET_int64"); break; }
        case Unsigned: { fprintf(fp, "FET_uint64"); break; }
        }
        break;
    }
    case PATTERN_CTYPE_VAR: {
        fprintf(fp, "%s", type->data.var);
        break;
    }
    case PATTERN_CTYPE_STRUCT : {
        fprintf(fp, "(FET_alias (\"%s\"))", type->data.tstruct->struct_name);
        break;
    }
    case PATTERN_CTYPE_UNION : {
        fprintf(fp, "(FET_alias (\"%s\"))", type->data.tunion->union_name);
        break;
    }
    case PATTERN_CTYPE_ENUM : {
        fprintf(fp, "(FET_alias (\"%s\"))", type->data.tenum->enum_name);
        break;
    }
    default: { fprintf(fp, "FET_ptr"); break; }
    }

}

void printPatternProp(struct PatternProp * prop, FILE * fp, struct charMapping * type_mapping, struct environment * env) {
    if (prop == NULL) return;
    switch (prop->ty) {
    case PATTERN_PROP_TRUE: {
        fprintf(fp, "True");
        break;
    }
    case PATTERN_PROP_FALSE: {
        fprintf(fp, "False");
        break;
    }
    case PATTERN_PROP_UNOP: {
        switch (prop->data.unop->op) {
        case PROP_NOT: {
            fprintf(fp, "~");
            break;
        }
        default: {
            ERROR("Unknown unary operator in printPatternProp()");
        }
        }
        printPatternProp(prop->data.unop->prop, fp, type_mapping, env);
        break;
    }
    case PATTERN_PROP_BINOP: {
        fprintf(fp, "(");
        printPatternProp(prop->data.binop->left, fp, type_mapping, env);
        switch (prop->data.binop->op) {
        case PROP_AND: {
            fprintf(fp, " /\\ ");
            break;
        }
        case PROP_OR: {
            fprintf(fp, " \\/ ");
            break;
        }
        case PROP_IMPLY: {
            fprintf(fp, " -> ");
            break;
        }
        case PROP_IFF: {
            fprintf(fp, " <-> ");
            break;
        }
        default: {
            ERROR("Unknown binary operator in printPatternProp()");
        }
        }
        printPatternProp(prop->data.binop->right, fp, type_mapping, env);
        fprintf(fp, ")");
        break;
    }
    case PATTERN_PROP_COMPARE: {
        switch (prop->data.comp->op) {
        case PROP_LE: {
            fprintf(fp, "(Z.le ");
            break;
        }
        case PROP_LT: {
            fprintf(fp, "(Z.lt ");
            break;
        }
        case PROP_GE: {
            fprintf(fp, "(Z.ge ");
            break;
        }
        case PROP_GT: {
            fprintf(fp, "(Z.gt ");
            break;
        }
        case PROP_EQ: {
            fprintf(fp, "(");
            break;
        }
        case PROP_NEQ: {
            fprintf(fp, "(");
            break;
        }
        default: {
            ERROR("Unknown comparison operator in printPatternProp()");
        }
        }
        printPatternExpr(prop->data.comp->left, fp, type_mapping, env);
        fprintf(fp, " ");
        if (prop->data.comp->op == PROP_EQ) {
            fprintf(fp, "= ");
        } else if (prop->data.comp->op == PROP_NEQ) {
            fprintf(fp, "<> ");
        }
        printPatternExpr(prop->data.comp->right, fp, type_mapping, env);
        fprintf(fp, ")");
        break;
    }
    case PATTERN_PROP_PRED: {
        fprintf(fp, "(%s", prop->data.pred->name);
        // printPatternPolyTypeList(prop->data.pred->types, fp);
        printPatternExprList(prop->data.pred->args, fp, type_mapping, env);
        fprintf(fp, ")");
        break;
    }
    case PATTERN_PROP_PATPRED: {
        fprintf(fp, "(%s", prop->data.ppred->var);
        printPatternExprList(prop->data.ppred->args, fp, type_mapping, env);
        fprintf(fp, ")");
        break;
    }
    default: {
        ERROR("Not implemented in printPatternProp()");
    }
    }
}

void printPatternPropList(struct PatternPropList * pl, FILE * fp, int ty, struct charMapping * type_mapping, struct environment * env) {
    if (pl == NULL) {
        fprintf(fp, "TT");
        return;
    }
    if (pl->next) {
        printPatternPropList(pl->next, fp, ty, type_mapping, env);
        if (ty) fprintf(fp, " || "); else fprintf(fp, " && ");
    }
    fprintf(fp, "[| ");
    printPatternProp(pl->head, fp, type_mapping, env);
    fprintf(fp, " |]");
}

void printPatternPropLList(struct PatternPropLList * pl, FILE * fp, int num_tabs, struct charMapping * type_mapping, struct environment * env) {
    if (pl == NULL) {
        print_tabs(num_tabs, fp);
        fprintf(fp, "TT");
        return;
    }

    printPatternPropLList(pl->next, fp, num_tabs, type_mapping, env);
    fprintf(fp, " &&\n");
    print_tabs(num_tabs, fp);
    fprintf(fp, "(");
    printPatternPropList(pl->head, fp, pl->ty, type_mapping, env);
    fprintf(fp, ")");
}

void printPatternSep(struct PatternSep * sep, FILE * fp, struct charMapping * type_mapping, struct environment * env) {
    if (sep == NULL) return;
    switch (sep->ty) {
    case PATTERN_SEP_DATA_AT: {
        fprintf(fp, "(poly_store ");
        printPatternCType(sep->data.data_at->ty, fp);
        fprintf(fp, " ");
        printPatternExpr(sep->data.data_at->addr, fp, type_mapping, env);
        fprintf(fp, " ");
        printPatternExpr(sep->data.data_at->data, fp, type_mapping, env);
        fprintf(fp, ")");
        break;
    }
    case PATTERN_SEP_UNDEF: {
        fprintf(fp, "(poly_undef_store ");
        printPatternCType(sep->data.undef_data_at->ty, fp);
        fprintf(fp, " ");
        printPatternExpr(sep->data.undef_data_at->addr, fp, type_mapping, env);
        fprintf(fp, ")");
        break;
    }
    case PATTERN_SEP_PRED: {
        fprintf(fp, "(%s", sep->data.pred->name);
        // printPatternPolyTypeList(sep->data.pred->types, fp);
        printPatternExprList(sep->data.pred->args, fp, type_mapping, env);
        fprintf(fp, ")");
        break;
    }
    case PATTERN_SEP_PATPRED: {
        fprintf(fp, "(%s", sep->data.ppred->var);
        printPatternExprList(sep->data.ppred->args, fp, type_mapping, env);
        fprintf(fp, ")");
        break;
    }
    default: {
        ERROR("Not implemented in printPatternSep()");
    }
    }
}

void printPatternSepList(struct PatternSepList * sl, FILE * fp, int ty, struct charMapping * type_mapping, struct environment * env) {
    if (sl == NULL) {
        fprintf(fp, "emp");
        return;
    }
    if (sl->next) {
        printPatternSepList(sl->next, fp, ty, type_mapping, env);
        if (ty) fprintf(fp, " || "); else fprintf(fp, " && ");
    }
    printPatternSep(sl->head, fp, type_mapping, env);
}

void printPatternSepLList(struct PatternSepLList * sl, FILE * fp, int num_tabs, struct charMapping * type_mapping, struct environment * env) {
    if (sl == NULL) {
        print_tabs(num_tabs, fp);
        fprintf(fp, "emp");
        return;
    }
    printPatternSepLList(sl->next, fp, num_tabs, type_mapping, env);
    fprintf(fp, " **\n");
    print_tabs(num_tabs, fp);
    fprintf(fp, "(");
    printPatternSepList(sl->head, fp, sl->ty, type_mapping, env);
    fprintf(fp, ")");
}