#include <assert.h>
#include "PatternExpr.h"

struct PatternExpr *initPatternExprConst(unsigned long long num)
{
  struct PatternExpr *ret = (struct PatternExpr *)malloc(sizeof(struct PatternExpr));
  ret->ty = PATTERN_EXPR_CONST;
  ret->data.num = num;
  return ret;
}

struct PatternExpr * initPatternExprVar(char * var) {
    struct PatternExpr * ret = (struct PatternExpr *)malloc(sizeof(struct PatternExpr));
    ret->ty = PATTERN_EXPR_VAR;
    ret->data.var = var;
    return ret;
}

struct PatternExpr * initPatternExprEVar(char * var) {
    struct PatternExpr * ret = (struct PatternExpr *)malloc(sizeof(struct PatternExpr));
    ret->ty = PATTERN_EXPR_EVAR;
    ret->data.var = var;
    return ret;
}

struct PatternExpr * initPatternExprAtomVar(char * var) {
    struct PatternExpr * ret = (struct PatternExpr *)malloc(sizeof(struct PatternExpr));
    ret->ty = PATTERN_EXPR_SVAR;
    ret->data.var = var;
    return ret;
}

struct PatternExpr * initPatternExprGlobalVar(char * var) {
    struct PatternExpr * ret = (struct PatternExpr *)malloc(sizeof(struct PatternExpr));
    ret->ty = PATTERN_EXPR_GVAR;
    ret->data.var = var;
    return ret;
}

struct PatternExpr * initPatternExprField(struct PatternExpr * expr, char * struct_name, char * field_name) {
    struct PatternExpr * ret = (struct PatternExpr *)malloc(sizeof(struct PatternExpr));
    ret->ty = PATTERN_EXPR_FIELD;
    ret->data.field = malloc(sizeof(struct PatternExprField));
    ret->data.field->expr = expr;
    ret->data.field->struct_name = struct_name;
    ret->data.field->field_name = field_name;
    return ret;
}

struct PatternExpr * initPatternExprBinop(enum InnerBinaryOperation op, struct PatternExpr * left, struct PatternExpr * right) {
    struct PatternExpr * ret = (struct PatternExpr *)malloc(sizeof(struct PatternExpr));
    ret->ty = PATTERN_EXPR_BINOP;
    ret->data.binop = malloc(sizeof(struct PatternExprBinop));
    ret->data.binop->op = op;
    ret->data.binop->left = left;
    ret->data.binop->right = right;
    return ret;
}

struct PatternExpr * initPatternExprUnop(enum InnerUnaryOperation op, struct PatternExpr * expr) {
    struct PatternExpr * ret = (struct PatternExpr *)malloc(sizeof(struct PatternExpr));
    ret->ty = PATTERN_EXPR_UNOP;
    ret->data.unop = malloc(sizeof(struct PatternExprUnop));
    ret->data.unop->op = op;
    ret->data.unop->expr = expr;
    return ret;
}

struct PatternExpr * initPatternExprArridx(struct PatternExpr * array, struct PatternExpr * index) {
    struct PatternExpr * ret = (struct PatternExpr *)malloc(sizeof(struct PatternExpr));
    ret->ty = PATTERN_EXPR_ARRIDX;
    ret->data.arridx = malloc(sizeof(struct PatternExprArridx));
    ret->data.arridx->array = array;
    ret->data.arridx->index = index;
    return ret;
}

struct PatternExpr * initPatternExprApp(char * func, struct PatternPolyTypeList * type_list, struct PatternExprList * expr_list) {
    struct PatternExpr * ret = (struct PatternExpr *)malloc(sizeof(struct PatternExpr));
    ret->ty = PATTERN_EXPR_APP;
    ret->data.app = malloc(sizeof(struct PatternExprApp));
    ret->data.app->func = func;
    ret->data.app->type_list = type_list;
    ret->data.app->expr_list = expr_list;
    ret->data.app->id = -1;
    return ret;
}

struct PatternExpr * initPatternExprPatApp(char * var, struct PatternExprList * expr_list) {
    struct PatternExpr * ret = (struct PatternExpr *)malloc(sizeof(struct PatternExpr));
    ret->ty = PATTERN_EXPR_PATAPP;
    ret->data.papp = malloc(sizeof(struct PatternExprPatApp));
    ret->data.papp->var = var;
    ret->data.papp->expr_list = expr_list;
    return ret;
}

struct PatternExpr * initPatternExprSizeof(struct PatternCType * sizeof_expr) {
    struct PatternExpr * ret = (struct PatternExpr *)malloc(sizeof(struct PatternExpr));
    ret->ty = PATTERN_EXPR_SIZEOF;
    ret->data.sizeof_expr = sizeof_expr;
    return ret;
}

struct PatternExprList * initPatternExprList(struct PatternExpr * expr, struct PatternExprList * next) {
    struct PatternExprList * ret = (struct PatternExprList *)malloc(sizeof(struct PatternExprList));
    ret->expr = expr;
    ret->next = next;
    return ret;
}

void finiPatternExpr(struct PatternExpr * expr) {
    if (expr == NULL) return;
    switch (expr->ty) {
        case PATTERN_EXPR_CONST:
            break;
        case PATTERN_EXPR_VAR:
        case PATTERN_EXPR_EVAR:
        case PATTERN_EXPR_SVAR: 
        case PATTERN_EXPR_GVAR: {
            free(expr->data.var);
            break;
        }
        case PATTERN_EXPR_FIELD: {
            finiPatternExpr(expr->data.field->expr);
            free(expr->data.field->struct_name);
            free(expr->data.field->field_name);
            free(expr->data.field);
            break;
        }
        case PATTERN_EXPR_BINOP: {
            finiPatternExpr(expr->data.binop->left);
            finiPatternExpr(expr->data.binop->right);
            free(expr->data.binop);
            break;
        }
        case PATTERN_EXPR_UNOP: {
            finiPatternExpr(expr->data.unop->expr);
            free(expr->data.unop);
            break;
        }
        case PATTERN_EXPR_ARRIDX: {
            finiPatternExpr(expr->data.arridx->array);
            finiPatternExpr(expr->data.arridx->index);
            free(expr->data.arridx);
            break;
        }
        case PATTERN_EXPR_APP: {
            free(expr->data.app->func);
            PatternPolyTypeListFree(expr->data.app->type_list);
            finiPatternExprList(expr->data.app->expr_list);
            free(expr->data.app);
            break;
        }
        case PATTERN_EXPR_PATAPP: {
            free(expr->data.papp->var);
            finiPatternExprList(expr->data.papp->expr_list);
            free(expr->data.papp);
            break;
        }
        case PATTERN_EXPR_SIZEOF: {
            PatternCTypeFree(expr->data.sizeof_expr);
            break;
        }
        default: {
            ERROR("Unknown PatternExpr type in finiPatternExpr()");
        }
    }
    free(expr);
}

void finiPatternExprList(struct PatternExprList * head) {
    if (head == NULL) return;
    finiPatternExpr(head->expr);
    finiPatternExprList(head->next);
    free(head);
}

struct PatternExpr * PatternExprDeepCopy(struct PatternExpr * expr) {
    if (expr == NULL) return NULL;
    struct PatternExpr * ret = (struct PatternExpr *)malloc(sizeof(struct PatternExpr));
    ret->ty = expr->ty;
    switch (expr->ty) {
    case PATTERN_EXPR_CONST: {
        ret->data.num = expr->data.num;
        break;
    }
    case PATTERN_EXPR_VAR:
    case PATTERN_EXPR_EVAR:
    case PATTERN_EXPR_SVAR: 
    case PATTERN_EXPR_GVAR: {
        ret->data.var = strdup(expr->data.var);
        break;
    }
    case PATTERN_EXPR_FIELD: {
        ret->data.field = (struct PatternExprField *)malloc(sizeof(struct PatternExprField));
        ret->data.field->expr = PatternExprDeepCopy(expr->data.field->expr);
        ret->data.field->struct_name = strdup(expr->data.field->struct_name);
        ret->data.field->field_name = strdup(expr->data.field->field_name);
        break;
    }
    case PATTERN_EXPR_BINOP: {
        ret->data.binop = (struct PatternExprBinop *)malloc(sizeof(struct PatternExprBinop));
        ret->data.binop->op = expr->data.binop->op;
        ret->data.binop->left = PatternExprDeepCopy(expr->data.binop->left);
        ret->data.binop->right = PatternExprDeepCopy(expr->data.binop->right);
        break;
    }
    case PATTERN_EXPR_UNOP: {
        ret->data.unop = (struct PatternExprUnop *)malloc(sizeof(struct PatternExprUnop));
        ret->data.unop->op = expr->data.unop->op;
        ret->data.unop->expr = PatternExprDeepCopy(expr->data.unop->expr);
        break;
    }
    case PATTERN_EXPR_ARRIDX: {
        ret->data.arridx = (struct PatternExprArridx *)malloc(sizeof(struct PatternExprArridx));
        ret->data.arridx->array = PatternExprDeepCopy(expr->data.arridx->array);
        ret->data.arridx->index = PatternExprDeepCopy(expr->data.arridx->index);
        break;
    }
    case PATTERN_EXPR_APP: {
        ret->data.app = (struct PatternExprApp *)malloc(sizeof(struct PatternExprApp));
        ret->data.app->func = strdup(expr->data.app->func);
        ret->data.app->type_list = PatternPolyTypeListDeepCopy(expr->data.app->type_list);
        ret->data.app->expr_list = PatternExprListDeepCopy(expr->data.app->expr_list);
        ret->data.app->id = expr->data.app->id;
        break;
    }
    case PATTERN_EXPR_PATAPP: {
        ret->data.papp = (struct PatternExprPatApp *)malloc(sizeof(struct PatternExprPatApp));
        ret->data.papp->var = strdup(expr->data.papp->var);
        ret->data.papp->expr_list = PatternExprListDeepCopy(expr->data.papp->expr_list);
        break;
    }
    case PATTERN_EXPR_SIZEOF: {
        ret->data.sizeof_expr = PatternCTypeDeepCopy(expr->data.sizeof_expr);
        break;
    }
    }
    return ret;
}

struct PatternExprList * PatternExprListDeepCopy(struct PatternExprList * expr_list) {
    if (expr_list == NULL) return NULL;
    struct PatternExprList * ret = (struct PatternExprList *)malloc(sizeof(struct PatternExprList));
    ret->expr = PatternExprDeepCopy(expr_list->expr);
    ret->next = PatternExprListDeepCopy(expr_list->next);
    return ret;
}

int PatternExprEqual(struct PatternExpr * expr1, struct PatternExpr * expr2) {
    if (expr1 == NULL && expr2 == NULL) return 1;
    if (expr1 == NULL || expr2 == NULL) return 0;
    if (expr1->ty != expr2->ty) return 0;
    switch (expr1->ty) {
    case PATTERN_EXPR_CONST: {
        return expr1->data.num == expr2->data.num;
    }
    case PATTERN_EXPR_VAR:
    case PATTERN_EXPR_EVAR:
    case PATTERN_EXPR_SVAR: 
    case PATTERN_EXPR_GVAR: {
        return !strcmp(expr1->data.var, expr2->data.var);
    }
    case PATTERN_EXPR_FIELD: {
        return PatternExprEqual(expr1->data.field->expr, expr2->data.field->expr)
            && !strcmp(expr1->data.field->struct_name, expr2->data.field->struct_name)
            && !strcmp(expr1->data.field->field_name, expr2->data.field->field_name);
    }
    case PATTERN_EXPR_BINOP: {
        return expr1->data.binop->op == expr2->data.binop->op
            && PatternExprEqual(expr1->data.binop->left, expr2->data.binop->left)
            && PatternExprEqual(expr1->data.binop->right, expr2->data.binop->right);
    }
    case PATTERN_EXPR_UNOP: {
        return expr1->data.unop->op == expr2->data.unop->op
            && PatternExprEqual(expr1->data.unop->expr, expr2->data.unop->expr);
    }
    case PATTERN_EXPR_ARRIDX: {
        return PatternExprEqual(expr1->data.arridx->array, expr2->data.arridx->array)
            && PatternExprEqual(expr1->data.arridx->index, expr2->data.arridx->index);
    }
    case PATTERN_EXPR_APP: {
        if (strcmp(expr1->data.app->func, expr2->data.app->func)) return 0;
        return PatternPolyTypeListEqual(expr1->data.app->type_list, expr2->data.app->type_list)
            && PatternExprListEqual(expr1->data.app->expr_list, expr2->data.app->expr_list)
            && expr1->data.app->id == expr2->data.app->id;
    }
    case PATTERN_EXPR_PATAPP: {
        if (strcmp(expr1->data.papp->var, expr2->data.papp->var)) return 0;
        return PatternExprListEqual(expr1->data.papp->expr_list, expr2->data.papp->expr_list);
    }
    case PATTERN_EXPR_SIZEOF: {
        return PatternCTypeEqual(expr1->data.sizeof_expr, expr2->data.sizeof_expr);
    }
    default: {
        ERROR("Unknown PatternExpr type in PatternExprEqual()");
    }
    }
}

int PatternExprListEqual(struct PatternExprList * expr_list1, struct PatternExprList * expr_list2) {
    if (expr_list1 == NULL && expr_list2 == NULL) return 1;
    if (expr_list1 == NULL || expr_list2 == NULL) return 0;
    return PatternExprEqual(expr_list1->expr, expr_list2->expr)
        && PatternExprListEqual(expr_list1->next, expr_list2->next);
}