#include <assert.h>
#include "PatternSep.h"

struct PatternSep * initPatternSepDataAt(struct PatternExpr * addr, struct PatternCType * ty, struct PatternExpr * data) {
    struct PatternSep * ret = (struct PatternSep *)malloc(sizeof(struct PatternSep));
    ret->ty = PATTERN_SEP_DATA_AT;
    ret->data.data_at = malloc(sizeof(struct PatternSepDataAt));
    ret->data.data_at->addr = addr;
    ret->data.data_at->ty = ty;
    ret->data.data_at->data = data;
    return ret;
}

struct PatternSep * initPatternSepUndefDataAt(struct PatternExpr * addr, struct PatternCType * ty) {
    struct PatternSep * ret = (struct PatternSep *)malloc(sizeof(struct PatternSep));
    ret->ty = PATTERN_SEP_UNDEF;
    ret->data.undef_data_at = malloc(sizeof(struct PatternSepUndefDataAt));
    ret->data.undef_data_at->addr = addr;
    ret->data.undef_data_at->ty = ty;
    return ret;
}

struct PatternSep * initPatternSepArr(struct PatternExpr * addr, struct PatternCType * ty, struct PatternExpr * val, struct PatternExpr * size) {
    struct PatternSep * ret = (struct PatternSep *)malloc(sizeof(struct PatternSep));
    ret->ty = PATTERN_SEP_ARR;
    ret->data.arr = malloc(sizeof(struct PatternSepArr));
    ret->data.arr->addr = addr;
    ret->data.arr->ty = ty;
    ret->data.arr->val = val;
    ret->data.arr->size = size;
    return ret;
}

struct PatternSep * initPatternSepPred(char * name, struct PatternPolyTypeList * types, struct PatternExprList * args) {
    struct PatternSep * ret = (struct PatternSep *)malloc(sizeof(struct PatternSep));
    ret->ty = PATTERN_SEP_PRED;
    ret->data.pred = malloc(sizeof(struct PatternSepPred));
    ret->data.pred->name = name;
    ret->data.pred->types = types;
    ret->data.pred->args = args;
    ret->data.pred->id = -1;
    return ret;
}

struct PatternSep * initPatternSepPatPred(char * var, struct PatternExprList * args) {
    struct PatternSep * ret = (struct PatternSep *)malloc(sizeof(struct PatternSep));
    ret->ty = PATTERN_SEP_PATPRED;
    ret->data.ppred = malloc(sizeof(struct PatternSepPatPred));
    ret->data.ppred->var = var;
    ret->data.ppred->args = args;
    return ret;
}

void finiPatternSep(struct PatternSep * sep) {
    if (sep == NULL) return;
    switch (sep->ty) {
        case PATTERN_SEP_DATA_AT: {
            finiPatternExpr(sep->data.data_at->addr);
            PatternCTypeFree(sep->data.data_at->ty);
            finiPatternExpr(sep->data.data_at->data);
            free(sep->data.data_at);
            break;
        }
        case PATTERN_SEP_UNDEF: {
            finiPatternExpr(sep->data.undef_data_at->addr);
            PatternCTypeFree(sep->data.undef_data_at->ty);
            free(sep->data.undef_data_at);
            break;
        }
        case PATTERN_SEP_ARR: {
            finiPatternExpr(sep->data.arr->addr);
            PatternCTypeFree(sep->data.arr->ty);
            finiPatternExpr(sep->data.arr->val);
            finiPatternExpr(sep->data.arr->size);
            free(sep->data.arr);
            break;
        }
        case PATTERN_SEP_PRED: {
            free(sep->data.pred->name);
            PatternPolyTypeListFree(sep->data.pred->types);
            finiPatternExprList(sep->data.pred->args);
            free(sep->data.pred);
            break;
        }
        case PATTERN_SEP_PATPRED: {
            free(sep->data.ppred->var);
            finiPatternExprList(sep->data.ppred->args);
            free(sep->data.ppred);
            break;
        }
    }
    free(sep);
}

void finiPatternSepList(struct PatternSepList * sl) {
    if (sl == NULL) return;
    finiPatternSep(sl->head);
    finiPatternSepList(sl->next);
    free(sl);
}

struct PatternSepList * initPatternSepList(struct PatternSep * head, struct PatternSepList * next) {
    struct PatternSepList * ret = (struct PatternSepList *)malloc(sizeof(struct PatternSepList));
    ret->head = head;
    ret->next = next;
    return ret;
}

struct PatternSep * PatternSepDeepCopy(struct PatternSep * sep) {
    if (sep == NULL) return NULL;
    struct PatternSep * ret = (struct PatternSep *)malloc(sizeof(struct PatternSep));
    ret->ty = sep->ty;
    switch (sep->ty) {
    case PATTERN_SEP_DATA_AT: {
        ret->data.data_at = malloc(sizeof(struct PatternSepDataAt));
        ret->data.data_at->addr = PatternExprDeepCopy(sep->data.data_at->addr);
        ret->data.data_at->ty = PatternCTypeDeepCopy(sep->data.data_at->ty);
        ret->data.data_at->data = PatternExprDeepCopy(sep->data.data_at->data);
        break;
    }
    case PATTERN_SEP_UNDEF: {
        ret->data.undef_data_at = malloc(sizeof(struct PatternSepUndefDataAt));
        ret->data.undef_data_at->addr = PatternExprDeepCopy(sep->data.undef_data_at->addr);
        ret->data.undef_data_at->ty = PatternCTypeDeepCopy(sep->data.undef_data_at->ty);
        break;
    }
    case PATTERN_SEP_PRED: {
        ret->data.pred = malloc(sizeof(struct PatternSepPred));
        ret->data.pred->name = strdup(sep->data.pred->name);
        ret->data.pred->types = PatternPolyTypeListDeepCopy(sep->data.pred->types);
        ret->data.pred->args = PatternExprListDeepCopy(sep->data.pred->args);
        ret->data.pred->id = sep->data.pred->id;
        break;
    }
    case PATTERN_SEP_ARR: {
        ret->data.arr = malloc(sizeof(struct PatternSepArr));
        ret->data.arr->addr = PatternExprDeepCopy(sep->data.arr->addr);
        ret->data.arr->ty = PatternCTypeDeepCopy(sep->data.arr->ty);
        ret->data.arr->val = PatternExprDeepCopy(sep->data.arr->val);
        ret->data.arr->size = PatternExprDeepCopy(sep->data.arr->size);
        break;
    }
    case PATTERN_SEP_PATPRED: {
        ret->data.ppred = malloc(sizeof(struct PatternSepPatPred));
        ret->data.ppred->var = strdup(sep->data.ppred->var);
        ret->data.ppred->args = PatternExprListDeepCopy(sep->data.ppred->args);
        break;
    }
    default: {
        ERROR("Not implemented in PatternSepDeepCopy()");
    }
    }
    return ret;
}

struct PatternSepList * PatternSepListDeepCopy(struct PatternSepList * sl) {
    if (sl == NULL) return NULL;
    struct PatternSepList * ret = (struct PatternSepList *)malloc(sizeof(struct PatternSepList));
    ret->head = PatternSepDeepCopy(sl->head);
    ret->next = PatternSepListDeepCopy(sl->next);
    return ret;
}

int PatternSepEqual(struct PatternSep * sep1, struct PatternSep * sep2) {
    if (sep1 == NULL && sep2 == NULL) return 1;
    if (sep1 == NULL || sep2 == NULL) return 0;
    if (sep1->ty != sep2->ty) return 0;
    switch (sep1->ty) {
    case PATTERN_SEP_DATA_AT:
        return PatternExprEqual(sep1->data.data_at->addr, sep2->data.data_at->addr) &&
               PatternCTypeEqual(sep1->data.data_at->ty, sep2->data.data_at->ty) &&
               PatternExprEqual(sep1->data.data_at->data, sep2->data.data_at->data);
    case PATTERN_SEP_UNDEF:
        return PatternExprEqual(sep1->data.undef_data_at->addr, sep2->data.undef_data_at->addr) &&
               PatternCTypeEqual(sep1->data.undef_data_at->ty, sep2->data.undef_data_at->ty);
    case PATTERN_SEP_ARR:
        return PatternExprEqual(sep1->data.arr->addr, sep2->data.arr->addr) &&
               PatternCTypeEqual(sep1->data.arr->ty, sep2->data.arr->ty) &&
               PatternExprEqual(sep1->data.arr->val, sep2->data.arr->val) &&
               PatternExprEqual(sep1->data.arr->size, sep2->data.arr->size);
    case PATTERN_SEP_PRED:
        return !strcmp(sep1->data.pred->name, sep2->data.pred->name) &&
               PatternPolyTypeListEqual(sep1->data.pred->types, sep2->data.pred->types) &&
               PatternExprListEqual(sep1->data.pred->args, sep2->data.pred->args) &&
               sep1->data.pred->id == sep2->data.pred->id;
    case PATTERN_SEP_PATPRED:
        return !strcmp(sep1->data.ppred->var, sep2->data.ppred->var) &&
               PatternExprListEqual(sep1->data.ppred->args, sep2->data.ppred->args);
    default:
        ERROR("Not implemented in PatternSepEqual()");
    }
    return 0;
}

int PatternSepListEqual(struct PatternSepList * sl1, struct PatternSepList * sl2) {
    if (sl1 == NULL && sl2 == NULL) return 1;
    if (sl1 == NULL || sl2 == NULL) return 0;
    return PatternSepEqual(sl1->head, sl2->head) && PatternSepListEqual(sl1->next, sl2->next);
}

int PatternSepListFind(struct PatternSepList * sl, struct PatternSep * sep) {
    struct PatternSepList * p = sl;
    while (p) {
        if (PatternSepEqual(p->head, sep)) return 1;
        p = p->next;
    }
    return 0;

}

struct PatternSepList * PatternSepListErase(struct PatternSepList * sl, struct PatternSep * sep) {
    struct PatternSepList * p = sl;
    struct PatternSepList * prev = NULL;
    while (p) {
        if (PatternSepEqual(p->head, sep)) {
            if (prev == NULL) {
                struct PatternSepList * next = p->next;
                finiPatternSep(p->head);
                free(p);
                return next;
            } else {
                prev->next = p->next;
                finiPatternSep(p->head);
                free(p);
                return sl;
            }
        }
        prev = p;
        p = p->next;
    }
    return sl;
}

struct PatternSepLList * initPatternSepLList(int ty, struct PatternSepList * head, struct PatternSepLList * next) {
    struct PatternSepLList * ret = (struct PatternSepLList *)malloc(sizeof(struct PatternSepLList));
    ret->ty = ty;
    ret->head = head;
    ret->next = next;
    return ret;
}

void finiPatternSepLList(struct PatternSepLList * sll) {
    if (sll == NULL) return;
    finiPatternSepList(sll->head);
    finiPatternSepLList(sll->next);
    free(sll);
}

struct PatternSepLList * PatternSepLListDeepCopy(struct PatternSepLList * sll) {
    if (sll == NULL) return NULL;
    struct PatternSepLList * ret = (struct PatternSepLList *)malloc(sizeof(struct PatternSepLList));
    ret->ty = sll->ty;
    ret->head = PatternSepListDeepCopy(sll->head);
    ret->next = PatternSepLListDeepCopy(sll->next);
    return ret;
}

int PatternSepLListEqual(struct PatternSepLList * sll1, struct PatternSepLList * sll2) {
    if (sll1 == NULL && sll2 == NULL) return 1;
    if (sll1 == NULL || sll2 == NULL) return 0;
    return sll1->ty == sll2->ty && PatternSepListEqual(sll1->head, sll2->head) && PatternSepLListEqual(sll1->next, sll2->next);
}

int PatternSepLListFind(struct PatternSepLList * sll, struct PatternSepList * sl) {
    struct PatternSepLList * p = sll;
    while (p) {
        if (PatternSepListEqual(p->head, sl)) return 1;
        p = p->next;
    }
    return 0;
}

struct PatternSepLList * PatternSepLListErase(struct PatternSepLList * sll, struct PatternSepList * sl) {
    struct PatternSepLList * p = sll;
    struct PatternSepLList * prev = NULL;
    while (p) {
        if (PatternSepListEqual(p->head, sl)) {
            if (prev == NULL) {
                struct PatternSepLList * next = p->next;
                finiPatternSepList(p->head);
                free(p);
                return next;
            } else {
                prev->next = p->next;
                finiPatternSepList(p->head);
                free(p);
                return sll;
            }
        }
        prev = p;
        p = p->next;
    }
    return sll;
}