#include "PatternProp.h"

struct PatternProp * initPatternPropTrue() {
    struct PatternProp * ret = (struct PatternProp *)malloc(sizeof(struct PatternProp));
    ret->ty = PATTERN_PROP_TRUE;
    return ret;
}

struct PatternProp * initPatternPropFalse() {
    struct PatternProp * ret = (struct PatternProp *)malloc(sizeof(struct PatternProp));
    ret->ty = PATTERN_PROP_FALSE;
    return ret;
}

struct PatternProp * initPatternPropUnop(enum PropUOP op, struct PatternProp * prop) {
    struct PatternProp * ret = (struct PatternProp *)malloc(sizeof(struct PatternProp));
    ret->ty = PATTERN_PROP_UNOP;
    ret->data.unop = malloc(sizeof(struct PatternPropUnop));
    ret->data.unop->op = op;
    ret->data.unop->prop = prop;
    return ret;
}

struct PatternProp * initPatternPropBinop(enum PropBinOP op, struct PatternProp * left, struct PatternProp * right) {
    struct PatternProp * ret = (struct PatternProp *)malloc(sizeof(struct PatternProp));
    ret->ty = PATTERN_PROP_BINOP;
    ret->data.binop = malloc(sizeof(struct PatternPropBinop));
    ret->data.binop->op = op;
    ret->data.binop->left = left;
    ret->data.binop->right = right;
    return ret;
}

struct PatternProp * initPatternPropPtr(enum PropPtrOP op, struct PatternExpr * expr) {
    struct PatternProp * ret = (struct PatternProp *)malloc(sizeof(struct PatternProp));
    ret->ty = PATTERN_PROP_PTR;
    ret->data.ptr = malloc(sizeof(struct PatternPropPtr));
    ret->data.ptr->op = op;
    ret->data.ptr->expr = expr;
    return ret;
}

struct PatternProp * initPatternPropComp(enum PropCompOp op, struct PatternExpr * left, struct PatternExpr * right) {
    struct PatternProp * ret = (struct PatternProp *)malloc(sizeof(struct PatternProp));
    ret->ty = PATTERN_PROP_COMPARE;
    ret->data.comp = malloc(sizeof(struct PatternPropCompare));
    ret->data.comp->op = op;
    ret->data.comp->left = left;
    ret->data.comp->right = right;
    return ret;
}

struct PatternProp * initPatternPropPred(char * name, struct PatternPolyTypeList * types, struct PatternExprList * args) {
    struct PatternProp * ret = (struct PatternProp *)malloc(sizeof(struct PatternProp));
    ret->ty = PATTERN_PROP_PRED;
    ret->data.pred = malloc(sizeof(struct PatternPropPred));
    ret->data.pred->name = name;
    ret->data.pred->types = types;
    ret->data.pred->args = args;
    ret->data.pred->id = -1;
    return ret;
}

struct PatternProp * initPatternPropPatPred(char * var, struct PatternExprList * args) {
    struct PatternProp * ret = (struct PatternProp *)malloc(sizeof(struct PatternProp));
    ret->ty = PATTERN_PROP_PATPRED;
    ret->data.ppred = malloc(sizeof(struct PatternPropPatPred));
    ret->data.ppred->var = var;
    ret->data.ppred->args = args;
    return ret;
}

void finiPatternProp(struct PatternProp * prop) {
    switch (prop->ty) {
        case PATTERN_PROP_TRUE:
        case PATTERN_PROP_FALSE:
            break;
        case PATTERN_PROP_UNOP: {
            finiPatternProp(prop->data.unop->prop);
            free(prop->data.unop);
            break;
        }
        case PATTERN_PROP_BINOP: {
            finiPatternProp(prop->data.binop->left);
            finiPatternProp(prop->data.binop->right);
            free(prop->data.binop);
            break;
        }
        case PATTERN_PROP_PTR: {
            finiPatternExpr(prop->data.ptr->expr);
            free(prop->data.ptr);
            break;
        }
        case PATTERN_PROP_COMPARE: {
            finiPatternExpr(prop->data.comp->left);
            finiPatternExpr(prop->data.comp->right);
            free(prop->data.comp);
            break;
        }
        case PATTERN_PROP_PRED: {
            PatternPolyTypeListFree(prop->data.pred->types);
            finiPatternExprList(prop->data.pred->args);
            free(prop->data.pred->name);
            free(prop->data.pred);
            break;
        }
        case PATTERN_PROP_PATPRED: {
            finiPatternExprList(prop->data.ppred->args);
            free(prop->data.ppred->var);
            free(prop->data.ppred);
            break;
        }
        default:
            ERROR("Unknown PatternProp type in finiPatternProp()");
    }
    free(prop);
}

struct PatternPropList * initPatternPropList(struct PatternProp * head, struct PatternPropList * next) {
    struct PatternPropList * ret = (struct PatternPropList *)malloc(sizeof(struct PatternPropList));
    ret->head = head;
    ret->next = next;
    return ret;
}

void finiPatternPropList(struct PatternPropList * list) {
    if (list == NULL) return;
    finiPatternProp(list->head);
    finiPatternPropList(list->next);
    free(list);
}

struct PatternProp * PatternPropDeepCopy(struct PatternProp * prop) {
    if (prop == NULL) return NULL;
    struct PatternProp * ret = (struct PatternProp *) malloc(sizeof(struct PatternProp));
    ret->ty = prop->ty;
    switch (prop->ty) {
        case PATTERN_PROP_TRUE:
        case PATTERN_PROP_FALSE:
            break;
        case PATTERN_PROP_UNOP: {
            ret->data.unop = malloc(sizeof(struct PatternPropUnop));
            ret->data.unop->op = prop->data.unop->op;
            ret->data.unop->prop = PatternPropDeepCopy(prop->data.unop->prop);
            break;
        }
        case PATTERN_PROP_BINOP: {
            ret->data.binop = malloc(sizeof(struct PatternPropBinop));
            ret->data.binop->op = prop->data.binop->op;
            ret->data.binop->left = PatternPropDeepCopy(prop->data.binop->left);
            ret->data.binop->right = PatternPropDeepCopy(prop->data.binop->right);
            break;
        }
        case PATTERN_PROP_PTR: {
            ret->data.ptr = malloc(sizeof(struct PatternPropPtr));
            ret->data.ptr->op = prop->data.ptr->op;
            ret->data.ptr->expr = PatternExprDeepCopy(prop->data.ptr->expr);
            break;
        }
        case PATTERN_PROP_COMPARE: {
            ret->data.comp = malloc(sizeof(struct PatternPropCompare));
            ret->data.comp->op = prop->data.comp->op;
            ret->data.comp->left = PatternExprDeepCopy(prop->data.comp->left);
            ret->data.comp->right = PatternExprDeepCopy(prop->data.comp->right);
            break;
        }
        case PATTERN_PROP_PRED: {
            ret->data.pred = malloc(sizeof(struct PatternPropPred));
            ret->data.pred->name = strdup(prop->data.pred->name);
            ret->data.pred->types = PatternPolyTypeListDeepCopy(prop->data.pred->types);
            ret->data.pred->args = PatternExprListDeepCopy(prop->data.pred->args);
            ret->data.pred->id = prop->data.pred->id;
            break;
        }
        case PATTERN_PROP_PATPRED: {
            ret->data.ppred = malloc(sizeof(struct PatternPropPatPred));
            ret->data.ppred->var = strdup(prop->data.ppred->var);
            ret->data.ppred->args = PatternExprListDeepCopy(prop->data.ppred->args);
            break;
        }
        default:
            ERROR("Unknown PatternProp type in PatternPropDeepCopy()");
    }
    return ret;
}

struct PatternPropList * PatternPropListDeepCopy(struct PatternPropList * list) {
    if (list == NULL) return NULL;
    struct PatternPropList * ret = (struct PatternPropList *) malloc(sizeof(struct PatternPropList));
    ret->head = PatternPropDeepCopy(list->head);
    ret->next = PatternPropListDeepCopy(list->next);
    return ret;
}

struct PatternPropList * PatternPropListApp(struct PatternPropList * l1, struct PatternPropList * l2) {
    if (l1 == NULL) return l2;
    struct PatternPropList * cur = l1;
    for (; cur->next != NULL; cur = cur->next);
    cur->next = l2;
    return l1;
}

int PatternPropEqual(struct PatternProp * p1, struct PatternProp * p2) {
    if (p1 == NULL && p2 == NULL) return 1;
    if (p1 == NULL || p2 == NULL) return 0;
    if (p1->ty != p2->ty) return 0;
    switch (p1->ty) {
        case PATTERN_PROP_TRUE:
        case PATTERN_PROP_FALSE: {
            return 1;
        }
        case PATTERN_PROP_UNOP: {
            return p1->data.unop->op == p2->data.unop->op && PatternPropEqual(p1->data.unop->prop, p2->data.unop->prop);
        }
        case PATTERN_PROP_BINOP: {
            return p1->data.binop->op == p2->data.binop->op && PatternPropEqual(p1->data.binop->left, p2->data.binop->left) && PatternPropEqual(p1->data.binop->right, p2->data.binop->right);
        }
        case PATTERN_PROP_PTR: {
            return p1->data.ptr->op == p2->data.ptr->op && PatternExprEqual(p1->data.ptr->expr, p2->data.ptr->expr);
        }
        case PATTERN_PROP_COMPARE: {
            return p1->data.comp->op == p2->data.comp->op && PatternExprEqual(p1->data.comp->left, p2->data.comp->left) && PatternExprEqual(p1->data.comp->right, p2->data.comp->right);
        }
        case PATTERN_PROP_PRED: {
            if (strcmp(p1->data.pred->name, p2->data.pred->name)) return 0;
            return PatternPolyTypeListEqual(p1->data.pred->types, p2->data.pred->types) && PatternExprListEqual(p1->data.pred->args, p2->data.pred->args) &&
                   p1->data.pred->id == p2->data.pred->id;
        }
        case PATTERN_PROP_PATPRED: {
            if (strcmp(p1->data.ppred->var, p2->data.ppred->var)) return 0;
            return PatternExprListEqual(p1->data.ppred->args, p2->data.ppred->args);
        }
        default:
            ERROR("Unknown PatternProp type in PatternPropEqual()");
    }
    return 0;
}

int PatternPropListEqual(struct PatternPropList * l1, struct PatternPropList * l2) {
    if (l1 == NULL && l2 == NULL) return 1;
    if (l1 == NULL || l2 == NULL) return 0;
    return PatternPropEqual(l1->head, l2->head) && PatternPropListEqual(l1->next, l2->next);
}

int PatternPropListFind(struct PatternPropList * list, struct PatternProp * prop) {
    struct PatternPropList * p = list;
    while (p) {
        if (PatternPropEqual(p->head, prop)) return 1;
        p = p->next;
    }
    return 0;
}

struct PatternPropList * PatternPropListErase(struct PatternPropList * list, struct PatternProp * prop) {
    struct PatternPropList * p = list;
    struct PatternPropList * prev = NULL;
    while (p) {
        if (PatternPropEqual(p->head, prop)) {
            if (prev == NULL) {
                struct PatternPropList * next = p->next;
                finiPatternProp(p->head);
                free(p);
                return next;
            } else {
                struct PatternPropList * next = p->next;
                finiPatternProp(p->head);
                free(p);
                prev->next = next;
                return list;
            }
        }
        prev = p;
        p = p->next;
    }
    return list;
}

struct PatternPropLList * initPatternPropLList(int ty, struct PatternPropList * head, struct PatternPropLList * next) {
    struct PatternPropLList * ret = (struct PatternPropLList *)malloc(sizeof(struct PatternPropLList));
    ret->ty = ty;
    ret->head = head;
    ret->next = next;
    return ret;
}

void finiPatternPropLList(struct PatternPropLList * list) {
    if (list == NULL) return;
    finiPatternPropList(list->head);
    finiPatternPropLList(list->next);
    free(list);
}

struct PatternPropLList * PatternPropLListApp(struct PatternPropLList * l1, struct PatternPropLList * l2) {
    if (l1 == NULL) return l2;
    struct PatternPropLList * cur = l1;
    for (; cur->next != NULL; cur = cur->next);
    cur->next = l2;
    return l1;
}

struct PatternPropLList * PatternPropLListDeepCopy(struct PatternPropLList * list) {
    if (list == NULL) return NULL;
    struct PatternPropLList * ret = (struct PatternPropLList *) malloc(sizeof(struct PatternPropLList));
    ret->ty = list->ty;
    ret->head = PatternPropListDeepCopy(list->head);
    ret->next = PatternPropLListDeepCopy(list->next);
    return ret;
}

int PatternPropLListEqual(struct PatternPropLList * l1, struct PatternPropLList * l2) {
    if (l1 == NULL && l2 == NULL) return 1;
    if (l1 == NULL || l2 == NULL) return 0;
    return l1->ty == l2->ty && PatternPropListEqual(l1->head, l2->head) && PatternPropLListEqual(l1->next, l2->next);
}

int PatternPropLListFind(struct PatternPropLList * list, struct PatternPropList * prop) {
    struct PatternPropLList * p = list;
    while (p) {
        if (PatternPropListEqual(p->head, prop)) return 1;
        p = p->next;
    }
    return 0;
}

struct PatternPropLList * PatternPropLListErase(struct PatternPropLList * list, struct PatternPropList * prop) {
    struct PatternPropLList * p = list;
    struct PatternPropLList * prev = NULL;
    while (p) {
        if (PatternPropListEqual(p->head, prop)) {
            if (prev == NULL) {
                struct PatternPropLList * next = p->next;
                finiPatternPropList(p->head);
                free(p);
                return next;
            } else {
                struct PatternPropLList * next = p->next;
                finiPatternPropList(p->head);
                free(p);
                prev->next = next;
                return list;
            }
        }
        prev = p;
        p = p->next;
    }
    return list;
}