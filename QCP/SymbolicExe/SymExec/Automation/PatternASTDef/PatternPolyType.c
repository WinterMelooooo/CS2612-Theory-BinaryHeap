#include "PatternPolyType.h"

struct PatternPolyType * initPatternPolyTypeConst(char * var) {
    struct PatternPolyType * res = (struct PatternPolyType *) malloc(sizeof(struct PatternPolyType));
    res->ty = PATTERN_POLY_CONST;
    res->data.var = var;
    return res;
}

struct PatternPolyType * initPatternPolyTypeVar(char * var) {
    struct PatternPolyType * res = (struct PatternPolyType *) malloc(sizeof(struct PatternPolyType));
    res->ty = PATTERN_POLY_VAR;
    res->data.var = var;
    return res;
}

struct PatternPolyType * initPatternPolyTypeApp(char * func, struct PatternPolyTypeList * args) {
    struct PatternPolyType * res = (struct PatternPolyType *) malloc(sizeof(struct PatternPolyType));
    res->ty = PATTERN_POLY_APP;
    res->data.app = (struct PatternPolyTypeApp *) malloc(sizeof(struct PatternPolyTypeApp));
    res->data.app->func = func;
    res->data.app->args = args;
    return res;
}

struct PatternPolyType * initPatternPolyTypeArrow(struct PatternPolyType * left, struct PatternPolyType * right) {
    struct PatternPolyType * res = (struct PatternPolyType *) malloc(sizeof(struct PatternPolyType));
    res->ty = PATTERN_POLY_ARROW;
    res->data.arrow = (struct PatternPolyTypeArrow *) malloc(sizeof(struct PatternPolyTypeArrow));
    res->data.arrow->left = left;
    res->data.arrow->right = right;
    return res;
}

struct PatternPolyType * initPatternPolyTypeUnk(char * var) {
    struct PatternPolyType * res = (struct PatternPolyType *) malloc(sizeof(struct PatternPolyType));
    res->ty = PATTERN_POLY_UNK;
    res->data.var = var;
    return res;
}

void PatternPolyTypeFree(struct PatternPolyType * t) {
    if (t == NULL) return;
    switch (t->ty) {
        case PATTERN_POLY_VAR:
        case PATTERN_POLY_CONST:
        case PATTERN_POLY_UNK: {
            free(t->data.var);
            break;
        }
        case PATTERN_POLY_APP: {
            free(t->data.app->func);
            PatternPolyTypeListFree(t->data.app->args);
            free(t->data.app);
            break;
        }
        case PATTERN_POLY_ARROW: {
            PatternPolyTypeFree(t->data.arrow->left);
            PatternPolyTypeFree(t->data.arrow->right);
            free(t->data.arrow);
            break;
        }
    }
    free(t);
}

struct PatternPolyTypeList * initPatternPolyTypeList(struct PatternPolyType * head, struct PatternPolyTypeList * next) {
    struct PatternPolyTypeList * res = (struct PatternPolyTypeList *) malloc(sizeof(struct PatternPolyTypeList));
    res->head = head;
    res->next = next;
    return res;
}

void PatternPolyTypeListFree(struct PatternPolyTypeList * l) {
    if (l == NULL) return;
    PatternPolyTypeFree(l->head);
    PatternPolyTypeListFree(l->next);
    free(l);
}

struct PatternPolyType * PatternPolyTypeDeepCopy(struct PatternPolyType * t) {
    if (t == NULL) return NULL;
    struct PatternPolyType * res = (struct PatternPolyType *) malloc(sizeof(struct PatternPolyType));
    res->ty = t->ty;
    switch (t->ty) {
    case PATTERN_POLY_VAR:
    case PATTERN_POLY_UNK:
    case PATTERN_POLY_CONST: {
        res->data.var = strdup(t->data.var);
        break;
    }
    case PATTERN_POLY_APP: {
        res->data.app = (struct PatternPolyTypeApp *) malloc(sizeof(struct PatternPolyTypeApp));
        res->data.app->func = strdup(t->data.app->func);
        res->data.app->args = PatternPolyTypeListDeepCopy(t->data.app->args);
        break;
    }
    case PATTERN_POLY_ARROW: {
        res->data.arrow = (struct PatternPolyTypeArrow *) malloc(sizeof(struct PatternPolyTypeArrow));
        res->data.arrow->left = PatternPolyTypeDeepCopy(t->data.arrow->left);
        res->data.arrow->right = PatternPolyTypeDeepCopy(t->data.arrow->right);
        break;
    }
    }
    return res;
}

struct PatternPolyTypeList * PatternPolyTypeListDeepCopy(struct PatternPolyTypeList * l) {
    if (l == NULL) return NULL;
    struct PatternPolyTypeList * res = (struct PatternPolyTypeList *) malloc(sizeof(struct PatternPolyTypeList));
    res->head = PatternPolyTypeDeepCopy(l->head);
    res->next = PatternPolyTypeListDeepCopy(l->next);
    return res;
}

int PatternPolyTypeEqual(struct PatternPolyType * t1, struct PatternPolyType * t2) {
    if (t1 == NULL && t2 == NULL) return 1;
    if (t1 == NULL || t2 == NULL) return 0;
    if (t1->ty != t2->ty) return 0;
    switch (t1->ty) {
    case PATTERN_POLY_VAR:
    case PATTERN_POLY_UNK:
    case PATTERN_POLY_CONST: {
        return !strcmp(t1->data.var, t2->data.var);
    }
    case PATTERN_POLY_APP: {
        if (strcmp(t1->data.app->func, t2->data.app->func)) return 0;
        return PatternPolyTypeListEqual(t1->data.app->args, t2->data.app->args);
    }
    case PATTERN_POLY_ARROW: {
        return PatternPolyTypeEqual(t1->data.arrow->left, t2->data.arrow->left) && PatternPolyTypeEqual(t1->data.arrow->right, t2->data.arrow->right);
    }
    }
    return 0;
}

int PatternPolyTypeListEqual(struct PatternPolyTypeList * l1, struct PatternPolyTypeList * l2) {
    if (l1 == NULL && l2 == NULL) return 1;
    if (l1 == NULL || l2 == NULL) return 0;
    return PatternPolyTypeEqual(l1->head, l2->head) && PatternPolyTypeListEqual(l1->next, l2->next);
}

void PatternPolyTypePrint(FILE * fp, struct PatternPolyType * t) {
    if (t == NULL) return;
    switch (t->ty) {
    case PATTERN_POLY_CONST: {
        fprintf(fp, "<%s>", t->data.var);
        break;
    }
    case PATTERN_POLY_VAR: {
        fprintf(fp, "%s", t->data.var);
        break;
    }
    case PATTERN_POLY_UNK: {
        fprintf(fp, "?%s", t->data.var);
        break;
    }
    case PATTERN_POLY_APP: {
        fprintf(fp, "(%s ", t->data.app->func);
        for (struct PatternPolyTypeList * lcur = t->data.app->args; lcur != NULL; lcur = lcur->next) {
            PatternPolyTypePrint(fp, lcur->head);
            if (lcur->next != NULL) fprintf(fp, " ");
        }
        fprintf(fp, ")");
        break;
    }
    case PATTERN_POLY_ARROW: {
        fprintf(fp, "(");
        PatternPolyTypePrint(fp, t->data.arrow->left);
        fprintf(fp, " -> ");
        PatternPolyTypePrint(fp, t->data.arrow->right);
        fprintf(fp, ")");
        break;
    }
    }
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

char * PatternPolyTypeToChar(struct PatternPolyType * t) {
    if (t == NULL) return NULL;
    switch (t->ty) {
    case PATTERN_POLY_VAR:
    case PATTERN_POLY_CONST: {
        return strdup(t->data.var);
    }
    case PATTERN_POLY_UNK: {
        fprintf(stderr, "Unknown type ?%s should not appear in PatternPolyTypeToChar\n", t->data.var);
        ERROR("");
        return NULL;
    }
    case PATTERN_POLY_APP: {
        int cnt = 0;
        for (struct PatternPolyTypeList * cur = t->data.app->args; cur != NULL; cur = cur->next) {
            cnt++;
        }
        char * ret = malloc(3 + get_len(cnt) + 1);
        sprintf(ret, "app%d", cnt);
        for (struct PatternPolyTypeList * cur = t->data.app->args; cur != NULL; cur = cur->next) {
            char * tmp = PatternPolyTypeToChar(cur->head);
            char * new_ret = malloc(strlen(ret) + strlen(tmp) + 2);
            sprintf(new_ret, "%s_%s", ret, tmp);
            free(ret);
            free(tmp);
            ret = new_ret;
        }
        return ret;
    }
    case PATTERN_POLY_ARROW: {
        char * left = PatternPolyTypeToChar(t->data.arrow->left);
        char * right = PatternPolyTypeToChar(t->data.arrow->right);
        char * ret = malloc(strlen(left) + strlen(right) + 8);
        sprintf(ret, "arrow_%s_%s", left, right);
        free(left);
        free(right);
        return ret;
    }
    }
}

void PatternPolyTypeListPrint(struct PatternPolyTypeList * l) {
    printf("PatternPolyTypeList(");
    struct PatternPolyTypeList * cur = l;
    while (cur != NULL) {
        PatternPolyTypePrint(stdout, cur->head);
        cur = cur->next;
        if (cur != NULL) {
            printf(",");
        }
    }
    printf(")");
}