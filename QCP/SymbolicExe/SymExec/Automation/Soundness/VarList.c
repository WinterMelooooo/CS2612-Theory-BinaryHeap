#include "VarList.h"

struct VarType * initVarType(char * var, struct PatternPolyType * type) {
    struct VarType * ret = malloc(sizeof(struct VarType));
    ret->name = var;
    ret->type = type;
    return ret;
}

void finiVarType(struct VarType * vt) {
    free(vt->name);
    PatternPolyTypeFree(vt->type);
    free(vt);
}

struct VarType * VarTypeDeepCopy(struct VarType * vt) {
    return initVarType(strdup(vt->name), PatternPolyTypeDeepCopy(vt->type));
}

struct VarList * initVarList(struct VarType * head, struct VarList * next) {
    struct VarList * vl = (struct VarList *)malloc(sizeof(struct VarList));
    vl->head = head;
    vl->next = next;
    return vl;
}

void finiVarList(struct VarList * vl) {
    if (vl == NULL) return;
    finiVarList(vl->next);
    finiVarType(vl->head);
    free(vl);
}

int VarListIn(struct VarType * vt, struct VarList * vl) {
    struct VarList * p = vl;
    while (p) {
        if (!strcmp(p->head->name, vt->name)) return 1;
        p = p->next;
    }
    return 0;
}

struct VarList * VarListInsert(struct VarType * vt, struct VarList * vl) {
    if (VarListIn(vt, vl)) return vl;
    return initVarList(VarTypeDeepCopy(vt), vl);
}

struct VarList * VarListMerge(struct VarList * vl1, struct VarList * vl2) {
    for (struct VarList * cur = vl2; cur != NULL; cur = cur->next) {
        vl1 = VarListInsert(cur->head, vl1);
    }
    finiVarList(vl2);
    return vl1;
}

struct VarList * VarListApp(struct VarList * vl1, struct VarList * vl2) {
    struct VarList * cur;
    if (vl1 == NULL) return vl2;
    for (cur = vl1; cur->next != NULL; cur = cur->next);
    cur->next = vl2;
    return vl1;
}

struct VarList * VarListMinus(struct VarList * vl1, struct VarList * vl2) {
    if (vl1 == NULL) return NULL;
    if (VarListIn(vl1->head, vl2)) return VarListMinus(vl1->next, vl2);
    else return initVarList(VarTypeDeepCopy(vl1->head), VarListMinus(vl1->next, vl2));
}

struct VarList * VarListDeepCopy(struct VarList * vl) {
    if (vl == NULL) return NULL;
    return initVarList(VarTypeDeepCopy(vl->head), VarListDeepCopy(vl->next));
}