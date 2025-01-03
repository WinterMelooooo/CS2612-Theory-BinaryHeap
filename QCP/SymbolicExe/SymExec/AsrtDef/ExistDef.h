#ifndef EXISTDEF_INCLUDED
#define EXISTDEF_INCLUDED

#include <stdio.h>
#include <stdlib.h>
#include "ExprValDef.h"

struct ExistList {
   int id;
   struct ExistList * next;
};

struct ExistList * ExistListNil();

struct ExistList * ExistListCons(int id, struct ExistList *list);

struct ExistList * ExistListReverse(struct ExistList * list);

struct ExistList * ExistListLink(struct ExistList *left, struct ExistList *right);

struct ExistList * ExistListRemove(int id, struct ExistList * list);

struct ExistList *ExistListSort(struct ExistList * list);

struct ExistList * ExistListUnique(struct ExistList * list);

struct ExistList * ExistListDeepCopy(struct ExistList * exist_list);

struct ExistList * ExistListSubst(struct ExistList * exist_list, struct ExprVal * pre, struct ExprVal * post);

struct ExistList * ExistListSubstPolyType(struct ExistList * exist_list, struct PolyType * pre, struct PolyType * post, struct persistent_env * env);

int ExistListContains(int id, struct ExistList * exist_list);

void ExistListFree(struct ExistList * exist_list);

#endif
