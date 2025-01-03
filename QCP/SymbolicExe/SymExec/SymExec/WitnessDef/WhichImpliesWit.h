#ifndef WHICH_IMPLIES_WIT_H
#define WHICH_IMPLIES_WIT_H

#include "../../AsrtDef/AssDef.h"
#include "../../Utility/List.h"

struct WhichImpliesWit {
   struct AsrtList * pre, * post;
   struct StringList * strategy_scopes;
   struct WhichImpliesWit * next;
   struct IntList * auto_solved;
};

struct WhichImpliesWit * WhichImpliesWitNil();
struct WhichImpliesWit * WhichImpliesWitCons(struct AsrtList * pre, 
                                             struct AsrtList * post, 
                                             struct StringList * strategy_scopes,
                                             struct WhichImpliesWit * next);
struct WhichImpliesWit * WhichImpliesWitLink(struct WhichImpliesWit * list1, struct WhichImpliesWit * list2);
void WhichImpliesWitFree(struct WhichImpliesWit * list);

#endif