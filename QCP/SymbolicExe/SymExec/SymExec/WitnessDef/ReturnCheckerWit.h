#include "../../Utility/List.h"
#include "../../AsrtDef/AssDef.h"
#include "../../Utility/List.h"

struct ReturnCheckWit {
   struct IntList * auto_solved;
   struct FuncRetType * pre, * post;
   struct StringList * strategy_scopes;
   struct ReturnCheckWit * next;
};

struct ReturnCheckWit * ReturnCheckWitNil();
struct ReturnCheckWit * ReturnCheckWitCons(struct FuncRetType * pre, 
                                           struct FuncRetType *post, 
                                           struct StringList * strategy_scopes,
                                           struct ReturnCheckWit * next);
struct ReturnCheckWit * ReturnCheckWitLink(struct ReturnCheckWit * list1, struct ReturnCheckWit * list2);
void ReturnCheckWitFree(struct ReturnCheckWit * return_checker_wit);