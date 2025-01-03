#include "ReturnCheckerWit.h"

struct ReturnCheckWit * ReturnCheckWitNil() {
   return NULL;
}

struct ReturnCheckWit * ReturnCheckWitCons(struct FuncRetType * pre, 
                                           struct FuncRetType *post, 
                                           struct StringList * strategy_scopes,
                                           struct ReturnCheckWit * next) {
   struct ReturnCheckWit * ret;
   ret = (struct ReturnCheckWit *) malloc(sizeof(struct ReturnCheckWit));
   ret->pre = pre;
   ret->post = post;
   ret->next = next;
   ret->strategy_scopes = strategy_scopes;
   ret->auto_solved = NULL;
   return ret;
}

struct ReturnCheckWit * ReturnCheckWitLink(struct ReturnCheckWit * list1, struct ReturnCheckWit * list2) {
   if (list1 == NULL) return list2;
   if (list2 == NULL) return list1;
   struct ReturnCheckWit * tmp = list1;
   while (tmp->next != NULL) {
      tmp = tmp->next;
   }
   tmp->next = list2;
   return list1;
}

void ReturnCheckWitFree(struct ReturnCheckWit * return_checker_wit) {
   if (return_checker_wit == NULL) return;
   FuncRetTypeFree(return_checker_wit->pre);
   FuncRetTypeFree(return_checker_wit->post);
   ReturnCheckWitFree(return_checker_wit->next);
   free(return_checker_wit);
}