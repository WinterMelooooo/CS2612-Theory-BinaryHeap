#include "WhichImpliesWit.h"

struct WhichImpliesWit * WhichImpliesWitNil() {
   return NULL;   
}

struct WhichImpliesWit * WhichImpliesWitCons(struct AsrtList * pre, 
                                             struct AsrtList * post, 
                                             struct StringList * strategy_scopes,
                                             struct WhichImpliesWit * next) {
   struct WhichImpliesWit * ret = malloc(sizeof(struct WhichImpliesWit));
   ret->pre = pre;
   ret->post = post;
   ret->next = next;
   ret->strategy_scopes = strategy_scopes;
   ret->auto_solved = NULL;
   return ret;
}

struct WhichImpliesWit * WhichImpliesWitLink(struct WhichImpliesWit * list1, struct WhichImpliesWit * list2) {
   if (list1 == NULL) return list2;
   if (list2 == NULL) return list1;
   struct WhichImpliesWit * cur = list1;
   while (cur->next != NULL) {
      cur = cur->next;
   }
   cur->next = list2;
   return list1;
}

void WhichImpliesWitFree(struct WhichImpliesWit * list) {
   if (list == NULL) return;
   AsrtListFree(list->pre);
   AsrtListFree(list->post);
   IntListFree(list->auto_solved);
   WhichImpliesWitFree(list->next);
   free(list);
}