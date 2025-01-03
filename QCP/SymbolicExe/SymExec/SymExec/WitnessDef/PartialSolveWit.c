#include "PartialSolveWit.h"

struct PartialSolveWit * PartialSolveWitNil() {
   return NULL;
}

struct PartialSolveWit * PartialSolveWitCons(struct Assertion * pre, 
                                             struct Assertion * post, 
                                             struct Assertion *  frame, 
                                             struct StringList * strategy_scopes,
                                             struct PartialSolveWit * next) {
   struct PartialSolveWit * ret;
   ret = (struct PartialSolveWit *) malloc(sizeof(struct PartialSolveWit));
   ret->pre = pre;
   ret->post = post;
   ret->frame = frame;
   ret->next = next;
   ret->auto_solved = 0;
   ret->strategy_scopes = strategy_scopes;
   return ret;
}

struct PartialSolveWit * PartialSolveWitLink(struct PartialSolveWit * wit1, struct PartialSolveWit * wit2) {
   if (wit1 == NULL) return wit2;
   if (wit2 == NULL) return wit1;
   struct PartialSolveWit * tmp = wit1;
   while (tmp->next != NULL) {
      tmp = tmp->next;
   }
   tmp->next = wit2;
   return wit1;
}

void PartialSolveWitFree(struct PartialSolveWit * wit) {
   if (wit == NULL) return;
   AsrtFree(wit->pre);
   AsrtFree(wit->post);
   AsrtFree(wit->frame);
   PartialSolveWitFree(wit->next);
   free(wit);
}
