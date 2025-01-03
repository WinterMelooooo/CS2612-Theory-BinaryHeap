#ifndef ENTAILMENT_CHECKER_WIT_H
#define ENTAILMENT_CHECKER_WIT_H

#include "../../../compiler/env.h"
#include "../../AsrtDef/AssDef.h"
#include "../../Utility/List.h"

struct EntailmentCheckerWit {
   int auto_solved;
   struct AsrtList * pre, * post;
   struct StringList * strategy_scopes;
   struct EntailmentCheckerWit * next;
};

struct EntailmentCheckerWit * EntailmentCheckerWitNil();

struct EntailmentCheckerWit * EntailmentCheckerWitCons(struct AsrtList * pre, 
                                                       struct AsrtList * post, 
                                                       struct StringList * strategy_scopes,
                                                       struct EntailmentCheckerWit * next);

struct EntailmentCheckerWit * EntailmentCheckerWitLink(struct EntailmentCheckerWit * list1, struct EntailmentCheckerWit * list2);

void EntailmentCheckerWitFree(struct EntailmentCheckerWit * entailment_checker_wit);

struct EntailmentCheckerWit * CheckEntailment(struct AsrtList * pre, struct AsrtList * post, 
                                              struct StringList * strategy_scopes, struct environment * env,
                                              struct EntailmentCheckerWit * entailment_checker_wit);
#endif // ENTAILMENT_CHECKER_WIT_H