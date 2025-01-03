#ifndef SAFEFY_CHECKER_WIT_H
#define SAFEFY_CHECKER_WIT_H

#include "../../AsrtDef/AssDef.h"
#include "../../Utility/List.h"

struct SafetyCheckerWit {
   int auto_solved;
   struct Assertion * asrt;
   struct PropList * constraits;
   struct SafetyCheckerWit * next;
};

struct SafetyCheckerWit * SafetyCheckerWitNil();
struct SafetyCheckerWit * SafetyCheckerWitCons(struct Assertion * asrt, 
                                               struct PropList * constraits, 
                                               struct SafetyCheckerWit * next);
struct SafetyCheckerWit * SafetyCheckerWitLink(struct SafetyCheckerWit * list1, struct SafetyCheckerWit * list2);
void SafetyCheckerWitFree(struct SafetyCheckerWit * safety_checker_wit);

#endif // SAFEFY_CHECKER_WIT_H