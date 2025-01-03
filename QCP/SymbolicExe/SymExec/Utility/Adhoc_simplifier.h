#ifndef AD_HOC_SIMPLIFIER
#define AD_HOC_SIMPLIFIER 1

#include "../AsrtDef/ExistDef.h"
#include "../AsrtDef/PropDef.h"

struct PropList *Quantifier_Adhoc_change(struct PropList *target_list, struct PropList *source_list, struct environment * env);

struct PropList *Adhoc_change_tar(struct PropList* target_list,struct PropList* source_list, struct environment * env);

struct PropList *Adhoc_change_src(struct PropList *source_list);
#endif