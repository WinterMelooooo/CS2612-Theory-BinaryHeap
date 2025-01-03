#ifndef FP_SPEC_DEF
#define FP_SPEC_DEF

#include "SimpleCtypeDef.h"
#include "PolyTypeDef.h"
#include "../Utility/List.h"

struct persistent_env;

struct FPSpec
{
  struct ExprVal *fp_addr;
  struct func_info *func_info;
};

struct FPSpec * CreateFPSepc(struct ExprVal * fp_addr, struct func_info * func_info);

struct FPSpec * FPSpecDeepCopy(struct FPSpec * spec);

void FPSpecFree(struct FPSpec * spec);

DECLARE_LIST(FPSpecList, struct FPSpec*, data)

struct func_info * FPSpecListFind(struct ExprVal * fp_addr, struct FPSpecList * list);

struct FPSpec * FPSpecSubst(struct FPSpec * spec, struct ExprVal * pre, struct ExprVal * post);
struct FPSpec * FPSpecSubstPolyType(struct FPSpec * spec, struct PolyType * pre, struct PolyType * post, struct persistent_env * env);
struct FPSpecList * FPSpecListSubst(struct FPSpecList * list, struct ExprVal * pre, struct ExprVal * post);
struct FPSpecList * FPSpecListSubstPolyType(struct FPSpecList * list, struct PolyType * pre, struct PolyType * post, struct persistent_env * env);

#endif
