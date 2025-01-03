#ifndef FUNC_CALL_WIT_H
#define FUNC_CALL_WIT_H

#include "../../../compiler/env.h"
#include "../../AsrtDef/AssDef.h"
#include "../../Utility/List.h"

// own the memory of *spec*, args, with_vals, pre, frame
struct FuncCallWit {
   struct func_spec * spec;
   struct ExprValList * param, * args, * with_vals;
   struct Assertion * pre, * frame;
   struct ExistList * post_exist_inst;
   struct FuncCallWit * next;
};

struct FuncCallWit * FuncCallWitNil();
struct FuncCallWit * FuncCallWitCons(struct func_spec * spec, 
                                     struct ExprValList * param, struct ExprValList * args, struct ExprValList * with_vals, 
                                     struct Assertion * pre, struct Assertion * frame, 
                                     struct ExistList * post_exist_inst, struct FuncCallWit * next);
struct FuncCallWit * FuncCallWitLink(struct FuncCallWit * wit1, struct FuncCallWit * wit2);
void FuncCallWitFree(struct FuncCallWit * wit);
struct AsrtList * FuncCallWitRecoverPost(struct FuncCallWit * wit, struct environment * env);

#endif // FUNC_CALL_WIT_H