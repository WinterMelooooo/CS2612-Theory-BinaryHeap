#ifndef FUNC_CALL_H
#define FUNC_CALL_H

#include "ExprExecRetTypeDef.h"
#include "../AsrtDef/AssDef.h"
#include "../../compiler/env.h"
#include "../Trans/PropToSmtPropTrans.h"

struct func_spec * DeclareSpec(struct ExistList * witht,
                               struct ExistList * with,
                               struct AsrtList * pre,
                               struct AsrtList * post,
                               struct ExprVal * __return,
                               struct qvar_list * qv);

// struct_field, partial_solve, ... are solve implemented by func-call 
// but renaming should have different implementation
enum CallType {
   NORMAL_CALL, FIELD_CALL, PARTIAL_CALL, PREFILL_CALL, WHICH_IMPLIES_CALL
};

enum PrefillValueType {
   PREFILL_EXPRVAL, PREFILL_TYPE
};

struct PrefillValue {
   enum PrefillValueType t;
   union {
      struct ExprVal * value;
      struct PolyType * type;
   } d;
};

struct PrefillValue * PrefillExprVal(struct ExprVal * value);
struct PrefillValue * PrefillType(struct PolyType * type);

// Currently only used for single assertion derives single assertion, so next is always NULL
struct EntailRetType {
   struct Assertion * frame;
   struct IntList * introed_vars;
   struct hashtbl * ex_instance;         // map name to expr_val
   struct Witness * witness;
};

struct EntailRetType * CreateEntailRetType(struct Assertion * frame, struct IntList * introed_vars, struct hashtbl * ex_instance, struct Witness * witness); 

void EntailRetTypeFree(struct EntailRetType * ret);

struct FuncCallRetType {
   struct ExprExecRetType * ret;
   struct hashtbl * ex_instance;         // != NULL only when call_type == PREFILL_CALL
};

struct FuncCallRetType * CreateFuncCallRetType(struct ExprExecRetType * ret, struct hashtbl * ex_instance);
void FuncCallRetTypeFree(struct FuncCallRetType * ret);

struct FuncCallRetType * FuncCallExec(
   struct Assertion * asrt, struct environment * env,
   struct prog_var_info_list * param, struct func_spec * spec, struct hashtbl * prefill,
   struct ExprValList * args, enum CallType call_type, struct StringList * scopes);

struct WhichImpliesRetType {
   struct AsrtList * asrt;
   struct Witness * witness;
};

struct WhichImpliesRetType * CreateWhichImpliesRetType(struct AsrtList * asrt, struct Witness * witness);
struct WhichImpliesRetType * WhichImpliesRetTypeMerge(struct WhichImpliesRetType * w1, struct WhichImpliesRetType * w2);
void WhichImpliesRetTypeFree(struct WhichImpliesRetType * ret);

struct WhichImpliesRetType * PartialSolveSingleAssert(struct Assertion * pre, struct Assertion * post, struct StringList * scopes, struct environment * env);
struct WhichImpliesRetType * PartialSolveSingleInv(struct Assertion * pre, struct Assertion * post, struct StringList * scopes, struct environment * env);
struct WhichImpliesRetType * PartialSolveInv(struct AsrtList * pre, struct AsrtList * post, struct StringList * scopes, struct environment * env);
struct WhichImpliesRetType * PartialSolveAssert(struct AsrtList * pre, struct AsrtList * post, struct StringList * scopes, struct environment * env);
struct WhichImpliesRetType * PartialSolveImplies(struct AsrtList * pre, struct func_spec * specs, struct StringList * scopes, struct environment * env);

struct ExprExecRetType * GetFuncPrefill(struct Assertion * asrt, struct VirtArg * varg, struct hashtbl * prefill, struct environment * env);
void PrintPrefillCharIndex(struct hashtbl * prefill, struct environment * env);
void PrintPrefillIntIndex(struct hashtbl * prefill, struct environment * env);

struct EntailRetType *SepLogicEntail(struct Assertion *pre,
                                     struct Assertion *post,
                                     struct StringList *scopes,
                                     struct environment *env);

#endif // FUNC_CALL_H
