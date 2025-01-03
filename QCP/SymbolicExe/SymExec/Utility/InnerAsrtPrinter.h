#ifndef INNERASRTPRINTER_INCLUDED
#define INNERASRTPRINTER_INCLUDED

#include "../AsrtDef/AssDef.h"
#include "../AsrtDef/ExistDef.h"
#include "../AsrtDef/PropDef.h"
#include "../AsrtDef/LocalDef.h"
#include "../AsrtDef/SepDef.h"
#include "../SymExec/StateDef.h"
#include "../../compiler/env.h"

void PrintPolyType(struct PolyType * type, struct environment * env);
void PrintLogicVar(int id, struct environment * env);
void PrintExprVal(struct ExprVal *expr, struct environment * env);
void PrintExprValList(struct ExprValList * list, struct environment * env);
void PrintExistList(struct ExistList * list, struct environment * env);
char* PrintPropUOp_str(enum PropUOP op);
char* PrintPropBinOp_str(enum PropBinOP op);
char* PrintPropPtrOp_str(enum PropPtrOP op);
char* PrintPropCmpOp_str(enum PropCompOp op);
void PrintProp(struct Proposition * prop, struct environment * env);
void PrintPropList(struct PropList * list, struct environment * env);
void PrintLocalList(struct LocalLinkedHashMap * list, struct environment * env);
void PrintSep(struct Separation *sep, struct environment * env);
void PrintSepList(struct SepList * list, struct environment * env);
void PrintFuncSpec(struct func_spec * spec, struct environment * env);
void PrintAsrt(struct Assertion * asrt, struct environment * env);
void PrintAsrtFP(struct Assertion * asrt, struct environment * env);
void PrintAsrtList(struct AsrtList * list, struct environment * env);
void PrintFuncRetType(struct FuncRetType * ret, struct environment * env);
void PrintAsrtTuple(struct AsrtTuple * asrt_nbcr, struct environment * env);
void PrintFuncRetType(struct FuncRetType * ret, struct environment * env);
void PrintAsrtAllMemInfo(struct Assertion * asrt);

void PrintPolyTypeFile(struct PolyType * type, struct environment * env, FILE * fp);
void PrintLogicVarFile(int id, struct environment * env, FILE * fp);
void PrintExprValFile(struct ExprVal *expr, struct environment * env, FILE * fp);
void PrintExprValListFile(struct ExprValList * list, struct environment * env, FILE * fp);
void PrintExistListFile(struct ExistList * list, struct environment * env, FILE * fp);
void PrintPropFile(struct Proposition * prop, struct environment * env, FILE * fp);
void PrintPropListFile(struct PropList * list, struct environment * env, FILE * fp);
void PrintLocalListFile(struct LocalLinkedHashMap * list, struct environment * env, FILE * fp);
void PrintSepFile(struct Separation *sep, struct environment * env, FILE * fp);
void PrintSepListFile(struct SepList * list, struct environment * env, FILE * fp);
void PrintFuncSpecFile(struct func_spec * spec, struct environment * env, FILE * fp);
void PrintAsrtFile(struct Assertion * asrt, struct environment * env, FILE * fp);
void PrintAsrtFPFile(struct Assertion * asrt, struct environment * env, FILE * fp);
void PrintAsrtListFile(struct AsrtList * list, struct environment * env, FILE * fp);
void PrintFuncRetTypeFile(struct FuncRetType * ret, struct environment * env, FILE * fp);
void PrintAsrtTupleFile(struct AsrtTuple * asrt_nbcr, struct environment * env, FILE * fp);

// for debug
void PrintPropNoEnv(struct Proposition * prop, FILE * fp);
void PrintPropListNoEnv(struct PropList * list, FILE * fp);
void PrintLocalListNoEnv(struct LocalLinkedHashMap * list, FILE * fp);
void PrintSepNoEnv(struct Separation *sep, FILE * fp);
void PrintSepListNoEnv(struct SepList * list, FILE * fp);
void PrintAsrtNoEnv(struct Assertion * asrt, FILE * fp);
void PrintAsrtListNoEnv(struct AsrtList * list, FILE * fp);
void PrintPolyArgListNoEnv(struct PolyTypeList * types, struct ExprValList * args, FILE * fp);

struct atype *InnerExprInfer(struct ExprVal *val, struct environment *env);
#endif