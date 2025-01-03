#ifndef PROP_TO_SMT_PROP_TRANS_INCLUDED
#define PROP_TO_SMT_PROP_TRANS_INCLUDED

#include "../../compiler/env.h"
#include "../AsrtDef/ExistDef.h"
#include "../AsrtDef/PropDef.h"
#include "../Utility/Adhoc_simplifier.h"
#include "../../smt_solver/src/Prop_solver.h"

#define enumToStr(s) #s

struct Prop_solver_return {
    int result; 
    struct PropList * res_prop;
};// result 表示Prop solver的结果 1表示success， -1表示fail，此时PropList为fail的prop， 0表示Unknown，此时PropList为Unknown的prop

struct SmtTerm * ExprValTransSmtTerm(struct ExprVal *expr, struct environment * env);

struct SmtProp * PropTransSmtProp(struct Proposition * source_prop, struct environment * env);

struct SmtProplist * ProplistTransSmtProplist(struct PropList * source_prop_list, struct environment * env);

struct Prop_solver_return * PropEntail(struct PropList *source_prop_list, struct PropList *target_prop_list, struct environment * env); 

void Prop_solver_return_free(struct Prop_solver_return * prop_solver_return);

#endif