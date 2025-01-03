#ifndef PARTIAL_SOLVE_WIT
#define PARTIAL_SOLVE_WIT

#include "../../../compiler/env.h"
#include "../../AsrtDef/AssDef.h"
#include "../../Utility/List.h"

/*
auto proof : if Pure1 && Q1  |-- Pure2 then Pure1 && P1  |-- Pure2 && P2 ** Q1
user's obligation : Pure1 && Q1  |-- Pure2

pre := Pure1 && P1
post := Pure2 && P2
frame := Q1

auto proof : if pre |-- post->prop, then pre |-- post ** frame
user's obligation : pre |-- post->prop
*/

struct PartialSolveWit {
   int auto_solved;
   struct Assertion * pre, * post, * frame;
   struct StringList * strategy_scopes;
   struct PartialSolveWit * next;
};

struct PartialSolveWit * PartialSolveWitNil();
struct PartialSolveWit * PartialSolveWitCons(struct Assertion * pre, 
                                             struct Assertion * post, 
                                             struct Assertion *  frame, 
                                             struct StringList * strategy_scopes,
                                             struct PartialSolveWit * next);
struct PartialSolveWit * PartialSolveWitLink(struct PartialSolveWit * wit1, struct PartialSolveWit * wit2);
void PartialSolveWitFree(struct PartialSolveWit * wit);

#endif 