#ifndef StateMachine_H
#define StateMachine_H

#include "../../compiler/env.h"
#include "../CDef/PartialStmt.h"
#include "./WitnessDef/Witness.h"

struct SymbolicExecRet {
   struct StateStack * state_stack;
   struct AsrtTuple * asrt;
   struct AsrtList * inv;
   struct Witness * witness;
};

struct AsrtListWitnessPair {
   struct AsrtList * asrt_list;
   struct Witness * witness;
};

enum TransType {
   NormalTrans, TransForInvCheck
};

struct SymbolicExecRet StateMachineTransition(
            struct PartialStmt * ps, struct AsrtList * inv, 
            struct StateStack * state_stack, struct AsrtTuple * asrt,  
            struct environment * env, enum TransType trans_type);

struct SymbolicExecRet SymbolicExecForInvCheck(struct PartialStmt *begin, struct PartialStmt *end, 
                                               struct StateStack * state_machine, struct AsrtTuple *precondition,
                                               struct environment * env);
               
struct SymbolicExecRet MakeSymbolicExecRet(struct StateStack * state_stack, 
                                 struct AsrtTuple * asrt, struct AsrtList * inv, struct Witness * witness);

struct AsrtListWitnessPair MakeAsrtListWitnessPair(struct AsrtList * asrt_list, struct Witness * witness);

struct AsrtTuple * StateMachineFuncEnd(struct AsrtTuple * asrt, struct StateStack * state_stack, struct environment * env);

#endif // StateMachine_H