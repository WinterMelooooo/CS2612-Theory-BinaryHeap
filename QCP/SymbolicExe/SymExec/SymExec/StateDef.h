#ifndef STATE_DEF_H
#define STATE_DEF_H

#include "../CDef/PartialStmt.h"
#include "../../compiler/env.h"

struct AsrtTuple {
   struct AsrtList *nrm, *brk, *cnt;
   struct FuncRetTypeList *ret;
};

struct AsrtTuple * CreateAsrtTuple(struct AsrtList * nrm, struct AsrtList * brk,
                                    struct AsrtList * cnt, struct FuncRetTypeList * ret);

enum StateType {
   In_Global,
   In_func_block,
   Get_Inv,
   In_while_block,
   In_do_block,
   In_for_block,
   In_switch_block,
   In_switch_cases_block,
   In_switch_default_block,
   In_if_then_block,
   In_if_else_block,
   In_block                    // some eccentric cases, like `int a; { int a; { int a; } }`
};

struct State {
   enum StateType t;
   union {
      struct {} In_Global;
      struct {} In_func_block;
      struct {} Get_Inv;
      struct { 
         int inv_explicit;
         struct AsrtTuple * asrt;              // record cnt, brk, ret before entering the loop
                                              // asrt->nrm records (precondition && !condition) if inv_in_front == 0
                                              //           records (inv && !condition) if inv_in_front == 1
         struct PartialStmt * start;          // record the start of the loop(The position of while(e))
         struct AsrtList * inv;               
         struct Cexpr * condition;            
         struct AsrtList * precondition;      // nrm part of asrt before entering the loop
      } In_while_block;                       // inv and precondition should be freed when destructing
      struct {
         int inv_explicit;
         struct AsrtTuple * asrt; 
         struct PartialStmt * start; 
         struct AsrtList * inv; 
         struct Cexpr * condition;
      } In_do_block;
      struct { 
         int inv_explicit;
         struct AsrtTuple * asrt; 
         struct PartialStmt * start; 
         struct AsrtList * inv; 
         struct Cexpr * condition; 
         struct CSimpleCommand * afterthought;
      } In_for_block;
      struct { struct Cexpr * expr; struct AsrtTuple * asrt; } In_switch_block;       // record asrt which not satisfy the all above conditions
      struct { struct Cexpr * expr; struct AsrtTuple * asrt; } In_switch_cases_block;
      struct { struct AsrtTuple * asrt; } In_switch_default_block;
      struct { struct AsrtList * false_part_asrt;  } In_if_then_block;
      struct { struct AsrtList * true_part_asrt; } In_if_else_block;
   }d;
   struct PSVarDefList * defined_vars;   // record the variables defined in this block
   int depth;
};

struct StateStack {
   struct State * state;
   struct StateStack * next;
};

struct State * CreateState(enum StateType type, struct StateStack * stack);
void StateFree(struct State * state);
char* StateTypeToString(enum StateType t);
struct Assertion * AssertionVarPerish(struct Assertion * asrt, struct State * state, struct environment * env);
struct AsrtList * AsrtListVarPerish(struct AsrtList * asrt_list, struct State * state, struct environment * env);

int IsContinueRelatedType(enum StateType t);
int IsBreakRelatedType(enum StateType t);


struct StateStack * StartStateMachineInFunc();
struct StateStack * StateStackPush(struct StateStack * stack, struct State * state);
struct StateStack * StateStackPop(struct StateStack * stack);
struct State * StateStackPeek(struct StateStack * stack);

#endif // STATE_DEF_H