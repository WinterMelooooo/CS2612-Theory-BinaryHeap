## Some API

### Main Function Pointers and Global Variables

SymExec/main.c 43~47 LocalDeepCopy LocalMerge LocalSubst LocalSubstPolyType LocalFree : You can change these function pointer to support different local situations. Our Local part in assertion syntax tree is a hashtable.

SymExec/main.c 54 recorded_witness : the recorder of all the witness 

SymExec/main.c 58 SepSolver : You can change the separation logic solver by edit this function pointer. 
SymExec/main.c 59 PropSolver : You can change the pure proposition smt solver by edit this function pointer.

SymExec/main.c 288 captured_asrt_nbcr : Current assertion, include nrm, brk, cnt and ret four parts.

SymExec/main.c 295 exec_func_begin_handler : You can do something at the function begin by edit this function , here we change non-addressable precondition into addressable precondition here.  

SymExec/main.c 318 exec_partial_statement_handler : You can do something at each partial statement by edit this function, here we step the symbolic execution statemachine and collect the witness.

SymExec/main.c 368 exec_func_end_handler : You can do something at the end of function by edit this function, here we collect the return witness.



### macro of error lines of C program
failwith(error_message)

### Assertion Printer
PrintAsrt(asrt, env); 
PrintAsrtFile(asrt, env, File);

### Assertion List Printer
PrintAsrtList(asrt_list,env); 
PrintAsrtListFile(asrt, env, File);

### User Assertion Printer
cpu_comment(asrt_list,env) : trans assertion_list into user assertion 
print_RA(user_assertion) : print user assertion 
print_RA_File(File, user_assertion) : print user assertion into File

### Symbolic execution Automation
SymExec/SymExec/StateMachine.c/StateMachineTransition : Single Step Symbolic Execution

SymExec/SymExec/StateMachine.c 289: CheckEntailment(struct AsrtList * pre, struct AsrtList * post, struct StringList * strategy_scopes, struct environment * env, struct EntailmentCheckerWit * entailment_checker_wit) : Try to solve pre |-- post by using strategies : strategy_scopes, the witness will stored in entailment_checker_wit.

### Failed Entailment Solver
SymExec/SymExec/WitnessDef/WitnessTrySolve.c/Failed_NestedSolver : Report Error Message of entailment