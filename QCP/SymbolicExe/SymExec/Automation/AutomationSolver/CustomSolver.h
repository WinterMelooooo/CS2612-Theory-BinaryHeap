#ifndef _CUSTOM_SOLVER
#define _CUSTOM_SOLVER

#include"solver.h"
#include"../dsl_match/ASTtoLibRule.h"
#include"../../Utility/List.h"

void initStrategyLibInScopesSingle(char * path, struct environment * env);
void initStrategyLibInScopes(struct environment * env);
void finiStrategyAll();

struct EntailRetType * custom_solve(struct Assertion * pre, struct Assertion * post, struct environment * env, struct StringList *scope);
struct EntailRetType * custom_solve_no_core(struct Assertion * pre, struct Assertion * post,struct environment * env, struct StringList * scope);
struct EntailRetType *prop_cancel_solve(struct Assertion * pre, struct Assertion * post, struct environment * env);
struct EntailRetType *post_solve(struct Assertion * pre, struct Assertion * post, struct environment * env);
struct EntailRetType *tag_cancel_solve(struct Assertion * pre, struct Assertion * post, struct environment * env);

char *get_global_var(char *name);

void setIncludePath();

#endif