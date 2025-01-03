#ifndef LOGIC_NAME_MANAGER_H
#define LOGIC_NAME_MANAGER_H

#include "../../compiler/env.h"

void LogicNameManagerInit(struct environment * env);

int GetNewLogicVar();

void AsrtNormalizeName(struct Assertion * asrt, int asrt_id, int branch_id, int is_old, struct environment * env);
void AsrtListNormalizeName(struct AsrtList * asrt_list, struct environment * env);
void PrePostAsrtNormalizeName(struct Assertion * asrt, int asrt_id, int branch_id, int is_pre, struct environment * env);
void PrePostAsrtListNormalizeName(struct AsrtList * asrt_list, int is_pre, struct environment * env);
void WithVarNormalizeName(struct ExistList * with_list, struct environment * env);
#endif