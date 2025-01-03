#ifndef PROPSOLVER_H
#define PROPSOLVER_H 1

#include "smt_solver.h"
#include <string.h>
#include <stdlib.h>

struct UFunction *Get_True_UF();

struct UFunction *Get_False_UF();

int SmtProp_list_length (struct SmtProplist *target); // 该函数计算SmtProp_list中有多少个prop

struct SmtProp * SmtProp_list_to_SmtProp(struct SmtProplist *prop_list); // 该函数会把一个prop list转化为&&链接的Prop

int SingleSmtPropCheck(struct SmtProp *source, struct SmtProp *target); // 这个函数检查source -> target是否成立,如果成立返回0,不成立返回-1,无法判断返回1

SMT_PROOF* SingleSmtPropCheck_proof(struct SmtProp *source, struct SmtProp *target); // 这个函数检查source -> target是否成立, proof->ans的值如果成立返回0,不成立返回-1,无法判断返回1
#endif