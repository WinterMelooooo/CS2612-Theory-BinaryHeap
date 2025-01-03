#ifndef LIA_THEORY_H
#define LIA_THEORY_H 1

#include <stdio.h>
#include<stdlib.h>
#include <stdbool.h>
#include <string.h>
#include<math.h>
#include"proof_lang.h"

#ifndef INT8_MAX 
#define INT8_MAX 127
#define INT8_MIN (-INT8_MAX - 1)
#define UINT8_MAX (INT8_MAX * 2 - 1)
#define INT16_MAX 32767
#define INT16_MIN (-INT16_MAX - 1)
#define UINT16_MAX (INT16_MAX * 2 - 1)
#define INT32_MAX 2147483647
#define INT32_MIN (-INT32_MAX - 1)
#define UINT32_MAX (INT32_MAX * 2 - 1)
#define INT64_MAX 9223372036854775807
#define INT64_MIN (-INT64_MAX - 1)
#define UINT64_MAX (INT64_MAX * 2 - 1)
#endif
#ifndef LIA_INT_MAX
#define LIA_INT_MAX INT32_MAX
#define LIA_INT_MIN INT32_MIN
#endif

typedef struct InequList InequList;

//链表的每一个节点是一个不等式
// a0+a1x1+a2x2+.... </<= 0
struct InequList{
    int* coef;       //coef[0]为常数量
    int strict;      // le为-1, lt为 1, eq为0, not eq为2
    InequList* next;
} ;

//存储原始不等式组信息
typedef struct {
    int numVariables; // 变量数量
    int numInequalities; // 不等式数量
    InequList* data;
    InequList* tail;
} LiaSystem;

typedef struct {
    InequList* upper;
    InequList* lower;
    InequList* remain;
} BoundPair;

typedef struct {
    int int8_max;
    int int16_max;
    int int32_max;
    int int64_max;
} MaxVar;

int gcd(int a, int b);

int sign_add_safe(int x, int y);

int mul_safe(int x, int y);

int check_add_safe(int x, int y);

InequList* initInequList();

void free_InequList(InequList* p);

void printInequlist(InequList* r, int n);
//删除形如a！=b的约束
InequList* delete_notEq(InequList* p);

InequList* copy_InequList(InequList* p, int num);

//删去xn相关约束，并且生成xn的upperbound list和lowerbound list
BoundPair* eliminate_xn(InequList* r, int num);

//r1中xn系数为正，r2中xn系数为负
int* generate_new_constraint(int* r1, int* r2, int num, int cur_num);

int* dark_generate_new_constraint(int* r1, int* r2, int num);

//r1和r2都有不存储信息的尾指针
//r1中所有不等式xn系数为正，r2所有不等式中xn系数为负
InequList* generate_new_constraint_list(InequList* r1, InequList* r2, int num, int cur_num);

//提取约束中的等式 ，复用boundpair结构，不过upper存等式，remain存剩余约束，lower=null
BoundPair* get_equation(InequList* r);

int* equ_eliminate(int* r1, int* r2, int elim_v, int n);
int* equ_eliminate_simplify(int* r1, int* r2, int* value, int size, int int8_max, int int16_max, int int32_max, int int64_max);
//消除等式约束
InequList* eliminate_equa_constraint(InequList* r1, InequList* r2, int* value, int num, int int8_max, int int16_max, int int32_max, int int64_max);

InequList* dark_generate_new_constraint_list(InequList* r1, InequList* r2, int num);

//消去x2,...xn,得到x1的实数域范围
//real shadow没有整数解，原问题必没有，若有整数解，原问题未必有
InequList* real_shadow(InequList* r, int* value, int n, int int8_max, int int16_max, int int32_max, int int64_max);

//dark shadow有整数解，原问题必有，若没有整数解，原问题未必没有
InequList* dark_shadow(InequList* r, int n);

//value数组用来表示是否包含变元i，value[i] = 0 表示没有变量i， =1表示有变量i， n表示不等式组最大的变元编号，int_max表示其对应的变量编号
int lia_theory_deduction(InequList* r1, InequList* r2, int* value, int n, int int8_max, int int16_max, int int32_max, int int64_max);


#endif