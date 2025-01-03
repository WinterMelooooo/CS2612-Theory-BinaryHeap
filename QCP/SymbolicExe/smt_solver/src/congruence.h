#ifndef CONGRUENCE_H
#define CONGRUENCE_H

#include <stdio.h>
#include<stdlib.h>
#include <stdbool.h>
#include"proof_lang.h"


typedef struct EquationNode EquationNode;
typedef struct ValNode ValNode;

struct EquationNode {
    int left1;
    int left2;              //左边非函数时left2=-1, 在lookuptable中代表返回不存在
    int right;
    EquationNode* next;
};

struct ValNode{
    int val;
    ValNode* next;
};

typedef struct{
    int left;
    int right;
} ConstantEquation;

typedef struct{
    int lleft1;
    int lleft2;
    int lright;
    int rleft1;
    int rleft2;
    int rright;
} Pair;

typedef union{
    Pair pair;
    ConstantEquation equation;
} Label;

typedef struct{
    int vertex;
    int labelType;    //0->undefine, 1->pair, 2->equation
    Label label;
} Edge;

// 定义等价类结构
typedef struct {
    int parent;
    int size;                          
} EquivalenceClass;


typedef struct{
    EquationNode* pendinglist;
    EquationNode* pendingProofs;
    EquationNode** uselist;
    ValNode** classlist; 
    EquivalenceClass* representative;
    EquivalenceClass* classes; //用于在explain时构建等价类
    EquationNode** lookupTable;
    Edge *edgelist;                //描述proof forest
} database;

void unionNode(EquivalenceClass* classes, int x, int y); //在explain中所使用的union操作，y应为parent(x) 不采用按秩合并，需要维持highestnode

int nearestCommonAncestor(database* S, int x, int y);   //explain中寻找两者的最近公共祖先

int findRoot(EquivalenceClass* classes, int x);         // 查找根节点

EquationNode* createEquationNode(int left1, int left2, int right);

void freeEquationlist(EquationNode* list);

ValNode* createValNode(int val);

void freeValist(ValNode* list);

database* initialize(int n);

void freeMemory(database* S, int n);

void propagate(database* S);

void merge(database* S, EquationNode* input);

bool areCongruent(database* S, int a1, int a2);

void explainAlongPath(database* S,int a, int c);

void explain(database* S, int a, int b);



//返回a=b的证明
//ProofNode* explain_p(database* S, int a, int b);


#endif