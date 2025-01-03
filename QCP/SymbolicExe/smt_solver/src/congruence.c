#include <stdio.h>
#include<stdlib.h>
#include <stdbool.h>
#include <string.h>
#include"congruence.h"
#define CONG_DEBUG 1

void unionNode(EquivalenceClass* classes, int x, int y){ //在explain中所使用的union操作，y应为parent(x) 不采用按秩合并，需要维持highestnode
    classes[x].parent = y;
    classes[x].size = classes[y].size; //此处size代表highestNode的编号
}

//反转proof forest中x指向root的边
int reverse_edge(database* S, int x){
    int x1 = x;
    int x2 = S->edgelist[x].vertex;
    while(x2 != 0){
        int next = S->edgelist[x2].vertex;

        S->edgelist[x2].vertex = x1;
        S->edgelist[x2].labelType = S->edgelist[x1].labelType;
        S->edgelist[x2].label = S->edgelist[x1].label;

        x1 = x2;
        x2 = next;
    }
}

int nearestCommonAncestor(database* S, int x, int y){
    if(x == y) return x;
    int lengthx = 0;
    int lengthy = 0;
    int tmpx = x;
    int tmpy = y;
    while(S->edgelist[tmpx].vertex != 0){
        lengthx++;
        tmpx = S->edgelist[tmpx].vertex;
    }
    while(S->edgelist[tmpy].vertex != 0){
        lengthy++;
        tmpy = S->edgelist[tmpy].vertex;
    }
    tmpx = x;
    tmpy = y;
    if(lengthx > lengthy){
        int diff = lengthx - lengthy;
        while(diff > 0){
            x = S->edgelist[x].vertex;
            diff--;
        }
    }
    else{
        int diff = lengthy - lengthx;
        while(diff > 0){
            y = S->edgelist[y].vertex;
            diff--;
        }
    }
    while(x != 0 && y != 0){
        if(x == y) return x;
        else{
            x = S->edgelist[x].vertex;
            y = S->edgelist[y].vertex;
        }
    }
    printf("no common ancestor between %d and %d", tmpx, tmpy);
    return 0;
}


// 查找根节点
int findRoot(EquivalenceClass* classes, int x) {
    if (classes[x].parent != x) {
        classes[x].parent = findRoot(classes, classes[x].parent);
    }
    return classes[x].parent;
}

EquationNode* createEquationNode(int left1, int left2, int right){
    EquationNode* node = (EquationNode*)malloc(sizeof(EquationNode));
    node->left1 = left1;
    node->left2 = left2;
    node->right = right;
    node->next = NULL;
    return node;
}

void freeEquationlist(EquationNode* list){
    EquationNode* p;
    while(list != NULL){
        p = list;
        list = list->next;
        free(p);
    }
}

ValNode* createValNode(int val){
    ValNode* node = (ValNode*)malloc(sizeof(ValNode));
    node->val = val;
    node->next = NULL;
    return node;
}

void freeValist(ValNode* list){
    ValNode* p;
    while(list != NULL){
        p = list;
        list = list->next;
        free(p);
    }
}

database* initialize(int n){
    database* S = (database*)malloc(sizeof(database));
    memset(S, 0, sizeof(database));
    S->pendinglist = NULL;
    S->pendingProofs = NULL;
    S->uselist = (EquationNode**)malloc(sizeof(EquationNode*)*(n+1));
    memset(S->uselist, 0, sizeof(EquationNode*)*(n+1));
    S->lookupTable = (EquationNode**)malloc(sizeof(EquationNode*)*(n+1));
    memset(S->lookupTable, 0, sizeof(EquationNode*)*(n+1));
    S->classlist = (ValNode**)malloc(sizeof(ValNode*)*(n+1));
    memset(S->classlist, 0, sizeof(ValNode*)*(n+1));
    S->representative = (EquivalenceClass*)malloc(sizeof(EquivalenceClass)*(n+1));
    memset(S->representative, 0, sizeof(EquivalenceClass)*(n+1));
    S->classes = (EquivalenceClass*)malloc(sizeof(EquivalenceClass)*(n+1));
    memset(S->classes, 0, sizeof(EquivalenceClass)*(n+1));
    S->edgelist = (Edge*)malloc(sizeof(Edge)*(n+1));
    memset(S->edgelist, 0, sizeof(Edge)*(n+1));
    for(int i = 1; i <= n; i++){
        S->classlist[i] = createValNode(i);
        S->uselist[i] = NULL;
        S->representative[i].parent = i;
        S->classes[i].parent = i;
        S->representative[i].size = 1;
        S->classes[i].size = i;                       //初始每个点的highestNode是自己
        S->edgelist[i].labelType = 0;
        S->edgelist[i].vertex = 0;
        S->lookupTable[i] = (EquationNode*)malloc(sizeof(EquationNode)*(n+1));
        memset(S->lookupTable[i], 0, sizeof(EquationNode)*(n+1));
        for(int j = 1; j <= n; j++) S->lookupTable[i][j].left2 = -1;
    }
    return S;

}

void freeMemory(database* S, int n){
    free(S->edgelist);
    free(S->representative);
    free(S->pendinglist);
    for(int i = 1; i <= n; i++){
        free(S->lookupTable[i]);
        freeEquationlist(S->uselist[i]);
        freeValist(S->classlist[i]);
    }
    free(S->lookupTable);
    free(S->classes);
    free(S->uselist);
    free(S->classlist);
    free(S);
}

void propagate(database* S){
    while(S->pendinglist != NULL){
        EquationNode* term1 = S->pendinglist;
        EquationNode* term2 = S->pendinglist->next;
        int a = term1->left1;
        int b = term1->right;
        if(term1->left2 == -1){
            S->pendinglist = term2;
        }
        else{
            a = term1->right;
            b = term2->right;
            if(term2 == NULL) 
                printf("unexpected case");
            S->pendinglist = term2->next;
        }
            
        int rep_a = findRoot(S->representative, a);
        int rep_b = findRoot(S->representative, b);
        if(S->representative[rep_a].size > S->representative[rep_b].size){  //a为size较小的类
            int tmp1 = a;
            int tmp2 = rep_a;
            a = b;
            rep_a = rep_b;
            b = tmp1;
            rep_b = tmp2;
        }

        if(rep_a != rep_b){
            reverse_edge(S, a);
            S->edgelist[a].vertex = b;
            if(term1->left2 == -1){
                S->edgelist[a].labelType = 2;
                S->edgelist[a].label.equation.left = a;
                S->edgelist[a].label.equation.right = b;
                free(term1);
            }
            else{
                S->edgelist[a].labelType = 1;
                S->edgelist[a].label.pair.lleft1 = term1->left1;
                S->edgelist[a].label.pair.lleft2 = term1->left2;
                S->edgelist[a].label.pair.lright = term1->right;
                S->edgelist[a].label.pair.rleft1 = term2->left1;
                S->edgelist[a].label.pair.rleft2 = term2->left2;
                S->edgelist[a].label.pair.rright = term2->right;
                free(term1);
                free(term2);
            }
            ValNode* list1 = S->classlist[rep_a];
            ValNode* list2 = S->classlist[rep_b];
            while(list1 != NULL){
                S->representative[list1->val].parent = rep_b;
                list1 = list1->next;
            }
            if(list2 == NULL) 
                printf("unexpected case");
            while(list2->next != NULL){
                    list2 = list2->next;
            }
            list2->next = S->classlist[rep_a];
            S->classlist[rep_a] = NULL;
            S->representative[rep_b].size += S->representative[rep_a].size;   

            EquationNode* usel = S->uselist[rep_a];
            while(usel != NULL){
                int c1 = usel->left1;
                int c2 = usel->left2;
                int c = usel->right;   //f(c1,c2) = c;
                int rep_c1 = findRoot(S->representative,c1);
                int rep_c2 = findRoot(S->representative,c2);
                int d1 = S->lookupTable[rep_c1][rep_c2].left1;
                int d2 = S->lookupTable[rep_c1][rep_c2].left2;
                int d = S->lookupTable[rep_c1][rep_c2].right;
                if(d2 != -1){
                    EquationNode* node1 = createEquationNode(c1, c2, c);
                    EquationNode* node2 = createEquationNode(d1, d2, d);
                    node1->next = node2;
                    node2->next = S->pendinglist;
                    S->pendinglist = node1;
                    S->uselist[rep_a] = usel->next;
                    free(usel);
                    usel = S->uselist[rep_a];
                }
                else{
                    S->lookupTable[rep_c1][rep_c2].left1 = c1;
                    S->lookupTable[rep_c1][rep_c2].left2 = c2;
                    S->lookupTable[rep_c1][rep_c2].right = c;
                    S->uselist[rep_a] = usel->next;
                    usel->next = S->uselist[rep_b];
                    S->uselist[rep_b] = usel;
                    usel = S->uselist[rep_a];
                }
            }
        }      
    }
}

void merge(database* S, EquationNode* input){
    if(input == NULL) return;
    while(input->next != NULL){
        EquationNode* cur = input;
        if(cur->left2 == -1){
            EquationNode* node = createEquationNode(cur->left1, -1, cur->right);
            node->next = S->pendinglist;
            S->pendinglist = node;
            propagate(S);
        }
        else{
            int a1 = input->left1;
            int a2 = input->left2;
            int a = input->right;
            int rep_a1 = findRoot(S->representative, a1);
            int rep_a2 = findRoot(S->representative, a2);
            int d1 = S->lookupTable[rep_a1][rep_a2].left1;
            int d2 = S->lookupTable[rep_a1][rep_a2].left2;
            int d = S->lookupTable[rep_a1][rep_a2].right;
            if(d2 != -1){
                EquationNode* node1 = createEquationNode(a1, a2, a);
                EquationNode* node2 = createEquationNode(d1, d2, d);
                node1->next = node2;
                node2->next = S->pendinglist;
                S->pendinglist = node1;
                propagate(S);
            }
            else{
                S->lookupTable[rep_a1][rep_a2].left1 = a1;
                S->lookupTable[rep_a1][rep_a2].left2 = a2;
                S->lookupTable[rep_a1][rep_a2].right = a;
                EquationNode* node1 = createEquationNode(a1, a2, a);
                EquationNode* node2 = createEquationNode(a1, a2, a);
                node1->next = S->uselist[rep_a1];
                S->uselist[rep_a1] = node1;
                node2->next = S->uselist[rep_a2];
                S->uselist[rep_a2] = node2;
            }
        }
        input = input->next;
    }

}

bool areCongruent(database* S, int a1, int a2){
    if(a1 == a2) return true; 
    int rep_a1 = findRoot(S->representative, a1);
    int rep_a2 = findRoot(S->representative, a2);
    return rep_a1 == rep_a2;
}

void explainAlongPath(database* S,int a, int c){
    a = findRoot(S->classes, a); //a := HighestNode(a)
    while(a != c){
        int b = S->edgelist[a].vertex;
        if(S->edgelist[a].labelType == 2){
            printf("%d = %d\n", S->edgelist[a].label.equation.left, S->edgelist[a].label.equation.right);
        }
        else if(S->edgelist[a].labelType == 1){
            printf("f(%d, %d) = %d\nf(%d, %d) = %d\n",S->edgelist[a].label.pair.lleft1, S->edgelist[a].label.pair.lleft2,
            S->edgelist[a].label.pair.lright, S->edgelist[a].label.pair.rleft1, S->edgelist[a].label.pair.rleft2,S->edgelist[a].label.pair.rright);
            EquationNode* node1 =createEquationNode(S->edgelist[a].label.pair.lleft1, -1, S->edgelist[a].label.pair.rleft1);
            EquationNode* node2 =createEquationNode(S->edgelist[a].label.pair.lleft2, -1, S->edgelist[a].label.pair.rleft2);
            node1->next = node2;
            node2->next = S->pendingProofs;
            S->pendingProofs = node1;
            
        }
        unionNode(S->classes, a, b);
        a = findRoot(S->classes, a);     //a := HighestNode(b)
    }

}

void explain(database* S, int a, int b){
     S->pendingProofs = createEquationNode(a, -1, b);
     while(S->pendingProofs != NULL){
        EquationNode* tmp = S->pendingProofs;
        int left = S->pendingProofs->left1;
        int right = S->pendingProofs->right;
        S->pendingProofs = S->pendingProofs->next;
        free(tmp);
        int com = nearestCommonAncestor(S, left, right);
        com = S->classes[com].size;
        explainAlongPath(S, left, com);
        explainAlongPath(S, right, com);
     }
}

