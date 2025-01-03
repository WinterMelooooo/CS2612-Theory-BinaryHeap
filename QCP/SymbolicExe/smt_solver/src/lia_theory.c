#include"lia_theory.h"
//#define LIA_THEORY_DEBUG 1

int gcd(int a, int b)
{
    return b ? gcd(b, a % b) : a;
}

int sign_add_safe(int x, int y){
    int res = x + y;
    if(x > 0 && y > 0 && res < 0) {
        printf("add upper overflow \n");
        exit(-1);
    }
    if(x < 0 && y < 0 && res > 0) {
        printf("add lower overflow \n");
        exit(-1);
    }
    return res;
}

int mul_safe(int x, int y){
    if(x == 0 || y == 0) return 0;
    int res = x*y;
    if(res/y == x) return res;
    else{
        printf("multiple overflow \n");
        exit(-1);
    }
}

int check_add_safe(int x, int y){
    if (x > 0) {
        return y <= LIA_INT_MAX - x;
    }
    else {
        return y >= LIA_INT_MIN - x;
    }
}

InequList* copy_InequList(InequList* p, int num){
    InequList* res= initInequList();
    if(p == NULL){
        printf("error in copy Inequlist, invalid nullptr\n");
        exit(-1);
    }
    if(p->next == NULL) return res;
    else{
        InequList* p1 = p;
        InequList* p2 = res;
        while(p1->next != NULL){
            int* arr = (int*)malloc(sizeof(int)*(num+1));
            for(int i = 0; i <= num; i++) arr[i] = p1->coef[i];
            InequList* new_node = initInequList();
            new_node->coef = arr;
            new_node->strict = p1->strict;
            if(p2->next == NULL) {
                new_node->next = p2;
                p2 = new_node;
                res = p2;
            }
            else{
                new_node->next = p2->next;
                p2->next = new_node;
                p2 = new_node;
            }
            p1 = p1->next;
        }
    }
    return res;
}

InequList* delete_notEq(InequList* r){
    InequList* p = r;
    InequList* pre_p = NULL;
    if(r == NULL) {
        printf("here should not have nullptr\n");
        exit(-1);
    }
    if(r->next == NULL) return r;
    while(p->next != NULL){
        if(p->strict == 2){
            if(pre_p == NULL) {
                r = p->next;
                free(p->coef);
                free(p);
                p = r;
            }
            else{
                pre_p->next = p->next;
                free(p->coef);
                free(p);
                p = pre_p->next;
            }
        }
        else{
            pre_p = p;
            p = p->next;
        }
    }
    return r;
}

void printInequlist(InequList* r, int n){
    if(r == NULL) return;
    if(r->next == NULL) return;
    for(int i = 1; i <= n; i++){
        printf("%d*x%d + ", r->coef[i],i);
    }
    printf("%d ", r->coef[0]);
    if(r->strict == -1) printf("<= 0\n");
    else if(r->strict == 1) printf("< 0\n");
    else if(r->strict == 0) printf("= 0\n");
    else  printf("!= 0\n");
    printInequlist(r->next, n);
}

InequList* initInequList(){
    InequList* res = (InequList*)malloc(sizeof(InequList));
    res->coef = NULL;
    res->strict = 0;
    res->next = NULL;
    return res;
}

InequList* initInequList_test(int n){
    InequList* res = (InequList*)malloc(sizeof(InequList));
    res->coef = (int*)malloc(sizeof(int)*(n+1));
    memset(res->coef, 0, sizeof(int)*(n+1));
    res->strict = 0;
    res->next = NULL;
    return res;
}
void free_InequList(InequList* p){
    if(p == NULL) return;
    if(p->next != NULL) free_InequList(p->next);
    if(p->coef != NULL) free(p->coef);
    free(p);
}

//删去xn相关约束，并且生成xn的upperbound list和lowerbound list
//r有不存储信息的尾指针
BoundPair* eliminate_xn(InequList* r, int num){
    if(r == NULL){
        printf("error in eliminate_xn, should have tail pointer\n");
        exit(-1);
    }
    InequList* upper = initInequList();
    InequList* lower = initInequList();
    InequList* cur = r;
    InequList* pre_cur = NULL;
    while(cur->next != NULL){
        if(cur->coef[num] != 0){
            InequList* tmp = cur->next;
            if(cur->coef[num] > 0){
                cur->next = upper;
                upper = cur;
            }
            else {
                cur->next = lower;
                lower = cur;
            }
            if(pre_cur == NULL){
                cur = tmp;
                r = cur;
            }
            else {
                pre_cur->next = tmp;
                cur = tmp;
            }
            
        // printf("in eliminate_xn, after delete xn :\n");
        // printInequlist(r, num);
        }
        else {
            pre_cur = cur;
            cur = cur->next;
        }
    }
    BoundPair* res = (BoundPair*)malloc(sizeof(BoundPair));
    res->upper = upper;
    res->lower = lower;
    res->remain = r;
    return res;
}

BoundPair* get_equation(InequList* r){
    if(r == NULL){
        printf("error in eliminate_xn, should have tail pointer\n");
        exit(-1);
    }
    InequList* upper = initInequList();
    InequList* cur = r;
    InequList* pre_cur = NULL;
    while(cur->next != NULL){
        InequList* tmp = cur->next;
        if(cur->strict == 0){
            cur->next = upper;
            upper = cur;
        
            if(pre_cur == NULL){
                cur = tmp;
                r = cur;
            }
            else{
                pre_cur->next = tmp;
                cur = tmp;
            }
        }
        else{
            pre_cur = cur;
            cur = cur->next;
        }
    }
    BoundPair* res = (BoundPair*)malloc(sizeof(BoundPair));
    res->upper = upper;
    res->lower = NULL;
    res->remain = r;
    return res;
}

//r1中全为等式，r2中为不等式
InequList* eliminate_equa_constraint(InequList* r1, InequList* r2, int* value, int num, int int8_max, int int16_max, int int32_max, int int64_max){
    InequList* cur = r1;
    while(cur->next != NULL){
        InequList* equ = cur->next;
        InequList* tmp = r2;
        while(equ->next != NULL){
            int* res = equ_eliminate_simplify(cur->coef, equ->coef, value, num, int8_max, int16_max, int32_max, int64_max);
            if(res == NULL) return NULL;
            free(equ->coef);
            equ->coef = res;
            equ = equ->next;
        }     
        while(tmp->next != NULL){
            int* res = equ_eliminate_simplify(cur->coef, tmp->coef, value, num, int8_max, int16_max, int32_max, int64_max);
            if(res == NULL) return NULL;
            free(tmp->coef);
            tmp->coef = res;
            tmp = tmp->next;
        }
        if(equ->next == NULL && tmp->next == NULL){
            //即lia读入的是等式组，此时消元只剩一个等式
            int* res = equ_eliminate_simplify(cur->coef, cur->coef, value, num, int8_max, int16_max, int32_max, int64_max);
            if(res == NULL) return NULL;
            free(res);

        }
        cur = cur->next;
        #ifdef LIA_THEORY_DEBUG
        printf("elimata once: \n");
        printInequlist(r1, num);
        printInequlist(r2, num);
        printf("elimate end\n");
        #endif
    }
    return r2;
}

int* equ_eliminate(int* r1, int* r2, int elim_v, int n){
    int num = elim_v;
    int* res = (int*)malloc(sizeof(int)*(n+1));
    memset(res, 0, sizeof(int)*(n+1));
    if(num == 0 || r2[num] == 0){
        for(int i = 0; i <= n; i++)
            res[i] = r2[i];
        return res;
    }
    int an = r1[num];
    int bn = -r2[num];
    int lcm = (an*bn)/gcd(an, bn);
    int m1 = lcm/an;
    int m2 = lcm/bn; 
    if(m2 < 0) {
        m2 = -m2;
        m1 = -m1;
    }
    for(int i = 0; i <= n; i++){
        if(m1 != -1 && (r1[i] < LIA_INT_MIN / m1 || r2[i] > LIA_INT_MAX / m1) ) {
            printf("mul overflow7\n");
            free(res);
            exit(-1);
        }
        else if(m1 == -1 && r1[i] == LIA_INT_MIN){
            printf("mul overflow8\n");
            free(res);
            exit(-1);
        }
        if(r2[i] < LIA_INT_MIN / m2 || r2[i] > LIA_INT_MAX / m2) {
            printf("mul overflow9\n");
            free(res);
            exit(-1);
        }
        int x = m2 * r2[i];
        int y = m1 * r1[i];
        if (! check_add_safe(x, y)) {
            printf("add overflow\n");
            free(res);
            exit(-1);
        }
        res[i] = x + y;
    }

    return res;
}

//r1 : a0 + a1*x1 + .. + an-1*xn-1 + an*xn = 0
//r2 : b0 + b1*x1 + .. + bn-1*xn-1 - bn*xn </<= 0
int* equ_eliminate_simplify(int* r1, int* r2, int* value, int size, int int8_max, int int16_max, int int32_max, int int64_max){
    int num = 0;
    //找出编号最大的系数不为0的变元
    for(int i = size; i >= 0; i--){
        if(r1[i] != 0 && i != int8_max && i != int16_max && i != int32_max && i != int64_max){
            num = i;
            value[i] = 0;
            break;
        }
    }
    if(num == 0 && int64_max != -1 && r1[int64_max] != 0) return NULL;
    long long cons = (long long) r1[0];
    //由于系数范围不超过int32，所以下面的计算在极端情况下也不会超过int64的范围
    if(int8_max != -1 && r1[int8_max] != 0) cons = cons + ((long long)r1[int8_max])*((long long)INT8_MAX);
    if(int16_max != -1 && r1[int16_max] != 0) cons = cons + ((long long)r1[int16_max])*((long long)INT16_MAX);
    if(int32_max != -1 && r1[int32_max] != 0) cons = cons + ((long long)r1[int32_max])*((long long)INT32_MAX);
    if(num == 0 && cons != 0) return NULL;
    int* res = (int*)malloc(sizeof(int)*(size+1));
    memset(res, 0, sizeof(int)*(size+1));
    if(num == 0 || r2[num] == 0){
        for(int i = 0; i <= size; i++)
            res[i] = r2[i];
        return res;
    }
   int an = r1[num];
    int bn = -r2[num];
    int lcm = (an*bn)/gcd(an, bn);
    int m1 = lcm/an;
    int m2 = lcm/bn; 
    if(m2 < 0) {
        m2 = -m2;
        m1 = -m1;
    }
    for(int i = 0; i <= size; i++){
        if(m1 != -1 && m1 > 0 && (r1[i] < LIA_INT_MIN / m1 || r1[i] > LIA_INT_MAX / m1) ) {
            printf("mul overflow10\n");
            printf("num:%d, r1[num]:%d, r2[num]:%d\n", num, r1[num], r2[num]);
            printf("lcm : %d, m1:%d, m2:%d, i: %d, r1[i]:%d, r2[i]:%d\n", lcm, m1, m2, i, r1[i], r2[i]);
            exit(-1);
        }
        else if(m1 == -1 && r1[i] == LIA_INT_MIN){
            printf("mul overflow11\n");
            exit(-1);
        }
        if(r2[i] < LIA_INT_MIN / m2 || r2[i] > LIA_INT_MAX / m2) {
            printf("mul overflow12\n");
            exit(-1);
        }
        int x = m2 * r2[i];
        int y = m1 * r1[i];
        if (! check_add_safe(x, y)) {
            printf("add overflow\n");
            free(res);
            exit(-1);
        }
        res[i] = x + y;
    }

    return res;
}



//r1中xn系数为正，r2中xn系数为负, num = n
//r1 : a0 + a1*x1 + .. + an-1*xn-1 + an*xn </<= 0
//r2 : b0 + b1*x1 + .. + bn-1*xn-1 - bn*xn </<= 0
//此时an, bn 均大于0
//生成的新约束 : c0 + c1*x1 + .. + cn-1*xn-1 </<= 0
int* generate_new_constraint(int* r1, int* r2, int num, int cur_num){
    int an = r1[cur_num];
    int bn = -r2[cur_num];
    int g = gcd(an, bn);
    int m1 = bn/g;
    int m2 = an/g;
    int ub1, ub2, lb1, lb2;
    ub1 = LIA_INT_MAX / m1;
    lb1 = LIA_INT_MIN / m1;
    ub2 = LIA_INT_MAX / m2;
    lb2 = LIA_INT_MIN / m2;
    for(int i = 0; i <= num; i++){
        if (r1[i] < lb1 || r1[i] > ub1) {
            printf("mul overflow13\n");
            exit(-1);
        }
        if (r2[i] < lb2 || r2[i] > ub2) {
            printf("mul overflow14\n");
            exit(-1);
        }
    }
    int* res = (int*)malloc(sizeof(int)*(num+1));
    memset(res, 0, sizeof(int)*(num+1));
    for(int i = 0; i <= num; i++){
        //ci = m1*ai + m2*bi
        int x = m2 * r2[i];
        int y = m1 * r1[i];
        if (! check_add_safe(x, y)) {
            printf("add overflow\n");
            free(res);
            exit(-1);
        }
        res[i] = x + y;
    }
    return res;
}

int* dark_generate_new_constraint(int* r1, int* r2, int num){
    int* res = (int*)malloc(sizeof(int)*(num+1));
    memset(res, 0, sizeof(int)*(num+1));
    int an = r1[num];
    int bn = -r2[num]; 
    int lcm = (mul_safe(an,bn))/gcd(an, bn);
    int m1 = lcm/an;
    int m2 = lcm/bn;
    for(int i = 0; i < num; i++){
        //ci = m1*ai + m2*bi
        int x = mul_safe(m2, r2[i]);
        int y = mul_safe(m1, r1[i]);
        res[i] = sign_add_safe(x, y);
    }
    res[0] = sign_add_safe(res[0] , lcm -m1 - m2 + 1);
    return res;
}

//r1和r2都有不存储信息的尾指针
//r1中所有不等式xn系数为正，r2所有不等式中xn系数为负
InequList* generate_new_constraint_list(InequList* r1, InequList* r2, int num, int cur_num){
    if(r1 == NULL || r2 == NULL){
        printf("error in generate_new_constraint_list, should have tail pointer\n");
        exit(-1);
    }
    InequList* res = initInequList();
    if(r1->next == NULL || r2->next == NULL){
        //表明xn是一个unbounded的变元，直接删去其所有相关约束，不需要增加新的约束
        return res;
    }
    InequList* p1 = r1;
    while(p1->next != NULL){
         InequList* p2 = r2;
         while(p2->next != NULL){
            InequList* tmp = initInequList();
            tmp->coef = generate_new_constraint(p1->coef, p2->coef, num, cur_num);
            if(p1->strict == 1 || p2->strict == 1) tmp->strict = 1;
            else tmp->strict = -1;
            tmp->next = res;
            res = tmp;
            p2 = p2->next;
         }
         p1 = p1->next;
    }
    return res;
}


InequList* dark_generate_new_constraint_list(InequList* r1, InequList* r2, int num){
    if(r1 == NULL || r2 == NULL){
        printf("error in generate_new_constraint_list, should have tail pointer\n");
        exit(-1);
    }
    InequList* res = initInequList();
    if(r1->next == NULL || r2->next == NULL){
        //表明xn是一个unbounded的变元，直接删去其所有相关约束，不需要增加新的约束
        return res;
    }
    InequList* p1 = r1;
    while(p1->next != NULL){
         InequList* p2 = r2;
         while(p2->next != NULL){
            InequList* tmp = initInequList();
            tmp->coef = dark_generate_new_constraint(p1->coef, p2->coef, num);
            if(p1->strict == 1 || p2->strict == 1) tmp->strict = 1;
            else tmp->strict = -1;
            tmp->next = res;
            res = tmp;
            p2 = p2->next;
         }
         p1 = p1->next;
    }
    return res;
}

//消去x2,...xn,得到x1的实数域范围
//real shadow没有整数解，原问题必没有，若有整数解，原问题未必有
InequList* real_shadow(InequList* r, int* value, int n, int int8_max, int int16_max, int int32_max, int int64_max){
    int cnt = n;
    #ifdef LIA_THEORY_DEBUG
    printInequlist(r, n);
    #endif
    while(cnt >= 1){
        if(value[cnt] == 0 || cnt == int8_max || cnt == int16_max || cnt == int32_max || cnt == int64_max){
            cnt--;
            continue;
        }
        #ifdef LIA_THEORY_DEBUG
        printf("eliminate x%d\n", cnt);
        #endif
        BoundPair* res = eliminate_xn(r, cnt);
        r = res->remain;
        #ifdef LIA_THEORY_DEBUG
        printf("r after elimate:\n");
        printInequlist(r, n);
        printf("upper bound:\n");
        printInequlist(res->upper, n);
        printf("lower bound:\n");
        printInequlist(res->lower, n);
        #endif
        InequList* new_cons = generate_new_constraint_list(res->upper, res->lower, n, cnt);
        free_InequList(res->upper);
        free_InequList(res->lower);
        #ifdef LIA_THEORY_DEBUG
        printf("new general cons: \n");
        printInequlist(new_cons, n);
        #endif
        InequList* p = r;
        if(p->next == NULL) {
            free(r);
            r = new_cons;
        }
        else {
            while(p->next->next != NULL) p = p->next; //寻找尾指针前一个指针
            free(p->next);
            p->next = new_cons;
        }
        #ifdef LIA_THEORY_DEBUG
        printf("new cons: \n");
        printInequlist(r, n);
        #endif
        cnt--;
    }
    return r;
}

//dark shadow有整数解，原问题必有，若没有整数解，原问题未必没有
InequList* dark_shadow(InequList* r, int n){
    int cnt = n;
    while(cnt > 1){
        BoundPair* res = eliminate_xn(r, cnt);
        InequList* new_cons = dark_generate_new_constraint_list(res->upper, res->lower,cnt);
        InequList* p = r;
        if(p->next == NULL) {
            free(r);
            r = new_cons;
        }
        else {
            while(p->next->next != NULL) p = p->next; //寻找尾指针前一个指针
            free(p->next);
            p->next = new_cons;
        }
        cnt--;
    }
    return r;
}


int lia_theory_deduction(InequList* r1, InequList* r2, int* value, int n, int int8_max, int int16_max, int int32_max, int int64_max){
    #ifdef LIA_THEORY_DEBUG
    printf("lia_theory_deduction:\n");
    #endif
    if(r1->next != NULL){
        r2 = eliminate_equa_constraint(r1, r2, value, n, int8_max, int16_max, int32_max, int64_max);
        if(r2 == NULL) return 0;
    }
    InequList* res = real_shadow(r2, value, n, int8_max, int16_max, int32_max, int64_max);
    if(res == NULL) {
      printf("error in lia theory deduction");
       exit(-1);
    }
    InequList* p = res;
    while(p->next != NULL){
        //只要int64_max系数为正，在不等式系数不超过int32范围的情况下
        // a1*int_max + a2*ll_max + c <= 0 恒不成立
        //若int64_max系数为负，则上式恒成立
        if(int64_max != -1 && p->coef[int64_max] > 0) return 0;
        if(int64_max == -1 || (int64_max != -1 && p->coef[int64_max] == 0)) {
            long long cons = (long long)(p->coef[0]);
            //由于系数范围不超过int32，所以下面的计算在极端情况下也不会超过int64的范围
            if(int8_max != -1 && p->coef[int8_max] != 0) cons = cons + ((long long)(p->coef[int8_max]))*((long long)INT8_MAX);
            if(int16_max != -1 && p->coef[int16_max] != 0) cons = cons + ((long long)(p->coef[int16_max]))*((long long)INT16_MAX);
            if(int32_max != -1 && p->coef[int32_max] != 0) cons = cons + ((long long)(p->coef[int32_max]))*((long long)INT32_MAX);
            if(cons > 0) {
                #ifdef LIA_THEORY_DEBUG
                printf("cons : %lld\n", cons);
                #endif
                return 0;
            }
        }
        p = p->next;
    }
    free_InequList(res);
    return 1;
}






// int main(){

//     InequList* t1 = initInequList_test(3);
//     t1->coef[0] = -5;
//     t1->coef[1] = 2;
//     t1->coef[2] = 1;
//     t1->coef[3] = 2;
//     t1->strict = 0;
//     InequList* t2 = initInequList_test(3);
//     t2->coef[0] = -8;
//     t2->coef[1] = 1;
//     t2->coef[2] = -1;
//     t2->coef[3] = 5;
//     t2->strict = 0;
//     InequList* t3 = initInequList_test(3);
//     t3->coef[0] = 4;
//     t3->coef[1] = -4;
//     t3->coef[2] = -3;
//     t3->coef[3] = 1;
//     t3->strict = 0;
//     t1->next = t2;
//     t2->next = t3;
//     t3->next = initInequList();
//     printInequlist(t1, 3);
//     int* value = (int*)malloc(sizeof(int)*5);
//     for(int i = 0; i < 5; i++) value[i] = 1;
//     InequList* tt1 = initInequList_test(3);
//     tt1->coef[0] = -10;
//     tt1->coef[1] = 2;
//     tt1->coef[2] = -5;
//     tt1->coef[3] = 4;
//     tt1->strict = -1;
//     InequList* tt2 = initInequList_test(3);
//     tt2->coef[0] = -9;
//     tt2->coef[1] = 3;
//     tt2->coef[2] = -6;
//     tt2->coef[3] = 3;
//     tt2->strict = -1;
//     InequList* tt3 = initInequList_test(3);
//     tt3->coef[0] = -7;
//     tt3->coef[1] = -1;
//     tt3->coef[2] = 5;
//     tt3->coef[3] = -2;
//     tt3->strict = -1;
//     InequList* tt4 = initInequList_test(3);
//     tt4->coef[0] = -12;
//     tt4->coef[1] = -3;
//     tt4->coef[2] = 2;
//     tt4->coef[3] = 6;
//     tt4->strict = -1;
//     tt1->next = tt2;
//     tt2->next = tt3;
//     tt3->next = tt4;
//     tt4->next = initInequList();
//     printInequlist(tt1, 3);
//     printf("start\n");
//     InequList* r1 = initInequList();
//     int res = lia_theory_deduction(t1, tt1, value, 3);
//     if(res == 0) printf("unsat\n");
//     if(res == 1) printf("sat\n");
//     return 0;
// }