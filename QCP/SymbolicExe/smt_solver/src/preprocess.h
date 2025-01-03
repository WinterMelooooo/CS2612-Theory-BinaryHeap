#ifndef PREPROCESS_H 
#define PREPROCESS_H 1
#include"hashtable.h"
#include "smt_lang.h"
#include"CDCL.h"

typedef struct cnf_list cnf_list;

typedef struct Hash_val{                
	char *name;	
	int num;
}Hash_val;

typedef struct UF_Hash{
    int arg1;
    int arg2;
} UF_Hash;

struct cnf_list{
    int size; //变量数量
    int* clause; //clause[i]存储命题变元的编号
    cnf_list* next;
};

typedef struct{
    Hash_Table* var_table;      //存储变量对应的编号
    Hash_Table* ufun_table;     //存储uf对应的新变量及其编号
    Hash_Table* fun_var_table;  //用来存储函数名是否被声明，value默认为1
    Hash_Table* lia_purify_table;   //存储liaterm对应的新变量及其编号(在purify过程中产生)
    Hash_Table* nia_purify_table;   //存储niaterm对应的新变量及其编号(在purify过程中产生)
    Hash_Table* uf_purify_table;    //存储ufterm对应的新变量及其编号(在purify过程中产生，此时未curryfy), currfy&&flatten生成的也在其中
    Hash_Table* prop_table; //存储命题对应的编号
    SmtProplist* replace_list;
    SmtProplist* uf_purify_list;
    SmtProplist* lia_purify_list;
    SmtProplist* nia_purify_list;
    cnf_list* cnf_res;
    char** var_list;  //存储变量编号对应的变量
    SmtProp** prop_list;  //存储命题变元对应的原子命题
    int int8_max;   //存储INT8_MAX对应的编号
    int int16_max;  //存储INT16_MAX对应的编号
    int int32_max;  //存储INT32_MAX对应的编号
    int int64_max;   //存储INT63_MAX对应的编号
    int prop_cnt; //命题变元数量
    int at_prop_cnt; //原子命题数量
    int var_cnt;
    int var_cnt_uf; //带上uf引入的变量数量
    int ufunc_cnt;  //特指flatten阶段起新名字的uf数量
    int purify_cnt; //特指purify阶段新增变量数量
    int clause_cnt; //转成cnf后clause的数量
} PreData;

Hash_val* initHashVal();

void hash_table_delete_trans(Hash_Table *Hs_Table);
void free_cnf_list(cnf_list* list);
void freePredata(PreData* data);

//初始化预处理数据结构
PreData* initPreData();

//将UF转成字符串用于做hash
//uf是已经purify之后的结果,即其参数只能是variable或者UFterm
char* UFunction_str(UFunction* uf);

//将算术表达式转成字符串用于做hash
//liaTerm是已经purify之后的结果，运算符连接的只能是变量或者常数
char* LiaTerm_str(SmtTerm* t);

//将原子命题转成字符串用于做hash
//仅限于完成预处理（purify，currfy，flatten）之后的原子命题
char* AtomicProp_str(SmtProp* p);

//在purify时，给UFterm起新的变量名，并且在data中增加新的约束，返回新的变量名
//在做uf相关的变量替代(flatten)时，作用类似
// mode = 0 => purify
// mode = 1 => uf_flatten
SmtTerm* new_name_UFterm(SmtTerm* t, PreData* data, int mode);

//在purify时，给Liaterm起新的变量名，并且增加新的约束，返回新的变量名
SmtTerm* new_name_Liaterm(SmtTerm* t, PreData* data);
SmtTerm* new_name_Niaterm(SmtTerm* t, PreData* data);
SmtTerm* term_purify(SmtTerm* t, PreData* data);
SmtProp* prop_purify(SmtProp* p, PreData* data);

SmtTerm* updateSmtTerm(SmtTerm* t, PreData* data, int mode);

//识别出表达式中的非线性乘除
void NiaTermIdentify(SmtTerm* t);
void NiaPropIdentify(SmtProp* p);

SmtTerm* termCurryfy(SmtTerm* t);

//对已经进行curryfy和purify的ufterm做变量替代
SmtTerm* term_replace(SmtTerm* t, PreData* data);

//同时完成curryfy和flatten
SmtProp* prop_currfy_flatten(SmtProp* p, PreData* data);

//除了对prop做curryfy&&flatten以外，还对purify生成的新约束做curryfy&&flatten
SmtProp* currfy_flatten(SmtProp* p, PreData* data);

void init_Varlist_term(SmtTerm* t, PreData* data);
void init_Varlist_prop(SmtProp* p, PreData* data);
void init_Varlist_proplist(SmtProplist* p, PreData* data);
//借助前面三个函数，生成编号与变量的对应列表
void init_Varlist(SmtProp* p, PreData* data);
void printVarlist(PreData* data);
void printVarlist_uf(PreData* data);
//只打印原子命题列表
void printSmtProplist_2(SmtProplist* p);

//把p中所有原子命题加入hashtable
void add_prop2HashTable(SmtProp* p, PreData* data);
void add_proplist2HashTable(SmtProplist* p, PreData* data);

//把p中所有原子命题转换为布尔变元
void init_propvar(SmtProp* p, PreData* data);
void init_propvar_list(SmtProplist* p, PreData* data);

//借助前面四个函数，将所有的原子命题转为布尔变元
void init_proplist(SmtProp* p, PreData* data);

//下面4个函数在完成前序步骤后生成cnf表达式，并且存储在SAT Solver的数据结构中
//生成p3<->(p1 op p2)对应的cnf中的clause, p3<->not p2 (op为 not时， 此时p1缺省为0)
void clause_gen(int p1, int p2, int p3, int op, PreData* data);
int prop2cnf(SmtProp* p, PreData* data);
clause_data* cnf_trans(SmtProp* p, PreData* data);
sat_data* initCDCL(SmtProp* p, PreData* data);

//读入原始命题，完成所有的预备工作，生成提供给SAT solver的数据
sat_data* preprocess(SmtProp* p, PreData* data);
#endif