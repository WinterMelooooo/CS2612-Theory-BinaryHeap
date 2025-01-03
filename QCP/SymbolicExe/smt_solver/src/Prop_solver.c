#include "Prop_solver.h"
#include"smt_solver_proof.h"
#include"smt_proof_checker.h"
// #define PROP_SOLVER_DEBUG 1
// #define PARSER_DEBUG 1
#ifdef PARSER_DEBUG
#include "smt_lang.tab.h"
#include "smt_lang_flex.h"
#include "coq_proofgen.h"
#endif
struct UFunction *Get_True_UF()
{
  struct UFunction *ans = malloc(sizeof(struct UFunction));
  ans->args = NULL;
  ans->name = "True";
  ans->numArgs = 0;
  return ans;
}

struct UFunction *Get_False_UF()
{
  struct UFunction *ans = malloc(sizeof(struct UFunction));
  ans->args = NULL;
  ans->name = "False";
  ans->numArgs = 0;
  return ans;
}

struct SmtProp * SmtProp_list_to_SmtProp(struct SmtProplist *prop_list)
// 该函数会把一个prop list转化为&&链接的Prop
{
    struct SmtProp *ans;
    if (prop_list == NULL || prop_list -> prop == NULL) {
      ans = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, true);
    }
    else {
      ans = newSmtProp(SMTB_PROP, SMTPROP_AND, copy_SmtProp(prop_list -> prop), SmtProp_list_to_SmtProp(prop_list -> next), NULL, NULL, true);
    }
    return ans;
}

int SingleSmtPropCheck(struct SmtProp *source, struct SmtProp *target)
// 这个函数检查source -> target是否成立,如果成立返回0,不成立返回-1,无法判断返回1
{   
    #ifdef PROP_SOLVER_DEBUG
    printf("into check function\n");
    printSmtProp(source);
    #endif
    SmtProp* left = prop_simplify(source);
    SmtProp* right = prop_simplify(target);
    if (left->type == SMTTF_PROP && left->prop.TF == false) return -1;
    if (right->type == SMTTF_PROP && right->prop.TF == false) return -1;
    if (left->type == SMTTF_PROP && right->type == SMTTF_PROP) return 0;
    #ifdef PROP_SOLVER_DEBUG
    printf("target success\n");
    //printSmtProp(lres->p);
    printf("\n");
    #endif
    SmtProp* p1 = newSmtProp(SMTB_PROP, SMTPROP_AND, left, right, NULL, NULL, true);
    
    SmtProp* p2 = newSmtProp(SMTU_PROP, SMTPROP_NOT, newSmtProp(SMTB_PROP, SMTPROP_IMPLY, copy_SmtProp(left), copy_SmtProp(right), NULL, NULL, true) , NULL, NULL, NULL, true);
    
    int res = smt_solver(p1);
    int res1 = smt_solver(p2);
    freeSmtProp(p2);
    freeSmtProp(p1);
    if (res == 0) return -1;
    if (res1 == 0) return 0;
    // if (res1 == -1)
    //   return -1;
    return 1;
}

SMT_PROOF* SingleSmtPropCheck_proof(struct SmtProp *source, struct SmtProp *target)
// 这个函数检查source -> target是否成立,如果成立返回0,不成立返回-1,无法判断返回1
{   
   #ifdef PROP_SOLVER_DEBUG
    printf("into check function\n");
    printf("source\n");
    printSmtProp(source);
    printf("target\n");
    printSmtProp(target);
    #endif
    SmtProp* left = copy_SmtProp(source);
    SmtProp* right = copy_SmtProp(target);
    #ifdef PROP_SOLVER_DEBUG
    printf("target success\n");
    #endif
    SmtProp* p1 = newSmtProp(SMTB_PROP, SMTPROP_AND, left, right, NULL, NULL, true);
    SmtProp* p2 = newSmtProp(SMTU_PROP, SMTPROP_NOT, newSmtProp(SMTB_PROP, SMTPROP_IMPLY, copy_SmtProp(left), copy_SmtProp(right), NULL, NULL, true) , NULL, NULL, NULL, true);
    SMT_PROOF* res = smt_solver_proof(p1);
    printf("check1 res:%d\n", res->ans);
    SMT_PROOF* res1 = smt_solver_proof(p2);
    printf("check2 res:%d\n", res1->ans);
    freeSmtProp(p2);
    freeSmtProp(p1);
    if (res->ans == 0) {
      res->ans = -1;
      freeSmtProof(res1);
      return res;
    }
    if (res1->ans == 0) {
      freeSmtProof(res);
      return res1;
    }
    SMT_PROOF* proof = (SMT_PROOF*)malloc(sizeof(SMT_PROOF));
    memset(proof, 0, sizeof(SMT_PROOF));
    proof->ans = 1;
    return proof;
}

int SmtProp_list_length (struct SmtProplist *target) {
  int count = 0;
  struct SmtProplist *temp = target;
  while (temp) {
    if (temp -> prop) count ++;
    temp = temp -> next;
  }
  return count;
}

void Prop_solver(struct SmtProplist *target, struct SmtProplist *source)
// 该函数依次检查target中的每一项能不能被source推出
{   
   if (target == NULL || target -> prop == NULL) {
      printf("Success\n");
      return ;
   }
   char *s = malloc(SmtProp_list_length(target) * sizeof(char));
   struct SmtProp *source_prop = SmtProp_list_to_SmtProp(source);
   struct SmtProplist *temp = target;
   int result,count;
   count = 0; 
   while (temp && temp -> prop)
   {    
      result = SingleSmtPropCheck(source_prop,temp->prop);
      #ifdef PROP_SOLVER_DEBUG
      printf("res : %d\n",result);
      #endif
      if (result == -1) {
        printf("Fail\n");
        freeSmtProp(source_prop);
        free(s);
        return ;
      }
      else {
        s[count ++] = result == 0 ? 'T' : 'F';
      }
      temp = temp -> next;
   }
   s[count] = '\0';
   printf("%s\n",s);
   freeSmtProp(source_prop);
   free(s);
}

#ifdef PARSER_DEBUG

int main(int argc, char **argv) {
    
	char s[80] = "input.txt";
	if(argc == 2)
	{
		printf("manual decided input file\n");
		strcpy(s,argv[1]);
	}
	 
	FILE *fp; // = the file in.
	fp=fopen(s, "rb");
	if (fp == NULL)
	{
		printf("File %s can't be opened.\n", s);
		exit(1);
	}
	else 
	{
		yyin = fp;
	}

	yyparse();
  extern struct SmtProp* root;

	printf("\n PARSING FINISHED. \n");
  // SmtProp* p = newSmtProp(SMTTF_PROP, 0, NULL, NULL, NULL, NULL, true);
  // SMT_PROOF* proof = SingleSmtPropCheck_proof(p, root);
  SMT_PROOF* proof = smt_solver_proof(root);
  // int res = smt_solver(root);
  // printf("res:%d\n", res);
  //printSmtProof(proof, stdout);

  // SmtTerm* t1 = newSmtTerm(SMT_VarName, 0, 0, "x_14", NULL, NULL, NULL);
  // SmtTerm* t2 = newSmtTerm(SMT_VarName, 0, 0, "x_11", NULL, NULL, NULL);
  // SmtTerm* t3 = newSmtTerm(SMT_VarName, 0, 0, "x_16", NULL, NULL, NULL);
  // SmtTerm* t4 = newSmtTerm(SMT_VarName, 0, 0, "x_17", NULL, NULL, NULL);
  // SmtTerm* t5 = newSmtTerm(SMT_LiaBTerm, LIA_ADD, 0, NULL, NULL, t1, t2);
  // SmtTerm* t6 = newSmtTerm(SMT_LiaBTerm, LIA_ADD, 0, NULL, NULL, t3, t4);
  // SmtTerm* t2 = newSmtTerm(SMT_ConstNum, 0, 1, NULL, NULL, NULL, NULL);
  // SmtTerm* t3 = newSmtTerm(SMT_VarName, 0, 0, "INT_MAX", NULL, NULL, NULL);
  // SmtTerm* t4 = newSmtTerm(SMT_LiaUTerm, LIA_NEG, 0, NULL, NULL, t3, NULL);
  // SmtTerm* t5 = newSmtTerm(SMT_LiaBTerm, LIA_MINUS, 0, NULL, NULL, t4, t2);
  // SmtProp* p1 = newSmtProp(SMTAT_PROP_EQ, SMT_EQ, NULL, NULL, t5, t6, true);
  // int res = SingleSmtPropCheck(root, p1);
  printf("smt ans: %d\n", proof->ans);
  if(proof->ans == 0){
    int res = smt_proof_check_high(root->prop.Unary_prop.prop1, proof);
    printf("res: %d\n", res);
    printSmtProof(proof, stdout);
    printCoqProof(proof, stdout);
  }
  freeSmtProof(proof);
  fclose(fp);
  printf("run success\n");
}

#endif

