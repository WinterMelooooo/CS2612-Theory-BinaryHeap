#define QUOTE(name) #name
#define STR(macro) QUOTE(macro)

#include <stdio.h>

#include "Paras.h"
#include "../compiler/cp.h"
#include "../compiler/ptrans.h"
#include "../compiler/utils.h"
#include "../compiler/parser_driver.h"
#include "../SymExec/Trans/StmtTrans.h"
#include "../SymExec/Trans/AddressabilityTrans.h"
#include "../SymExec/Trans/PropToSmtPropTrans.h"
#include "../SymExec/SymExec/CexprExec.h"
#include "../SymExec/SymExec/StateDef.h"
#include "../SymExec/SymExec/StateMachine.h"
#include "../SymExec/SymExec/WitnessDef/WitnessTrySolve.h"
#include "../SymExec/Automation/AutomationSolver/solver.h"
#include "../SymExec/Automation/AutomationSolver/CustomSolver.h"
#include "../SymExec/Utility/PSstmtPrinter.h"
#include "../SymExec/Utility/InnerAsrtPrinter.h"
#include "../SymExec/Utility/InnerAsrtCollector.h"
#include "../SymExec/Utility/WitnessPrinter.h"
#include "../SymExec/CoqPrint/CoqPartialStmtPrinter.h"
#include "../SymExec/CoqPrint/CoqCStatmentPrinter.h"
#include "../SymExec/CoqPrint/CoqWitnessPrinter.h"
#include "../SymExec/CoqPrint/CoqTheoremPrinter.h"
#include "../SymExec/CoqPrint/CoqInnerAsrtPrinter.h"
#include "../SymExec/CoqPrint/CoqPrintTools.h"
#include "../SymExec/CoqPrint/CoqSacEntailmentPrinter.h"
#include "../SymExec/CoqPrint/CoqSacSoundnessPrinter.h"
#include "../SymExec/Utility/LogicNameManager.h"
#include "../SymExec/Automation/Soundness/SoundnessStrategy.h"

#include <assert.h>

// compiler defined variables
void *scanner;
struct environment env;

extern struct def_list *root;
extern void* (*LocalDeepCopy)(void*);
extern void* (*LocalMerge)(void*, void*);
extern void* (*LocalSubst)(void*, struct ExprVal*, struct ExprVal*);
extern void* (*LocalSubstPolyType)(void*, struct PolyType*, struct PolyType*);
extern void  (*LocalFree)(void *);
extern int exec_outflag;
extern int exec_type;
extern struct StringList * all_strategy_libs;

struct WitnessList * recorded_witness;

// sep solver and smt solver
// defined in WitnessTrySolve
extern struct EntailRetType * (*SepSolver) (struct Assertion * pre, struct Assertion * post,struct StringList *scope, struct environment * env);
extern struct Prop_solver_return * (*PropSolver) (struct PropList *source_prop_list, struct PropList *target_prop_list, struct environment * env);

extern struct func_info *finalize_func_def(struct func_info *f, struct environment *env);

void ProcessArgv(int argc, char *argv[]) {
   // if both --no-logic-path and --coq-logic-path=<path> are included in argv, report an error
   int exist_logic_path = -1;
   // if both --no-strategy-proof-logic-path and --strategy-proof-logic-path=<path> are included in argv, report an error
   int exist_strategy_proof_logic_path = -1;
   input_file_dir = malloc(1);
   input_file_dir[0] = '\0';
#ifdef GOAL_FILE
   goal_file = STR(GOAL_FILE);
#else
   goal_file = NULL;
#endif
#ifdef PROOF_AUTO_FILE
   proof_auto_file = STR(PROOF_AUTO_FILE);
#else
   proof_auto_file = NULL;
#endif
#ifdef PROOF_MANUAL_FILE
   proof_manual_file = STR(PROOF_MANUAL_FILE);
#else
   proof_manual_file = NULL;
#endif
#ifdef COQ_LOGIC_PATH
   coq_logic_path = STR(COQ_LOGIC_PATH);
#else
   coq_logic_path = NULL;
#endif
#ifdef STRATEGY_PROOF_LOGIC_PATH
   strategy_file_name = STR(STRATEGY_FILE_NAME);
#else
   strategy_file = STR(STRATEGY_FILE);
#endif
#ifdef STRATEGY_FOLDER_PATH
   strategy_folder_path = STR(STRATEGY_FOLDER_PATH);
#else
   strategy_folder_path = NULL;
#endif
#ifdef STRATEGY_PROOF_LOGIC_PATH
   strategy_proof_logic_path = STR(STRATEGY_PROOF_LOGIC_PATH);
#else
   strategy_proof_logic_path = NULL;
#endif
   input_file = stdin;
   input_file_path = NULL;
   output_file = stdout;
   output_file_path = NULL;
   test_type = 0;
   strategy_gen = 1;
   backup = 0;
   coq_prog_path = NULL;
   exec_info = 1;
   for (int i = 1; i < argc; ++i) {
      if (strncmp(argv[i], "-s", 2) == 0) {
         ++i;
         if (i >= argc) {
            fprintf(stderr, "Usage: -s <test_type>\n");
            exit(1);
         }
         test_type = atoi(argv[i]);
         if (test_type < 0 || test_type > 5) {
            fprintf(stderr, "test_type should be in [0, 5]\n");
            exit(1);
         }
      }
      if (strncmp(argv[i], "--gen-and-backup", 15) == 0) {
         backup = 1;
      }
      if (strncmp(argv[i], "--conassertion", 13) == 0) {
         asrt_type = 1;
      }
      // --goal-file=<file>
      if (strncmp(argv[i], "--goal-file=", 12) == 0) {
         goal_file = argv[i] + 12;
      }
      // --proof-auto-file=<file>
      if (strncmp(argv[i], "--proof-auto-file=", 18) == 0) {
         proof_auto_file = argv[i] + 18;
      }
      // --proof-manual-file=<file>
      if (strncmp(argv[i], "--proof-manual-file=", 20) == 0) {
         proof_manual_file = argv[i] + 20;
      }
      // --coq-logic-path=<path>
      if (strncmp(argv[i], "--coq-logic-path=", 17) == 0) {
         coq_logic_path = argv[i] + 17;
         if (exist_logic_path == 0) {
            fprintf(stderr, "You can't use --coq-logic-path=<path> together with --no-logic-path\n");
            exit(0);
         }
         exist_logic_path = 1;
      }
      // --strategy-file=<file>
      if (strncmp(argv[i], "--strategy-file=", 16) == 0) {
         strategy_file = argv[i] + 16;
      }
      // --no-logic-path
      if (strncmp(argv[i], "--no-logic-path", 15) == 0) {
         coq_logic_path = NULL;
         if (exist_logic_path == 1) {
            fprintf(stderr, "You can't use --no-logic-path together with --coq-logic-path=<path>\n");
            exit(1);
         }
         exist_logic_path = 0;
      }
      // --no-strategy-gen
      if (strncmp(argv[i], "--no-strategy-gen", 17) == 0) {
         strategy_gen = 0;
      }
      // --input-file=<file>
      if (strncmp(argv[i], "--input-file=", 13) == 0) {
         input_file = fopen(argv[i] + 13, "r");
         input_file_path = argv[i] + 13;
         free(input_file_dir);
         input_file_dir = GetFileDir(input_file_path);
         if (input_file == NULL) {
            fprintf(stderr, "cannot open file %s\n", argv[i] + 13);
            perror("fopen error");
            exit(1);
         }
      }
      // --output-file=<file>
      if (strncmp(argv[i], "--output-file=", 14) == 0) {
         output_file = fopen(argv[i] + 14, "w");
         output_file_path = argv[i] + 14;
         if (output_file == NULL) {
            fprintf(stderr, "cannot open file %s\n", argv[i] + 14);
            perror("fopen error");
            exit(1);
         }
      }
      // --strategy-folder-path=<path>
      if (strncmp(argv[i], "--strategy-folder-path=", 23) == 0) {
         strategy_folder_path = argv[i] + 23;
      }
      // --strategy-proof-logic-path=<path>
      if (strncmp(argv[i], "--strategy-proof-logic-path=", 28) == 0) {
         strategy_proof_logic_path = argv[i] + 28;
         if (exist_strategy_proof_logic_path == 0) {
            fprintf(stderr, "You can't use --strategy-proof-logic-path=<path> together with --no-strategy-proof-logic-path\n");
            exit(1);
         }
         exist_strategy_proof_logic_path = 1;
      }
      // --no-strategy-proof-logic-path
      if (strncmp(argv[i], "--no-strategy-proof-logic-path", 30) == 0) {
         strategy_proof_logic_path = NULL;
         if (exist_strategy_proof_logic_path == 1) {
            fprintf(stderr, "You can't use --no-strategy-proof-logic-path together with --strategy-proof-logic-path=<path>\n");
            exit(1);
         }
         exist_strategy_proof_logic_path = 0;
      }
      // --program-path=<path>
      if (strncmp(argv[i], "--program-path=", 15) == 0) {
         coq_prog_path = argv[i] + 15;
      }
      if (strncmp(argv[i], "--no-exec-info", 14) == 0) {
         exec_info = 0;
      }
   }
}

void dsl_init() {
   all_strategy_libs = StringListNil();
   if (strategy_file != NULL && strcmp(strategy_file,"") != 0) checkDSLFiles(strategy_file);
}

void print_func(void *func_info, struct environment * env) {
  struct func_info *info = func_info;
  print_space();
  print_type(info->ret_type, info->name);
  printf("(");
  struct prog_var_info_list *i;
  for (i = info->param; i != NULL && i->tail != NULL; i = i->tail) {
    print_type(i->head->type, i->head->name);
    printf(", ");
  }
  if (i != NULL)
    print_type(i->head->type, i->head->name);
  printf(")\n");
  if (info->spec != NULL && info->defined) {
    printf("/ **** function spec ****\n");
    nspace += 2;
    print_spec(info->spec, &env->persist);
    nspace -= 2;
    printf(" ****  function spec end  ****/\n");
  }
  if (info->defined) {
    print_space();
    printf("{\n");
    nspace += 2;
    print_cmd(info->body, 1, &env->persist);
    nspace -= 2;
    printf("}\n");
  } else
    printf(";\n");
}

void test_ps_trans(struct func_info *info, struct environment * env) {
   if (info->defined == 0) return;
   struct PartialStmtList * ps_stmt;
   ps_stmt = StmtTrans(info->body, env, 0);
   printf("func %s:\n", info->name);
   struct PartialStmtListNode * i;
   for (i = ps_stmt->head; i != NULL; i = i->next) {
      PrintPartialStmt(i->data, env);
   }
}

struct AsrtTuple *captured_asrt_nbcr;
struct Witness * captured_witness;
struct StateStack * captured_state_machine;
struct AsrtList * captured_inv;
struct PartialStmt *waiting_inv;
struct PartialStmt *prev_stmt;

void exec_func_begin_handler(struct func_info *info, struct environment *env) {
   exec_outflag = exec_info;
   printf("Symbolic Execution into function %s\n", info->name);
   captured_state_machine = StartStateMachineInFunc();
   struct AsrtList * precond;
   WithVarNormalizeName(info->spec->with, env);
   // PrePostAsrtListNormalizeName(info->spec->pre, 1, env);
   // PrePostAsrtListNormalizeName(info->spec->post, 0, env);
   precond = info->spec->pre;
   captured_witness = NewWitness();
   captured_asrt_nbcr = CreateAsrtTuple(ToAddressable(precond, env), AsrtListNil(), AsrtListNil(), FuncRetTypeListNil());
   captured_inv = AsrtListNil();
   if (exec_info) {
      PrintAsrtTuple(captured_asrt_nbcr, env);
   }
   prev_stmt = NULL;
   waiting_inv = NULL;
}

struct AsrtList * exec_partial_statement_handler(struct PartialStmt *pstmt, struct environment *env) {

   if (prev_stmt != NULL) prev_stmt->next = pstmt;

   if (test_type == 3 || exec_info) {
      puts("");
      PrintPartialStmt(pstmt, env);
      puts("");
   }

   if (test_type == 0 || test_type == 4 || test_type == 5) {
      struct SymbolicExecRet exec_ret = StateMachineTransition(pstmt, captured_inv, captured_state_machine, captured_asrt_nbcr, env, NormalTrans);
      captured_asrt_nbcr = exec_ret.asrt;
      captured_state_machine = exec_ret.state_stack;
      captured_inv = exec_ret.inv;
      if (pstmt->t == PS_wi) {
         for (struct func_spec * specs = pstmt->d.PS_wi.specs; specs != NULL; specs = specs->next) {
            struct AsrtList * precond = specs->pre;
            struct AsrtList * postcond = specs->post;
            exec_ret.witness->which_implies_wit = 
               WhichImpliesWitCons(AsrtListDeepCopy(precond), 
                                   AsrtListDeepCopy(postcond), 
                                   pstmt->d.PS_wi.post_scopes,
                                   exec_ret.witness->which_implies_wit);
         }
      }
      if (pstmt->t == PS_return && exec_info) {
         PrintFuncRetType(captured_asrt_nbcr->ret->head, env);
      }
      WitnessTrySolve(exec_ret.witness, env);
      captured_witness = WitnessMerge(exec_ret.witness, captured_witness);
      if (exec_info) {
         PrintAsrtTuple(captured_asrt_nbcr, env);
      }
   }

   prev_stmt = pstmt;
   return captured_asrt_nbcr->nrm;
}

struct ReturnCheckWit * ReturnWitCollect(struct FuncRetTypeList * rets, struct FuncRetType *post) {
   if (rets == NULL) return ReturnCheckWitNil();
   struct FuncRetType * ret = rets->head;
   for (struct FuncRetType * i = ret; i != NULL; i = i->next) {
      i->asrt = ToNonaddressableSingle(i->asrt);
   }
   return ReturnCheckWitCons(ret, FuncRetTypeDeepCopy(post), rets->scopes, ReturnWitCollect(rets->next, post));
}

int SolverSingle(struct Assertion * pre, struct Assertion * post, struct environment * env, struct StringList * scopes) {
  SepSolver(pre, post, scopes, env);
  printf("Res pre after solve\n");
  PrintAsrtFile(pre, env, output_file);
  printf("\n--------------------\n");
  struct RAssertion * pre_ra = cpu_comment(AsrtListCons(pre, NULL),env);
  print_RA_File(output_file,pre_ra);
  free_ra(pre_ra);
  printf("\n====================\n");
  printf("Res post after solve\n");
  PrintAsrtFile(post, env, output_file);
  printf("\n--------------------\n");
  struct RAssertion * post_ra = cpu_comment(AsrtListCons(post, NULL),env);
  print_RA_File(output_file,post_ra);
  free_ra(post_ra);
  printf("\n====================\n");  
  if (post->exist_list != NULL || post->sep_list != NULL || pre->sep_list != 0) return 0;
  struct Prop_solver_return * prop_ret = PropSolver(pre->prop_list, post->prop_list, env);
  AsrtFree(pre);
  AsrtFree(post);
  if (prop_ret->result == 1) {
      return 1;
  } else {
      return 0;
  }
}

void SolveReturnWit(struct ReturnCheckWit * return_checker_wit, struct environment * env) {
#ifdef WITNESS_TRY_SOLVE_DEBUG      
   printf("Try Return Checker Solve\n");
#endif
   struct ReturnCheckWit * tmp = return_checker_wit;
   while (tmp != NULL) {
      tmp->auto_solved = IntListNil();
      for (struct FuncRetType * i = tmp->pre; i != NULL; i = i->next) {
         int solved = 0;
         for (struct FuncRetType * j = tmp->post; j != NULL; j = j->next) {
            struct Assertion * pre = AsrtDeepCopy(i->asrt);
            struct Assertion * post = AsrtDeepCopy(j->asrt);
            if (i->val != NULL) {
               post->exist_list = ExistListRemove(j->val->d.FUNCAPP.id, post->exist_list);
               post = AsrtSubst(post, j->val, i->val);
            }
            if (SolverSingle(pre, post, env, return_checker_wit->strategy_scopes) == 1) {
               solved = 1;
               break;
            }
         }
         if (solved) fprintf(output_file, "Success Entail!\n");
          else fprintf(output_file, "Fail Entail!\n");
      }
      tmp = tmp->next;
   }
}

void exec_func_end_handler(struct func_info *info, struct environment *env) {
   if (test_type == 0 || test_type == 4 || test_type == 5) {
      struct AsrtList * postcond = info->spec->post;
      struct FuncRetType * post = FuncRetTypeNil();
      while (postcond != NULL) {
         post = FuncRetTypeCons(postcond->head, info->spec->__return, post);
         postcond = postcond->next;
      }
      captured_asrt_nbcr = StateMachineFuncEnd(captured_asrt_nbcr, captured_state_machine, env);
      struct ReturnCheckWit * ret_wit = ReturnWitCollect(captured_asrt_nbcr->ret, post);
      SolveReturnWit(ret_wit, env);
   }
}

void exec_handler(struct partial_program *p, struct environment *env) {
   trans(p, env,
         exec_func_begin_handler,
         (void *)exec_partial_statement_handler,
         exec_func_end_handler);
   free_partial_program(p);
}

int main(int argc, char *argv[]) {
   ProcessArgv(argc, argv);
   exec_type = 0;
   dsl_init();
 
   LocalDeepCopy = (void*(*)(void *)) LocalListDeepCopy;
   LocalMerge = (void*(*)(void *, void *)) LocalLinkedHashMapMerge;
   LocalSubst = (void*(*)(void *, struct ExprVal *, struct ExprVal *)) LocalLinkedHashMapSubst;
   LocalSubstPolyType = (void*(*)(void *, struct PolyType *, struct PolyType *)) LocalLinkedHashMapSubstPolyType;
   LocalFree = (void (*)(void *)) LocalLinkedHashMapFree;
   SepSolver = SepLogicEntail;
   PropSolver = PropEntail;
   recorded_witness = WitnessListNil();

   init_env(&env);
   LogicNameManagerInit(&env);
   if (input_file_path == NULL) {
      parse_program(input_file, exec_handler, &env);
   } else {
      parse_program_path(input_file_path, exec_handler, &env);
   }
   
   finiStrategyAll();
   return 0;
}

#undef STR
#undef QUOTE