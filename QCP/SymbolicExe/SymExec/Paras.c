#include "Paras.h"

int asrt_type, test_type, backup, strategy_gen, strategy_backup, loop_inv_iter_times;
int exec_type;
int exec_info;
// asrt_type = 1 : ConAssertion
char * goal_file;
char * proof_auto_file;
char * proof_manual_file;
char * coq_logic_path;
char * coq_prog_path;                                                 // the path to print program in Coq
struct charmapping * strategy_logic_path;
struct StringList * strategy_folder_list;
char * strategy_proof_logic_path;
char * strategy_file_name;
char * strategy_file;
FILE * input_file;
char * input_file_path;
char * input_file_dir;
FILE * output_file;
char * output_file_path;
char * strategy_goal_file;
char * strategy_folder_path;
void * strategyLibInScopes;
struct StringList * all_strategy_libs;
struct StringList * additional_search_path;

// for coq print
FILE *fp_test, *fp_annots, *fp_witness, *fp_sound, *fp_goal, *fp_goal_check, *fp_auto, *fp_manual, *fp_prog;

char * GetFileDir(char * file) {
   int len = strlen(file), l = len - 1;
   while (l >= 0 && file[l] != '/') l--;
   char * ret = malloc(l + 2);
   int i;
   for (i = 0; i <= l; i++)
      ret[i] = file[i];
   ret[i] = '\0';
   return ret;
}