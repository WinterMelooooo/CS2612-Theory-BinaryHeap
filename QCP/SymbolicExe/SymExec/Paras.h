#ifndef PRARAS_H
#define PRARAS_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int asrt_type, test_type, backup, strategy_gen, strategy_backup, loop_inv_iter_times, exec_info;
extern char * goal_file;
extern char * proof_auto_file;
extern char * proof_manual_file;
extern char * coq_logic_path;
extern char * coq_prog_path;                                                 // the path to print program in Coq
extern char * strategy_proof_logic_path;
extern char * strategy_file_name;
extern char * strategy_file;
extern FILE * input_file;
extern char * input_file_path;
extern char * input_file_dir;
extern FILE * output_file;
extern char * output_file_path;
extern char * strategy_goal_file;
extern char * strategy_folder_path;
extern void * strategyLibInScopes;
extern struct StringList * additional_search_path;

// for coq print
extern FILE *fp_test, *fp_annots, *fp_witness, *fp_sound, *fp_goal, *fp_goal_check, *fp_auto, *fp_manual, *fp_prog;

char * GetFileDir(char * file);

#endif
