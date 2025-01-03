#include "SoundnessStrategy.h"

#ifndef FPRINT
#define FPRINT(fp, ...) \
   do { \
      if (fp != NULL) { \
         fprintf(fp, __VA_ARGS__); \
      } \
   } while (0)
#endif

void print_strategy_defs(struct StrategyLibRule * rule, FILE * fp, struct environment * env) {
    FPRINT(fp, "\n");
    if (rule->id >= 0)
        FPRINT(fp, "Definition %s_strategy%d :=\n", rule->filename, rule->id);
    else
        FPRINT(fp, "Definition %s_strategy_post%d :=\n", rule->filename, -rule->id);
    struct RamifiedCondition * rc = gen_rc(rule, env);
    print_rc(fp, rc, rule->type_mapping, env);
    FPRINT(fp, ".\n");
    fini_rc(rc);
}

void print_strategy_lemmas(struct StrategyLibRule * rule, FILE * fp) {
    FPRINT(fp, "\n");
    if (rule->id >= 0)
        FPRINT(fp, "Lemma %s_strategy%d_correctness : %s_strategy%d.\n", rule->filename, rule->id, rule->filename, rule->id);
    else
        FPRINT(fp, "Lemma %s_strategy_post%d_correctness : %s_strategy_post%d.\n", rule->filename, -rule->id, rule->filename, -rule->id);
    print_tabs(1, fp);
    FPRINT(fp, "pre_process_default.\n");
    FPRINT(fp, "Admitted.\n");
}

void print_defs_header(FILE * fp, struct environment * env) {
    FPRINT(fp, "Require Import Coq.ZArith.ZArith.\n");
    FPRINT(fp, "Require Import Coq.Bool.Bool.\n");
    FPRINT(fp, "Require Import Coq.Lists.List.\n");
    FPRINT(fp, "Require Import Coq.Strings.String.\n");
    FPRINT(fp, "Require Import Coq.micromega.Psatz.\n");
    FPRINT(fp, "From SimpleC.SL Require Import SeparationLogic.\n");
    dump_coq_module(&env->persist, fp);
    FPRINT(fp, "Local Open Scope Z_scope.\n");
    FPRINT(fp, "Local Open Scope sac.\n");
    FPRINT(fp, "Local Open Scope string.\n");
}

void print_proofs_header(FILE * fp, char * filename, struct environment * env) {
    FPRINT(fp, "Require Import Coq.ZArith.ZArith.\n");
    FPRINT(fp, "Require Import Coq.Bool.Bool.\n");
    FPRINT(fp, "Require Import Coq.Lists.List.\n");
    FPRINT(fp, "Require Import Coq.Strings.String.\n");
    FPRINT(fp, "Require Import Coq.micromega.Psatz.\n");
    FPRINT(fp, "From SimpleC.SL Require Import SeparationLogic.\n");
    if (coq_logic_path != NULL) FPRINT(fp, "From %s ", coq_logic_path);
    FPRINT(fp, "Require Import %s_strategy_goal.\n", filename);
    dump_coq_module(&env->persist, fp);
    FPRINT(fp, "Local Open Scope Z_scope.\n");
    FPRINT(fp, "Local Open Scope sac.\n");
    FPRINT(fp, "Local Open Scope string.\n");
}

void print_check_header(FILE * fp, char * filename) {
//     Require Import dll_queue_goal dll_queue_proof_auto dll_queue_proof_manual.

// Module VC_Correctness : VC_Correct.
//   Include dll_queue_proof_auto.
//   Include dll_queue_proof_manual.
// End VC_Correctness.
    if (coq_logic_path != NULL) FPRINT(fp, "From %s ", coq_logic_path);
    FPRINT(fp, "Require Import %s_strategy_goal %s_strategy_proof.\n\n", filename, filename);
    FPRINT(fp, "Module %s_Strategy_Correctness : %s_Strategy_Correct.\n", filename, filename);
    FPRINT(fp, "  Include %s_strategy_proof.\n", filename);
    FPRINT(fp, "End %s_Strategy_Correctness.\n", filename);
}

void print_strategy_soundness(struct StrategyLib * lib, FILE * defs_fp, FILE * proofs_fp, FILE * check_fp, char * filename, struct environment * env) {
    if (defs_fp != NULL) print_defs_header(defs_fp, env);
    if (proofs_fp != NULL) print_proofs_header(proofs_fp, filename, env);
    if (check_fp != NULL) print_check_header(check_fp, filename);
    for (int i = 0; i < STRATEGY_LIB_MAX_PRIORITY; i++)
        for (struct StrategyLibRuleList * cur = lib->rules[i]->head; cur != NULL; cur = cur->next) {
            if (defs_fp != NULL) print_strategy_defs(cur->rule, defs_fp, env);
            if (proofs_fp != NULL) print_strategy_lemmas(cur->rule, proofs_fp);
        }
    if (defs_fp != NULL) FPRINT(defs_fp, "\nModule Type %s_Strategy_Correct.\n\n", filename);
    for (int i = 0; i < STRATEGY_LIB_MAX_PRIORITY; i++)
        for (struct StrategyLibRuleList * cur = lib->rules[i]->head; cur != NULL; cur = cur->next) {
            if (cur->rule->id >= 0)
                if (defs_fp != NULL) FPRINT(defs_fp, "  Axiom %s_strategy%d_correctness : %s_strategy%d.\n", cur->rule->filename, cur->rule->id, cur->rule->filename, cur->rule->id);
            else
                if (defs_fp != NULL) FPRINT(defs_fp, "  Axiom %s_strategy_post%d_correctness : %s_strategy_post%d.\n", cur->rule->filename, -cur->rule->id, cur->rule->filename, -cur->rule->id);
        }
    if (defs_fp != NULL) FPRINT(defs_fp, "\nEnd %s_Strategy_Correct.\n", filename);
}