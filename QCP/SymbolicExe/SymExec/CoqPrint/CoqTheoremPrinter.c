#include "CoqTheoremPrinter.h"
#include "CoqInnerAsrtPrinter.h"

void CoqStateMachineSoundPrinter(int id, FILE * fp) {
   fprintf(fp, "Theorem StateMachine_sound%d :\n", id);
   fprintf(fp, "    State_valid env Funcpred_denote Seppred_denote return_val Pre%d execPost%d (ACstatement_denote env callees return_val ACStatement%d).\n", id, id, id);
   fprintf(fp, "Proof.\n");
   fprintf(fp, "eapply StateMachine_sound.\n");
   fprintf(fp, "apply ACStmt_to_ps_correctness%d.\n",id);
   fprintf(fp, "apply Soundness_of_witness%d.\n",id);
   fprintf(fp, "apply Exec_correctness%d.\n",id);
   fprintf(fp, "Qed.\n");
}