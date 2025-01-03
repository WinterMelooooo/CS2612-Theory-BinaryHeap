#ifndef COQ_SAC_ENTAILMENT_PRINTER_H
#define COQ_SAC_ENTAILMENT_PRINTER_H

#include "../../compiler/env.h"
#include "../AsrtDef/AssDef.h"
#include "../SymExec/WitnessDef/Witness.h"

FILE * OpenFile(char * path, int backup, int force);

struct RealNameMapping {
   struct hashtbl * id_to_name;
   struct hashtbl * name_to_id;
};

struct RealNameMapping * CreateRealNameMapping();
void RealNameMappingFree(struct RealNameMapping * mapping);
void RealNameMappingAdd(struct RealNameMapping * mapping, char * name, int id);
char * RealNameMappingGetName(struct RealNameMapping * mapping, int id);

char * GetFileNameNoCoqSuffix(char * path);
void CoqPrintDefineModuleType(FILE * fp, char * module_type);
void CoqPrintDefineModule(FILE * fp, char * module_name, char * module_type);
void CoqPrintEndModuleType(FILE * fp, char * module_type);
void CoqPrintEndModule(FILE * fp, char * module_name);
void CoqPrintSacProgHeader(FILE * fp_prog);
void CoqPrintSacGoalHeader(struct environment * env, FILE * fp_goal);
void CoqPrintSacProofHeader(struct environment * env, FILE * fp_unsolved);
void CoqPrintSacProgram(struct environment * env, FILE * fp);
void CoqPrintSacGoalCheck(FILE * fp_goal_check);
void CoqPrintSacWitness(struct Witness * witness, struct environment * env, FILE * fp_goal, FILE * fp_auto, FILE * fp_manual);
void CoqPrintSacWitnessList(struct WitnessList * list, struct environment * env, FILE * fp_goal, FILE * fp_auto, FILE * fp_manual);
void CoqPrintSacAllFuncDerivation(struct environment * env, FILE * fp_goal, FILE * fp_manual);
void CoqPrintSacStrategySoundness(char * path, struct environment * env);
void CoqPrintSacProgram(struct environment * env, FILE * fp);
void CoqPrintSacVCCorrectInit();
void CoqPrintSacVCCorrect(FILE * fp_goal);
// for debug
void DebugPrintRealNameMapping(struct RealNameMapping * mapping, struct environment * env);

#endif // COQ_SAC_ENTAILMENT_PRINTER_H