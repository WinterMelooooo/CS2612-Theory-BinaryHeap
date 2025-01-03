#include <assert.h>
#include "../Paras.h"
#include "../Automation/Util/Config.h"
#include "../Automation/StrategyLibDef/StrategyLib.h"
#include "../Automation/Soundness/SoundnessStrategy.h"
#include "../Automation/dsl_match/ASTtoLibRule.h"
#include "../Automation/Mapping/CharMapping.h"
#include "../Utility/List.h"
#include "CoqSacEntailmentPrinter.h"
#include "../Utility/InnerAsrtPrinter.h"
#include "../Utility/CexprPrinter.h"
#include "../Utility/List.h"
#include "../../compiler/env.h"
#include "../../compiler/cp.h"
#include "../SymExec/WitnessDef/WitnessTrySolve.h"

#define OPEN_FILE_WRITE(fp, path) \
   do { \
      (fp) = fopen((path), "w"); \
      if ((fp) == NULL) { \
         printf("cannot open file %s\n", (path)); \
         perror("fopen error"); \
         exit(1); \
      } \
   } while (0);

#ifndef FPRINT
#define FPRINT(fp, ...) \
   do { \
      if (fp != NULL) { \
         fprintf(fp, __VA_ARGS__); \
      } \
   } while (0)
#endif

char * func_name;
int entailment_wit_cnt;
int return_wit_cnt;
int which_implies_wit_cnt;
int safety_wit_cnt;
int partial_solve_wit_cnt;
struct StringList *all_proof_goals;
extern struct StringList *all_strategy_libs;
extern struct charMapping *strategy_logic_path;

extern struct PolyType *cpa_type_of(struct atype *ty);
extern struct atype * cpu_type_of(struct PolyType *ty, struct environment *env);

extern int cast_void(void *p);
extern void * cast_int(int p);

int LengthOfInt(int n) {
   if (n == 0) return 1;
   int len = 0;
   while (n > 0) {
      n /= 10;
      ++len;
   }
   return len;
}

char * StrCopy(char * str) {
   char * ret = (char *)malloc(strlen(str) + 1);
   strcpy(ret, str);
   return ret;
}

// If backup == 1, create a backup file if object file exists.
// If backup == 0 and object file exists
//   report an warning if force == 0
//   overwrite if force == 1
FILE * OpenFile(char * path, int backup, int force) {
   if (backup) {
      // if file not exist, return the file
      FILE * fp = fopen(path, "r");
      if (fp == NULL) {
         OPEN_FILE_WRITE(fp, path);
         return fp;
      }
      

      // if file exist, create a backup file
      char * path_no_v;
      path_no_v = (char *) malloc(strlen(path) + 1);
      strcpy(path_no_v, path);
      path_no_v[strlen(path_no_v) - 2] = '\0';

      char * backup_path;
      backup_path = (char *) malloc(strlen(path_no_v) + 20);
      int i = 1;
      while (1) {
         sprintf(backup_path, "%s_backup%d.v", path_no_v, i);
         FILE * fp_backup = fopen(backup_path, "r");
         if (fp_backup == NULL) {
            break;
         }
         fclose(fp_backup);
         ++i;
      }
      FILE * fp_backup;
      OPEN_FILE_WRITE(fp_backup, backup_path);

      // copy the content of the file to the backup file
      char c;
      while ((c = fgetc(fp)) != EOF) {
         fputc(c, fp_backup);
      }
      fclose(fp);
      fclose(fp_backup);
      free(path_no_v);
      free(backup_path);

      // open the file and clear the content
      OPEN_FILE_WRITE(fp, path);
      return fp;
   } else {
      FILE * fp;
      if (force == 0) {
         fp = fopen(path, "r");
         if (fp == NULL) {
            OPEN_FILE_WRITE(fp, path);
         } else {
            fp = NULL;
         } 
      } else {
         OPEN_FILE_WRITE(fp, path);
      }
      return fp;
   }
}

struct RealNameMapping * CreateRealNameMapping() {
   struct RealNameMapping * mapping = (struct RealNameMapping *) malloc(sizeof(struct RealNameMapping));
   mapping->id_to_name = create_hashtbl(hash_int, int_equal);
   mapping->name_to_id = create_hashtbl(hash_string, string_equal);
   return mapping;
}

void RealNameMappingFree(struct RealNameMapping * mapping) {
   free_hashtbl(mapping->id_to_name);
   free_hashtbl(mapping->name_to_id);
   free(mapping);
}

void RealNameMappingAdd(struct RealNameMapping * mapping, char * name, int id) {
   int valid;
   hashtbl_find(mapping->id_to_name, cast_int(id), (void *)&valid); 
   if (valid) return;
   hashtbl_find(mapping->name_to_id, (void *)name, (void *)&valid);
   if (!valid) {
      hashtbl_add(mapping->name_to_id, (void *)name, cast_int(id));
      hashtbl_add(mapping->id_to_name, cast_int(id), (void *)StrCopy(name));
   } else {
      int repeated_id = 2;
      while (1) {
         char * new_name = (char *)malloc(strlen(name) + LengthOfInt(repeated_id) + 2);
         sprintf(new_name, "%s_%d", name, repeated_id);
         hashtbl_find(mapping->name_to_id, (void *)new_name, (void *)&valid);
         if (!valid) {
            hashtbl_add(mapping->name_to_id, (void *)new_name, cast_int(id));
            hashtbl_add(mapping->id_to_name, cast_int(id), (void *)StrCopy(new_name));
            break;
         }
         free(new_name);
         ++repeated_id;
      }
      free(name);
   }
}

char * RealNameMappingGetName(struct RealNameMapping * mapping, int id) {
   char * name;
   int valid;
   name = hashtbl_find(mapping->id_to_name, cast_int(id), (void *)&valid);
   return name;
}

void RealNameMappingMerge(struct RealNameMapping * mapping1, struct RealNameMapping * mapping2) {
   for (struct blist * i = mapping2->id_to_name->top; i != NULL; i = i->down) {
      int id = cast_void(i->key);
      char * name = i->val;
      int valid;
      hashtbl_find(mapping1->id_to_name, cast_int(id), (void *)&valid);
      if (!valid) {
         RealNameMappingAdd(mapping1, StrCopy(name), id);
      }
   }
}

void CoqPrintSacImport(struct environment * env, FILE * fp) {
   dump_coq_module(&env->persist, fp);
}

static char * getFileName(char * file) {
    int len = strlen(file), l = len - 1;
    while (l >= 0 && file[l] != '/') l--;
    ++l;
    int r = l;
    while (r < len && file[r] != '.') r++;
    char * ret = malloc(r - l + 1);
    int i, j;
    for (i = 0, j = l; j < r; i++, j++)
        ret[i] = file[j];
    ret[i] = '\0';
    return ret;
}

void CoqPrintSacProgHeader(FILE * fp) {
   FPRINT(fp, "Require Import Coq.ZArith.ZArith.\n");
   FPRINT(fp, "Require Import Coq.Bool.Bool.\n");
   FPRINT(fp, "Require Import Coq.Strings.String.\n");
   FPRINT(fp, "Require Import Coq.Lists.List.\n");
   FPRINT(fp, "Require Import Coq.Classes.RelationClasses.\n");
   FPRINT(fp, "Require Import Coq.Classes.Morphisms.\n");
   FPRINT(fp, "Require Import Coq.micromega.Psatz.\n");
   FPRINT(fp, "Require Import Coq.Sorting.Permutation.\n");
   FPRINT(fp, "From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.\n");
   FPRINT(fp, "Require Import SetsClass.SetsClass. Import SetsNotation.\n");
   FPRINT(fp, "From SimpleC.SL Require Import Mem SeparationLogic.\n");
   FPRINT(fp, "Require Import Logic.LogicGenerator.demo932.Interface.\n");
   FPRINT(fp, "Local Open Scope Z_scope.\n");
   FPRINT(fp, "Local Open Scope sets.\n");
   FPRINT(fp, "Local Open Scope string.\n");
   FPRINT(fp, "Local Open Scope list.\n");
   FPRINT(fp, "\n");
}

void CoqPrintSacGoalHeader(struct environment * env, FILE * fp) {
   FPRINT(fp, "Require Import Coq.ZArith.ZArith.\n");
   FPRINT(fp, "Require Import Coq.Bool.Bool.\n");
   FPRINT(fp, "Require Import Coq.Strings.String.\n");
   FPRINT(fp, "Require Import Coq.Lists.List.\n");
   FPRINT(fp, "Require Import Coq.Classes.RelationClasses.\n");
   FPRINT(fp, "Require Import Coq.Classes.Morphisms.\n");
   FPRINT(fp, "Require Import Coq.micromega.Psatz.\n");
   FPRINT(fp, "Require Import Coq.Sorting.Permutation.\n");
   FPRINT(fp, "From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.\n");
   FPRINT(fp, "Require Import SetsClass.SetsClass. Import SetsNotation.\n");
   FPRINT(fp, "From SimpleC.SL Require Import Mem SeparationLogic.\n");
   FPRINT(fp, "Require Import Logic.LogicGenerator.demo932.Interface.\n");
   FPRINT(fp, "Local Open Scope Z_scope.\n");
   FPRINT(fp, "Local Open Scope sets.\n");
   FPRINT(fp, "Local Open Scope string.\n");
   FPRINT(fp, "Local Open Scope list.\n");
   CoqPrintSacImport(env, fp);
   FPRINT(fp, "Local Open Scope sac.\n");
   if (strategy_gen) {
      for (struct StringListNode * i = all_strategy_libs->head; i != NULL; i = i->next) {
         char *file_name = getFileName(i->data);
         char *dir_name = GetFileDir(i->data);
         struct mappingValue *res = charMappingFind(dir_name, strategy_logic_path);
         if (res == NULL) {
            FPRINT(fp, "Require Import %s_strategy_goal.\n", file_name);
            FPRINT(fp, "Require Import %s_strategy_proof.\n", file_name);
         } else {
            char* lp = (char*) res->val;
            FPRINT(fp, "From %s Require Import %s_strategy_goal.\n", lp, file_name);
            FPRINT(fp, "From %s Require Import %s_strategy_proof.\n", lp, file_name);
         }
         free(file_name);
         free(dir_name);
      }
      finiCharMapping(strategy_logic_path);
      strategy_logic_path = NULL;
   }
   FPRINT(fp, "\n");
}

char * GetFileNameNoCoqSuffix(char * path) {
   char * tmp = strrchr(path, '/');
   tmp = tmp == NULL ? path : tmp + 1;
   char * file_name_no_suffix = (char *)malloc(strlen(tmp) + 1);
   strcpy(file_name_no_suffix, tmp);
   file_name_no_suffix[strlen(tmp) - 2] = '\0';
   return file_name_no_suffix;
}

void CoqPrintDefineModuleType(FILE * fp, char * module_type) {
   FPRINT(fp, "Module Type %s.\n\n", module_type);
}

void CoqPrintDefineModule(FILE * fp, char * module_name, char * module_type) {
   if (module_type == NULL) {
      FPRINT(fp, "Module %s.\n", module_name);
   } else {
      FPRINT(fp, "Module %s : %s.\n", module_name, module_type);
   }
   FPRINT(fp, "\n");
}

void CoqPrintEndModuleType(FILE * fp, char * module_type) {
   FPRINT(fp, "End %s.\n", module_type);
}

void CoqPrintEndModule(FILE * fp, char * module_name) {
   FPRINT(fp, "End %s.\n", module_name);
}

void CoqPrintSacProofHeader(struct environment * env, FILE * fp) {
   FPRINT(fp, "Require Import Coq.ZArith.ZArith.\n");
   FPRINT(fp, "Require Import Coq.Bool.Bool.\n");
   FPRINT(fp, "Require Import Coq.Strings.String.\n");
   FPRINT(fp, "Require Import Coq.Lists.List.\n");
   FPRINT(fp, "Require Import Coq.Classes.RelationClasses.\n");
   FPRINT(fp, "Require Import Coq.Classes.Morphisms.\n");
   FPRINT(fp, "Require Import Coq.micromega.Psatz.\n");
   FPRINT(fp, "Require Import Coq.Sorting.Permutation.\n");
   FPRINT(fp, "From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap.\n");
   FPRINT(fp, "Require Import SetsClass.SetsClass. Import SetsNotation.\n");
   FPRINT(fp, "From SimpleC.SL Require Import Mem SeparationLogic.\n");
   // goal_file: .../goal_file_name.v
   char * goal_file_name = GetFileNameNoCoqSuffix(goal_file);
   if (coq_logic_path == NULL) {
      FPRINT(fp, "Require Import %s.\n", goal_file_name);
   } else {
      FPRINT(fp, "From %s Require Import %s.\n", coq_logic_path, goal_file_name);
   }
   free(goal_file_name);
   FPRINT(fp, "Require Import Logic.LogicGenerator.demo932.Interface.\n");
   FPRINT(fp, "Local Open Scope Z_scope.\n");
   FPRINT(fp, "Local Open Scope sets.\n");
   FPRINT(fp, "Local Open Scope string.\n");
   FPRINT(fp, "Local Open Scope list.\n");
   CoqPrintSacImport(env, fp);
   FPRINT(fp, "Local Open Scope sac.\n");
   FPRINT(fp, "\n");
}

void CoqPrintSacGoalCheck(FILE * fp_goal_check) {
   char * goal_file_name = GetFileNameNoCoqSuffix(goal_file);
   char * proof_auto_name = GetFileNameNoCoqSuffix(proof_auto_file);
   char * proof_manual_name = GetFileNameNoCoqSuffix(proof_manual_file);
   if (coq_logic_path != NULL) {
      FPRINT(fp_goal_check, "From %s ", coq_logic_path);
   }
   FPRINT(fp_goal_check, "Require Import %s %s %s.\n", goal_file_name, proof_auto_name, proof_manual_name);
   FPRINT(fp_goal_check, "\n");
   FPRINT(fp_goal_check, "Module VC_Correctness : VC_Correct.\n");
   if (strategy_gen) {
      for (struct StringListNode * i = all_strategy_libs->head; i != NULL; i = i->next) {
         char * name = getFileName(i->data);
         FPRINT(fp_goal_check, "  Include %s_strategy_proof.\n", name);
         free(name);
      }
   }
   FPRINT(fp_goal_check, "  Include %s.\n", proof_auto_name);
   FPRINT(fp_goal_check, "  Include %s.\n", proof_manual_name);
   FPRINT(fp_goal_check, "End VC_Correctness.\n");
   free(goal_file_name);
   free(proof_auto_name);
   free(proof_manual_name);
}

void AsrtEliminateEqual(struct Assertion * asrt) {
   struct PropList * it = asrt->prop_list;
   while (it != NULL) {
      struct PropList * tmp = it->next;
      if (it->head->t == T_PROP_COMPARE) {
         if (it->head->d.COMPARE.op == PROP_EQ) {
            if (ExprValCheckEqual(it->head->d.COMPARE.expr1, it->head->d.COMPARE.expr2)) {
               asrt->prop_list = PropListRemove(it, asrt->prop_list);
            }
         }
      }
      it = tmp;
   }
}

void AsrtListEliminateEqual(struct AsrtList * asrt_list) {
   struct AsrtList * it = asrt_list;
   while (it != NULL) {
      AsrtEliminateEqual(it->head);
      it = it->next;
   }
}

struct ExistList * ExprValListCollectAllVars(struct ExprValList * expr_list, struct environment * env);

struct ExistList * ExprValCollectAllVars(struct ExprVal * expr, struct environment * env) {
   if (expr == NULL) return ExistListNil();
   struct ExistList * ans;
   switch (expr->t) {
      case EZ_VAL:
         ans = ExistListNil();
         break;
      case VFIELD_ADDRESS:
         ans = ExprValCollectAllVars(expr->d.VFIELD_ADDRESS.expr, env);
         break;
      case VUOP:
         ans = ExprValCollectAllVars(expr->d.VUOP.expr, env);
         break;
      case VBOP:
         ans = ExistListLink(ExprValCollectAllVars(expr->d.VBOP.expr1, env), ExprValCollectAllVars(expr->d.VBOP.expr2, env));
         break;
      case FUNCAPP: {
          struct logic_var_info * var_info = find_logic_var_by_id(expr->d.FUNCAPP.id, &env->persist);
          if (var_info->category != LOGIC_EXTERN && var_info->category != LOGIC_PROJ) {
              ans = ExistListCons(expr->d.FUNCAPP.id, ExprValListCollectAllVars(expr->d.FUNCAPP.args, env));
          } else {
              ans = ExprValListCollectAllVars(expr->d.FUNCAPP.args, env);
          }
          break;
      }
      case LINDEX:
         ans = ExistListLink(ExprValCollectAllVars(expr->d.LINDEX.list, env), ExprValCollectAllVars(expr->d.LINDEX.index, env));
         break;
      case SIZE_OF:
         ans = ExistListNil();
         break;
      default:
         FPRINT(stderr, "unsupported at %s %d\n", __FILE__, __LINE__);
         exit(1);
         break;
   }
   return ExistListUnique(ans);
}

struct ExistList * ExprValListCollectAllVars(struct ExprValList * expr_list, struct environment * env) {
   struct ExistList * ans = ExistListNil();
   struct ExprValListNode * node;
   for (node = expr_list->head; node != NULL; node = node->next) {
      ans = ExistListLink(ans, ExprValCollectAllVars(node->data, env));
   }
   return ExistListUnique(ans);
}

struct ExistList * PropCollectAllVars(struct Proposition * prop, struct environment * env) {
   if (prop == NULL) return ExistListNil();
   struct ExistList * ans;
   switch (prop->t) {
      case T_PROP_TRUE:
         ans = ExistListNil();
         break;
      case T_PROP_FALSE:
         ans = ExistListNil();
         break;
      case T_PROP_UNARY:
         ans = PropCollectAllVars(prop->d.UNARY.prop, env);
         break;
      case T_PROP_BINARY:
         ans = ExistListLink(PropCollectAllVars(prop->d.BINARY.prop1, env), PropCollectAllVars(prop->d.BINARY.prop2, env));
         break;
      case T_PROP_PTR:
         ans = ExprValCollectAllVars(prop->d.PTR.expr, env);
         break;
      case T_PROP_COMPARE:
         ans = ExistListLink(ExprValCollectAllVars(prop->d.COMPARE.expr1, env), ExprValCollectAllVars(prop->d.COMPARE.expr2, env));
         break;
      case T_PROP_QUANTIFIER:
         ans = PropCollectAllVars(prop->d.QUANTIFIER.prop, env);
         break;
      case T_PROP_OTHER: {
          struct logic_var_info * var_info = find_logic_var_by_id(prop->d.OTHER.predicate, &env->persist);
          if (var_info->category != LOGIC_EXTERN) {
              ans = ExistListCons(prop->d.OTHER.predicate, ExprValListCollectAllVars(prop->d.OTHER.args, env));
          } else {
              ans = ExprValListCollectAllVars(prop->d.OTHER.args, env);
          }
          break;
      }
   }
   return ExistListUnique(ans);
}

struct ExistList * PropListCollectAllVars(struct PropList * prop_list, struct environment * env) {
   struct ExistList * ans = ExistListNil();
   while (prop_list != NULL) {
      ans = ExistListLink(ans, PropCollectAllVars(prop_list->head, env));
      prop_list = prop_list->next;
   }
   return ExistListUnique(ans);
}

struct ExistList * SepCollectAllVars(struct Separation * sep, struct environment * env) {
   if (sep == NULL) return ExistListNil();
   struct ExistList * ans;
   switch (sep->t) {
      case T_DATA_AT:
         ans = ExistListLink(ExprValCollectAllVars(sep->d.DATA_AT.left, env), ExprValCollectAllVars(sep->d.DATA_AT.right, env));
         break;
      case T_UNDEF_DATA_AT:
         ans = ExprValCollectAllVars(sep->d.UNDEF_DATA_AT.left, env);
         break;
      case T_ARR:
         ans = ExistListLink(ExprValCollectAllVars(sep->d.ARR.addr, env), ExprValCollectAllVars(sep->d.ARR.value, env));
         break;
      case T_OTHER: {
          struct logic_var_info * var_info = find_logic_var_by_id(sep->d.OTHER.sep_id, &env->persist);
          if (var_info->category != LOGIC_EXTERN) {
              ans = ExistListCons(sep->d.OTHER.sep_id, ExprValListCollectAllVars(sep->d.OTHER.exprs, env));
          } else {
              ans = ExprValListCollectAllVars(sep->d.OTHER.exprs, env);
          }
          break;
      }
   }
   return ExistListUnique(ans);
}

struct ExistList * SepListCollectAllVars(struct SepList * sep_list, struct environment * env) {
   struct ExistList * ans = ExistListNil();
   while (sep_list != NULL) {
      ans = ExistListLink(ans, SepCollectAllVars(sep_list->head, env));
      sep_list = sep_list->next;
   }
   return ExistListUnique(ans);
}

struct ExistList * CollectAllVars(struct Assertion * asrt, struct environment * env) {
   struct ExistList * ans = ExistListNil();
   ans = ExistListLink(ans, PropListCollectAllVars(asrt->prop_list, env));
   ans = ExistListLink(ans, SepListCollectAllVars(asrt->sep_list, env));
   ans = ExistListUnique(ans);
   return ans;   
}

struct ExistList * CollectFreeVars(struct Assertion * asrt, struct environment * env) {
   struct ExistList * ans = CollectAllVars(asrt, env);
   struct ExistList * i;
  //  printf("Get All Vars : %c", ans == NULL ? '\n' : ' ');
  //  for (i = ans; i != NULL; i = i->next)
  //  {
  //    printf("%d%c", i->id, i->next == NULL ? '\n' : ' ');
  //  }
   for (i = asrt->exist_list; i != NULL; i = i->next) {
      ans = ExistListRemove(i->id, ans);
   }
   return ans;
}

struct ExistList * AsrtListCollectFreeVars(struct AsrtList * asrt, struct environment * env) {
   struct ExistList * ans = ExistListNil();
   for (struct AsrtList * i = asrt; i != NULL; i = i->next) {
      ans = ExistListLink(ans, CollectFreeVars(i->head, env));
   }
   return ExistListUnique(ans);
}

struct StringList * CollectDefaultTypeVar(struct ExprVal * expr, struct environment * env) {
  if (expr == NULL) return StringListNil();
  switch (expr -> t) {
    case FUNCAPP: {

    }
    case LINDEX: {
      return CollectDefaultTypeVar(expr->d.LINDEX.list, env);
    }
    default: {
      FPRINT(stderr, "unsupported array type at %s %d\n", __FILE__, __LINE__);
      exit(1);
      break;
    }
  }
}

struct StringList * CollectDefaultTypeVarsExprList(struct ExprValList * expr, struct environment * env);

struct StringList * CollectDefaultTypeVarsExpr(struct ExprVal * expr, struct environment * env) {
  if (expr == NULL) return StringListNil();
  struct StringList * ans;
  switch (expr->t) {
      case EZ_VAL:
         ans = StringListNil();
         break;
      case VFIELD_ADDRESS:
         ans = CollectDefaultTypeVarsExpr(expr->d.VFIELD_ADDRESS.expr, env);
         break;
      case VUOP:
         ans = CollectDefaultTypeVarsExpr(expr->d.VUOP.expr, env);
         break;
      case VBOP:
         ans = StringListLink(CollectDefaultTypeVarsExpr(expr->d.VBOP.expr1, env), CollectDefaultTypeVarsExpr(expr->d.VBOP.expr2, env));
         break;
      case FUNCAPP:
         ans = CollectDefaultTypeVarsExprList(expr->d.FUNCAPP.args, env);
         break;
      case LINDEX:
         ans = StringListLink(CollectDefaultTypeVarsExpr(expr->d.LINDEX.list, env), CollectDefaultTypeVarsExpr(expr->d.LINDEX.index, env));
         char * type = Get_atype_name(InnerExprInfer(expr->d.LINDEX.list, env));
         if (type == NULL || strncmp(type, "_List_", 6) != 0) {
            fprintf(stderr, "The array ");
            PrintExprValFile(expr->d.LINDEX.list, env, stderr);
            fprintf(stderr, " of Znth is not a list type.\n");
            fprintf(stderr, "The type is %s\n", type);
            exit(1);
         }
         if (strncmp(type + 6, "Z", 1)) {
          ans = StringListLink(ans, StringListCons(strdup(type+6), StringListNil()));   
         }
         free(type);
         break;
      case SIZE_OF:
         ans = StringListNil();
         break;
      default:
         FPRINT(stderr, "unsupported expr for type var collect.\n");
         FPRINT(stderr, "the expr is: \n");
         PrintExprValFile(expr, env, stderr);
         FPRINT(stderr, "the type is: %d\n", expr->t);
         exit(1);
         break;
   }
   return StringListUnique(ans);
}

struct StringList * CollectDefaultTypeVarsExprList(struct ExprValList * expr, struct environment * env) {
   struct StringList * ans = StringListNil();
   struct ExprValListNode * node;
   for (node = expr->head; node != NULL; node = node->next) {
      ans = StringListLink(ans, CollectDefaultTypeVarsExpr(node->data, env));
   }
   return StringListUnique(ans);
}

struct StringList * CollectDefaultTypeVarsProp(struct Proposition * prop, struct environment * env) {
  if (prop == NULL) return StringListNil();
  struct StringList * ans;
  switch (prop->t) {
      case T_PROP_TRUE:
         ans = StringListNil();
         break;
      case T_PROP_FALSE:
         ans = StringListNil();
         break;
      case T_PROP_UNARY:
         ans = CollectDefaultTypeVarsProp(prop->d.UNARY.prop, env);
         break;
      case T_PROP_BINARY:
         ans = StringListLink(CollectDefaultTypeVarsProp(prop->d.BINARY.prop1, env), CollectDefaultTypeVarsProp(prop->d.BINARY.prop2, env));
         break;
      case T_PROP_PTR:
         ans = CollectDefaultTypeVarsExpr(prop->d.PTR.expr, env);
         break;
      case T_PROP_COMPARE:
         ans = StringListLink(CollectDefaultTypeVarsExpr(prop->d.COMPARE.expr1, env), CollectDefaultTypeVarsExpr(prop->d.COMPARE.expr2, env));
         break;
      case T_PROP_QUANTIFIER:
         ans = CollectDefaultTypeVarsProp(prop->d.QUANTIFIER.prop, env);
         break;
      case T_PROP_OTHER:
         ans = CollectDefaultTypeVarsExprList(prop->d.OTHER.args, env);
         break;
   }
   return StringListUnique(ans);
}

struct StringList * CollectDefaultTypeVarsPropList(struct PropList * prop_list, struct environment * env) {
    struct StringList * ans = StringListNil();
    while (prop_list != NULL) {
        ans = StringListLink(ans, CollectDefaultTypeVarsProp(prop_list->head, env));
        prop_list = prop_list->next;
    }
    return StringListUnique(ans);
}

struct StringList * CollectDefaultTypeVarsSep(struct Separation * sep, struct environment * env) {
  if (sep == NULL) return StringListNil();
  struct StringList * ans;
  switch (sep->t) {
      case T_DATA_AT:
         ans = StringListLink(CollectDefaultTypeVarsExpr(sep->d.DATA_AT.left, env), CollectDefaultTypeVarsExpr(sep->d.DATA_AT.right, env));
         break;
      case T_UNDEF_DATA_AT:
         ans = CollectDefaultTypeVarsExpr(sep->d.UNDEF_DATA_AT.left, env);
         break;
      case T_ARR:
         ans = StringListLink(CollectDefaultTypeVarsExpr(sep->d.ARR.addr, env), CollectDefaultTypeVarsExpr(sep->d.ARR.value, env));
         break;
      case T_OTHER:
         ans = CollectDefaultTypeVarsExprList(sep->d.OTHER.exprs, env);
         break;
  }
  return StringListUnique(ans);
}

struct StringList * CollectDefaultTypeVarsSepList(struct SepList * sep_list, struct environment * env) {
    struct StringList * ans = StringListNil();
    while (sep_list != NULL) {
        ans = StringListLink(ans, CollectDefaultTypeVarsSep(sep_list->head, env));
        sep_list = sep_list->next;
    }
    return StringListUnique(ans);

}

struct StringList * CollectDefaultTypeVars(struct Assertion * asrt, struct environment * env) {
  struct StringList * ans = StringListNil();
  ans = StringListLink(ans, CollectDefaultTypeVarsPropList(asrt->prop_list, env));
  ans = StringListLink(ans, CollectDefaultTypeVarsSepList(asrt->sep_list, env));
  return StringListUnique(ans);
}

struct StringList * AsrtListCollectDefaultTypeVars(struct AsrtList * asrt, struct environment * env) {
   struct StringList * ans = StringListNil();
   for (struct AsrtList * i = asrt; i != NULL; i = i->next) {
      ans = StringListLink(ans, CollectDefaultTypeVars(i->head, env));
   }
   return StringListUnique(ans);
}


int IsPrimitiveCoqType(int id) {
   return id == BUILTINTYPE_Z || id == BUILTINTYPE_PROP || id == BUILTINTYPE_ASSERTION || 
          id == BUILTINTYPE_BOOL || id == BUILTINTYPE_NAT || id == BUILTINTYPE_LIST;
}

struct ExistList * PolyTypeListCollectTypeVars(struct PolyTypeList * poly_list, struct environment * env);

struct ExistList * PolyTypeCollectTypeVars(struct PolyType * type, struct environment * env) {
   if (type == NULL) return ExistListNil();
   struct ExistList * ans;
   switch (type->t) {
      case POLY_VAR: {
         if (!IsPrimitiveCoqType(type->d.VAR.id)) {
            struct atype_info * type_info = find_atype_by_id(type->d.VAR.id, &env->persist);
            if (!type_info->defined) {
               ans = ExistListCons(type->d.VAR.id, ExistListNil());
            } else {
               ans = ExistListNil();
            }
         } else {
            ans = ExistListNil();
         }
         break;
      }
      case POLY_FUNCAPP:
         if (PolyTypeListIsEmpty(type->d.FUNCAPP.args)) {
            if (!IsPrimitiveCoqType(type->d.FUNCAPP.func)) {
               struct atype_info * type_info = find_atype_by_id(type->d.FUNCAPP.func, &env->persist);
               if (!type_info->defined) {
                  ans = ExistListCons(type->d.FUNCAPP.func, ExistListNil());
               } else {
                  ans = ExistListNil();
               }
            } else {
               ans = ExistListNil();
            }
         } else {
            ans = PolyTypeListCollectTypeVars(type->d.FUNCAPP.args, env);
         }
         break;
      case POLY_ARROW:
         ans = ExistListLink(PolyTypeCollectTypeVars(type->d.ARROW.left, env), PolyTypeCollectTypeVars(type->d.ARROW.right, env));
         break;
   }
   return ExistListUnique(ans);
}

struct ExistList * PolyTypeListCollectTypeVars(struct PolyTypeList * poly_list, struct environment * env) {
   struct ExistList * ans = ExistListNil();
   struct PolyTypeListNode * node;
   for (node = poly_list->head; node != NULL; node = node->next) {
      ans = ExistListLink(ans, PolyTypeCollectTypeVars(node->data, env));
   }
   return ExistListUnique(ans);
}

struct ExistList * ExprValListCollectTypeVars(struct ExprValList * list, struct environment * env);

struct ExistList * ExprValCollectTypeVars(struct ExprVal * expr, struct environment * env) {
   if (expr == NULL) return ExistListNil();
   struct ExistList * ans;
   switch (expr->t) {
      case EZ_VAL:
         ans = ExistListNil();
         break;
      case VFIELD_ADDRESS:
         ans = ExprValCollectTypeVars(expr->d.VFIELD_ADDRESS.expr, env);
         break;
      case VUOP:
         ans = ExprValCollectTypeVars(expr->d.VUOP.expr, env);
         break;
      case VBOP:
         ans = ExistListLink(ExprValCollectTypeVars(expr->d.VBOP.expr1, env), 
                             ExprValCollectTypeVars(expr->d.VBOP.expr2, env));
         break;
      case FUNCAPP: {
         ans = ExistListLink(ExprValListCollectTypeVars(expr->d.FUNCAPP.args, env),
                             PolyTypeListCollectTypeVars(expr->d.FUNCAPP.types, env));
         break;
      }
      case LINDEX:
         ans = ExistListLink(ExprValCollectTypeVars(expr->d.LINDEX.list, env), 
                             ExprValCollectTypeVars(expr->d.LINDEX.index, env));
         break;
      case SIZE_OF:
         ans = ExistListNil();
         break;
      default:
         FPRINT(stderr, "unsupported at %s %d\n", __FILE__, __LINE__);
         exit(1);
         break;
   }
   return ExistListUnique(ans);
}

struct ExistList * ExprValListCollectTypeVars(struct ExprValList * list, struct environment * env) {
   struct ExistList * ans = ExistListNil();
   struct ExprValListNode * node;
   for (node = list->head; node != NULL; node = node->next) {
      ans = ExistListLink(ans, ExprValCollectTypeVars(node->data, env));
   }
   return ExistListUnique(ans);
}

struct ExistList * PropCollectTypeVars(struct Proposition * prop, struct environment * env) {
   if (prop == NULL) return ExistListNil();
   struct ExistList * ans;
   switch (prop->t) {
      case T_PROP_TRUE:
         ans = ExistListNil();
         break;
      case T_PROP_FALSE:
         ans = ExistListNil();
         break;
      case T_PROP_UNARY:
         ans = PropCollectTypeVars(prop->d.UNARY.prop, env);
         break;
      case T_PROP_BINARY:
         ans = ExistListLink(PropCollectTypeVars(prop->d.BINARY.prop1, env), PropCollectTypeVars(prop->d.BINARY.prop2, env));
         break;
      case T_PROP_PTR:
         ans = ExistListNil();
         break;
      case T_PROP_COMPARE:
         ans = ExistListLink(ExprValCollectTypeVars(prop->d.COMPARE.expr1, env), ExprValCollectTypeVars(prop->d.COMPARE.expr2, env));
         break;
      case T_PROP_QUANTIFIER:
         ans = PropCollectTypeVars(prop->d.QUANTIFIER.prop, env);
         break;
      case T_PROP_OTHER:
         ans = ExistListLink(PolyTypeListCollectTypeVars(prop->d.OTHER.types, env), ExprValListCollectTypeVars(prop->d.OTHER.args, env));
         break;
   }
   return ans;
}

struct ExistList * SepCollectTypeVars(struct Separation * sep, struct environment * env) {
   if (sep == NULL) return ExistListNil();
   struct ExistList * ans;
   switch (sep->t) {
      case T_DATA_AT:
         ans = ExistListLink(ExprValCollectTypeVars(sep->d.DATA_AT.left, env), ExprValCollectTypeVars(sep->d.DATA_AT.right, env));
         break;
      case T_UNDEF_DATA_AT:
         ans = ExprValCollectTypeVars(sep->d.UNDEF_DATA_AT.left, env);
         break;
      case T_ARR:
         ans = ExistListLink(ExprValCollectTypeVars(sep->d.ARR.addr, env), ExprValCollectTypeVars(sep->d.ARR.value, env));
         break;
      case T_OTHER:
         ans = ExistListLink(ExprValListCollectTypeVars(sep->d.OTHER.exprs, env), PolyTypeListCollectTypeVars(sep->d.OTHER.types, env));
         break;
   }
   return ExistListUnique(ans);
}

struct ExistList * SepListCollectTypeVars(struct SepList * sep_list, struct environment * env) {
   struct ExistList * ans = ExistListNil();
   while (sep_list != NULL) {
      ans = ExistListLink(ans, SepCollectTypeVars(sep_list->head, env));
      sep_list = sep_list->next;
   }
   return ExistListUnique(ans);
}

struct ExistList * PropListCollectTypeVars(struct PropList * prop_list, struct environment * env) {
   struct ExistList * ans = ExistListNil();
   while (prop_list != NULL) {
      ans = ExistListLink(ans, PropCollectTypeVars(prop_list->head, env));
      prop_list = prop_list->next;
   }
   return ExistListUnique(ans);
}

struct ExistList * CollectTypeVars(struct Assertion * asrt, struct environment * env) {
   struct ExistList * ans = ExistListNil();
   ans = ExistListLink(ans, PropListCollectTypeVars(asrt->prop_list, env));
   ans = ExistListLink(ans, SepListCollectTypeVars(asrt->sep_list, env));
   struct ExistList * vars = CollectAllVars(asrt, env);
   for (struct ExistList * i = vars; i != NULL; i = i->next) {
      struct logic_var_info * var_info = find_logic_var_by_id(i->id, &env->persist);
      struct PolyType * type = cpa_type_of(var_info->atype);
      ans = ExistListLink(ans, PolyTypeCollectTypeVars(type, env));
      PolyTypeFree(type);
   }
   ans = ExistListUnique(ans);
   return ans;
}

struct ExistList * AsrtListCollectTypeVars(struct AsrtList * asrt, struct environment * env) {
   struct ExistList * ans = ExistListNil();
   for (struct AsrtList * i = asrt; i != NULL; i = i->next) {
      ans = ExistListLink(ans, CollectTypeVars(i->head, env));
   }
   return ExistListUnique(ans);
}

void WriteAndExtendInNeed(char ** ret, int * size_of_ret, int * length_of_ret, char * str) {
   int len = strlen(str);
   if (*length_of_ret + len > *size_of_ret) {
      *size_of_ret = *size_of_ret * 2;
      *ret = (char *)realloc(*ret, ((*size_of_ret) + 1));
   }
   strcpy(*ret + *length_of_ret, str);
   *length_of_ret += len;
}

void CoqPrintSacGetRealNameAux(struct renaming_info * info, char ** ret, 
                               int *size_of_ret, int *length_of_ret, 
                               int ignore_o, struct environment * env) {
   if (info == NULL) return;
   if (*size_of_ret == 0) {
      *ret = (char *)malloc(21);
      *size_of_ret = 20;
   }
   switch (info->t) {
      case RENAME_VAR_PRE_VALUE:
         WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, info->d.var_pre_value.var_name);
         WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, "_pre");
         break;
      case RENAME_VAR_VALUE:
         WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, info->d.var_value.var_name);
         break;
      case RENAME_VAR_ADDR:   // here use 32768 as magic number for distinguish real address and value of address
         if (ignore_o != 32768) WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, "( &( \"");
         WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, info->d.var_addr.var_name);
         if (ignore_o != 32768) WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, "\" ) )");
         if (ignore_o == 32768) WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, "_addr");
         break;
      case RENAME_DEREF:
         CoqPrintSacGetRealNameAux(info->d.deref.info, ret, size_of_ret, length_of_ret, 32768, env);
         WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, "_v");
         break;
      case RENAME_FIELD:
         CoqPrintSacGetRealNameAux(info->d.field.info, ret, size_of_ret, length_of_ret, 32768, env);
         WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, "_");
         WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, info->d.field.name);
         break;
      case RENAME_FALLBACK:
         WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, info->d.fallback.name);
         break;
      case RENAME_POST_INTROED:
         WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, info->d.post_introed.var_name);
         WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, "_in");
         char * tmp = (char *)malloc(LengthOfInt(info->d.post_introed.call_id) + 1);
         sprintf(tmp, "%d", info->d.post_introed.call_id);
         WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, tmp);
         free(tmp);
         break;
      case RENAME_RETURN_VALUE:
         WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, "retval");
         break;
      case RENAME_FORALL_VAR:
         WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, info->d.forall_var.var_name);
         break;
      case RENAME_EXISTS_VAR:
         WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, info->d.exists_var.var_name);
         break;
      case RENAME_FREE_VAR:
         WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, info->d.free_var.var_name);
         break;
   }
   // printf("the real name is %s\n", *ret);
   // if (info->is_old && !ignore_o) {
   //    WriteAndExtendInNeed(ret, size_of_ret, length_of_ret, "_o");
   // }
}

char * CoqPrintSacGetRealName(struct renaming_info * info, int ignore_o, struct environment * env) {
   char * ret = NULL;
   int size_of_ret = 0;
   int length_of_ret = 0;
   CoqPrintSacGetRealNameAux(info, &ret, &size_of_ret, &length_of_ret, ignore_o, env);
   return ret;  
}

void CoqPrintSacRenamingInfo(struct renaming_info * info, struct environment * env, FILE * fp) {
   switch (info->t) {
      case RENAME_VAR_PRE_VALUE:
         FPRINT(fp, "%s_pre", info->d.var_pre_value.var_name);
         break;
      case RENAME_VAR_VALUE: {
         FPRINT(fp, "%s", info->d.var_value.var_name);
         break;
      }
      case RENAME_VAR_ADDR:
         FPRINT(fp, "&(\" %s \")", info->d.var_addr.var_name);
         break;
      case RENAME_DEREF:
         CoqPrintSacRenamingInfo(info->d.deref.info, env, fp);
         FPRINT(fp, "_v");
         break;
      case RENAME_FIELD:
         CoqPrintSacRenamingInfo(info->d.field.info, env, fp);
         FPRINT(fp, "_%s", info->d.field.name);
         break;
      case RENAME_FALLBACK:
         FPRINT(fp, "%s", info->d.fallback.name);
         break;
      case RENAME_POST_INTROED:
         FPRINT(fp, "%s_in%d", info->d.post_introed.var_name, info->d.post_introed.call_id);
         break;
      case RENAME_RETURN_VALUE:
         FPRINT(fp, "retval");
         break;
      case RENAME_FORALL_VAR:
         FPRINT(fp, "%s", info->d.forall_var.var_name);
         break;
      case RENAME_EXISTS_VAR:
         FPRINT(fp, "%s", info->d.exists_var.var_name);
         break;
      case RENAME_FREE_VAR:
         FPRINT(fp, "%s", info->d.free_var.var_name);
         break;
   }
   if (info->is_old) {
      FPRINT(fp, "_o");
   }
}
  
void CoqPrintSacVari(int id, struct environment * env, struct RealNameMapping * map, FILE * fp) {
   struct atype_info * type_info = find_atype_by_id(id, &env->persist);
   if (type_info != NULL) {
      FPRINT(fp, "%s", type_info->name);
      return;
   }
   struct func_info * func_info = find_func_by_id(id, &env->persist);
   if (func_info != NULL) {
      FPRINT(fp, "%s", func_info->name);
      return;
   }
   struct logic_var_info * var_info = find_logic_var_by_id(id, &env->persist);
   if (var_info->category == LOGIC_EXTERN) {
      FPRINT(fp, "%s", var_info->name);
      return;
   } else if (var_info->renaming == NULL) {
      FPRINT(fp, "_%d", id);
   } else {
      char * real_name = RealNameMappingGetName(map, id);
      if (real_name == NULL) {
        FPRINT(stderr, "can not find the variable name.\n");
        FPRINT(stderr, "the id is %d\n", id);
        exit(1);
      }
      FPRINT(fp, "%s", real_name);
   }
}

void CoqPrintSacTypeList(struct PolyTypeList * list, struct environment * env, FILE * fp);

void CoqPrintSacType(struct PolyType * type, struct environment * env, FILE * fp) {
   if (type == NULL) return;
   switch (type->t) {
      case POLY_VAR: {
         struct atype_info * type_info = find_atype_by_id(type->d.VAR.id, &env->persist);
         FPRINT(fp, "%s", type_info->name);
         break;
      }
      case POLY_FUNCAPP: {
         struct atype_info * type_info = find_atype_by_id(type->d.FUNCAPP.func, &env->persist);
         if (strncmp(type_info->name, "prod", 4) == 0) {
            assert(PolyTypeListLength(type->d.FUNCAPP.args) == 2);
            FPRINT(fp, "(");
            CoqPrintSacType(type->d.FUNCAPP.args->head->data, env, fp);
            FPRINT(fp, " * ");
            CoqPrintSacType(type->d.FUNCAPP.args->head->next->data, env, fp);
            FPRINT(fp, ")");
            break;
         }
         if (PolyTypeListIsEmpty(type->d.FUNCAPP.args)) {
            FPRINT(fp, "%s", type_info->name);
         } else {
            FPRINT(fp, "(@%s ", type_info->name);
            CoqPrintSacTypeList(type->d.FUNCAPP.args, env, fp);
            FPRINT(fp, ")");
         }
         break;
      }
      case POLY_ARROW: {
         FPRINT(fp, "(");
         CoqPrintSacType(type->d.ARROW.left, env, fp);
         FPRINT(fp, " -> ");
         CoqPrintSacType(type->d.ARROW.right, env, fp);
         FPRINT(fp, ")");
         break;
      }
   }
}

void CoqPrintSacTypeList(struct PolyTypeList * list, struct environment * env, FILE * fp) {
   if (PolyTypeListIsEmpty(list)) return;
   for (struct PolyTypeListNode * type = list->head; type != NULL; type = type->next) {
      CoqPrintSacType(type->data, env, fp);
      if (type->next != NULL) {
         FPRINT(fp, " ");
      }
   }
}

int Not_Addr(int id, struct environment *env) {
  struct logic_var_info * var_info = find_logic_var_by_id(id, &env->persist);
  if (var_info->renaming->t == RENAME_VAR_ADDR) {
    return 0;
  }
  return 1;
}

int Not_Addr_Var(struct ExprVal *expr, struct environment *env) {
  if (expr == NULL) {
    FPRINT(stderr, "Input expr of Not_Addr_Var is NULL\n");
    exit(1);
  }
  if (expr -> t == FUNCAPP){
    struct logic_var_info * info = find_logic_var_by_id(expr->d.FUNCAPP.id, &env->persist);    
    if (info == NULL) {
      FPRINT(stderr, "Cannot find function info for %d\n", expr->d.FUNCAPP.id);
      exit(1);
    }
    if (!ExprValListIsEmpty(expr->d.FUNCAPP.args)) return 1;     
    return Not_Addr(expr->d.FUNCAPP.id, env);
  }
  return 1;
}


void CoqPrintSacVardef(int id, struct environment * env, struct RealNameMapping * map, FILE * fp) {
   FPRINT(fp, "(");
   CoqPrintSacVari(id, env, map, fp);
   FPRINT(fp, ": ");
   struct logic_var_info * info = find_logic_var_by_id(id, &env->persist);
  //  printf("logic var id : %d\n", id);
  //  print_atype(info->atype);
  //  PrintPolyType(cpa_type_of(info->atype), env);
   CoqPrintSacType(cpa_type_of(info->atype), env, fp);
   FPRINT(fp, ") ");
}

void CoqPrintSacExistList(struct ExistList * exist_list, char * start, char * end, struct environment * env, struct RealNameMapping * map, FILE * fp) {
   if (exist_list == NULL) return;
   FPRINT(fp, "  %sEX ", start);
   for (struct ExistList * i = exist_list; i != NULL; i = i->next) {
      CoqPrintSacVari(i->id, env, map, fp);
      if (i->next != NULL) {
         FPRINT(fp, " ");
      }
   }
   FPRINT(fp, ",%s", end);
}

void CoqPrintSacUOp(enum InnerUnaryOperation op, FILE * fp) {
   switch (op) {
      case Oneg:
         FPRINT(fp, "-");
         break;
      case Onint: {
         FPRINT(fp, "Z.lnot ");
         break;
      }
      case Onot: {
         FPRINT(fp, "Z.lnot ");
         break;
      }
   }
}

void CoqPrintSacBinOp(enum InnerBinaryOperation op, FILE * fp) {
   switch (op) {
      case Oadd:
         FPRINT(fp, "+");
         break;
      case Osub:
         FPRINT(fp, "-");
         break;
      case Omul:
         FPRINT(fp, "*");
         break;
      case Odiv:
         FPRINT(fp, "÷");
         break;
      case Omod:
         FPRINT(fp, "%%");
         break;
      case Oand:
         FPRINT(fp, "&");
         break;
      case Oor:
         FPRINT(fp, "|");
         break;
      case Oxor:
         FPRINT(fp, "^");
         break;
      case Oshl:
         FPRINT(fp, "<<");
         break;
      case Oshr:
         FPRINT(fp, ">>");
         break;
   }
}

void CoqPrintPropCompOp(enum PropCompOp op, FILE * fp) {
   switch (op) {
      case PROP_LE:
         FPRINT(fp, "<=");
         break;
      case PROP_GE:
         FPRINT(fp, ">=");
         break;
      case PROP_LT:
         FPRINT(fp, "<");
         break;
      case PROP_GT:
         FPRINT(fp, ">");
         break;
      case PROP_EQ:
         FPRINT(fp, "=");
         break;
      case PROP_NEQ:
         FPRINT(fp, "<>");
         break;
   }
}

void CoqPrintSacExprVal(struct ExprVal * expr, struct environment * env, struct RealNameMapping * map, FILE * fp);

void CoqPrintSacExprValNestedField(struct ExprVal * expr, struct environment * env, struct RealNameMapping * map, FILE * fp) {
   assert(expr->t == VFIELD_ADDRESS);
   struct field_info * field_info = find_field_by_id(expr->d.VFIELD_ADDRESS.field_id, &env->persist);
   struct ExprVal * base_addr = expr->d.VFIELD_ADDRESS.expr;
   if (base_addr->t == VFIELD_ADDRESS) {
      CoqPrintSacExprValNestedField(base_addr, env, map, fp);
      FPRINT(fp, " .ₛ \"%s\"", field_info->name);
   } else {     
      if (Not_Addr_Var(base_addr, env)) {
        FPRINT(fp, "(");
        CoqPrintSacExprVal(base_addr, env, map, fp);
        FPRINT(fp, ") ");
        FPRINT(fp, " # \"%s\" ", field_info->parent->name);
      }
      else {
        CoqPrintSacExprVal(base_addr, env, map, fp);
      }
      FPRINT(fp, "->ₛ \"%s\"", field_info->name);
   }
}

void CoqPrintSacExprVal(struct ExprVal * expr, struct environment * env, struct RealNameMapping * map, FILE * fp) {
   if (expr == NULL) return;
   switch (expr->t) {
      case EZ_VAL:
         if (expr->d.EZ_VAL.number == 2147483647) {
            FPRINT(fp, "INT_MAX");
         } else {
            FPRINT(fp, "%llu", expr->d.EZ_VAL.number);
         }
         break;
      case SIZE_OF: {
         switch (expr->d.SIZE_OF.type->t) {
            case C_int8: {
               FPRINT(fp, "sizeof(CHAR)");
               break;
            }
            case C_int16: {
               FPRINT(fp, "sizeof(SHORT)");
               break;
            }
            case C_int32: {
               FPRINT(fp, "sizeof(INT)");
               break;
            }
            case C_int64: {
               FPRINT(fp, "sizeof(INT64)");
               break;
            }
            case C_pointer: {
               FPRINT(fp, "sizeof(PTR)");
               break;
            }
            case C_union: {
               char * union_name = find_union_by_id(expr->d.SIZE_OF.type->d.CUNION.union_id, &env->persist) -> name;
               FPRINT(fp, "sizeof( \"%s\" )", union_name);
               break;
            }
            case C_struct: {
               char * struct_name = find_struct_by_id(expr->d.SIZE_OF.type->d.CSTRUCT.struct_id, &env->persist) -> name;
               FPRINT(fp, "sizeof( \"%s\" )", struct_name);
               break;
            }
            default: {
               FPRINT(stderr, "unsupported at %s %d\n", __FILE__, __LINE__);
               exit(1);
            }
         }
         break;
      }
      case VFIELD_ADDRESS: {
         FPRINT(fp, "&(");
         CoqPrintSacExprValNestedField(expr, env, map, fp);
         FPRINT(fp, ")");
         break;
      }
      case VUOP:
         FPRINT(fp, "(");
         if (expr->d.VUOP.op == Oneg && expr->d.VUOP.expr->t == EZ_VAL && expr->d.VUOP.expr->d.EZ_VAL.number == 2147483648) {
            FPRINT(fp, "INT_MIN)");
            break;
         }
         CoqPrintSacUOp(expr->d.VUOP.op, fp);
         CoqPrintSacExprVal(expr->d.VUOP.expr, env, map, fp);
         FPRINT(fp, ")");
         break;
      case VBOP:
         if (expr->d.VBOP.op == Oshl || expr->d.VBOP.op == Oshr || expr->d.VBOP.op == Oor || expr->d.VBOP.op == Oand) {
            FPRINT(fp, "(");
            if (expr->d.VBOP.op == Oshl) {
               FPRINT(fp, "Z.shiftl");
            } else if (expr->d.VBOP.op == Oshr) {
               FPRINT(fp, "Z.shiftr");
            } else if (expr->d.VBOP.op == Oor) {
               FPRINT(fp, "Z.lor");
            } else if (expr->d.VBOP.op == Oand) {
               FPRINT(fp, "Z.land");
            }
            FPRINT(fp, " ");
            CoqPrintSacExprVal(expr->d.VBOP.expr1, env, map, fp);
            FPRINT(fp, " ");
            CoqPrintSacExprVal(expr->d.VBOP.expr2, env, map, fp);
            FPRINT(fp, ")");
         } else {
            FPRINT(fp, "(");
            CoqPrintSacExprVal(expr->d.VBOP.expr1, env, map, fp);
            FPRINT(fp, " ");
            CoqPrintSacBinOp(expr->d.VBOP.op, fp);
            FPRINT(fp, " ");
            if (expr->d.VBOP.op == Omod) FPRINT(fp, "( ");
            CoqPrintSacExprVal(expr->d.VBOP.expr2, env, map, fp);
            if (expr->d.VBOP.op == Omod) FPRINT(fp, " )");
            FPRINT(fp, " )");
         }
         break;
      case FUNCAPP: {
         struct logic_var_info * info = find_logic_var_by_id(expr->d.FUNCAPP.id, &env->persist);    
         if (info == NULL) {
            FPRINT(stderr, "Cannot find function info for %d\n", expr->d.FUNCAPP.id);
            exit(1);
         }
         if (info->category == LOGIC_PROJ) {
           int flag = ExprValListLength(expr->d.FUNCAPP.args) == 1;
           FPRINT(fp, "(");
           CoqPrintSacExprVal(expr->d.FUNCAPP.args->head->data, env, map, fp);
           FPRINT(fp, ".(%s) ", info->name);
           if (!flag) {
            struct ExprValListNode * node;
            for (node = expr->d.FUNCAPP.args->head->next; node != NULL; node = node->next) {
               FPRINT(fp, "(");
               CoqPrintSacExprVal(node->data, env, map, fp);
               FPRINT(fp, ")");
               if (node->next != NULL) FPRINT(fp, " ");
            }
           }
           FPRINT(fp, ")");

         } else {
            int flag = ExprValListIsEmpty(expr->d.FUNCAPP.args);
            if (!flag) {
             FPRINT(fp, "(");
            }
            CoqPrintSacVari(expr->d.FUNCAPP.id, env, map, fp);
            if (!flag) {
               FPRINT(fp, " ");
            }
            struct ExprValListNode * node;
            for (node = expr->d.FUNCAPP.args->head; node != NULL; node = node->next) {
               FPRINT(fp, "(");
               CoqPrintSacExprVal(node->data, env, map, fp);
               FPRINT(fp, ")");
               if (node->next != NULL) FPRINT(fp, " ");
            }
            if (!flag) {
             FPRINT(fp, ")");
            }
         }
         break;
      }
      case LINDEX: {
         FPRINT(fp, "(Znth ");
         struct var_scope_union *logic_var = find_logic_var_by_name(strdup("Znth"),&(env->ephemer));
         if (logic_var == NULL) {
            fprintf(stderr, "Cannot find function Znth in the environment, which will be used in Coq compilation.\n");
            exit(1);
         }
         char * type = Get_atype_name(InnerExprInfer(expr->d.LINDEX.list, env));
         if (strncmp(type, "_List_", 6) != 0) {
            fprintf(stderr, "The array ");
            CoqPrintSacExprVal(expr->d.LINDEX.list, env, map, stderr);
            fprintf(stderr, " of Znth is not a list type.\n");
            fprintf(stderr, "The type is %s\n", type);
            exit(1);
         }
         CoqPrintSacExprVal(expr->d.LINDEX.index, env, map, fp);
         FPRINT(fp, " ");
         CoqPrintSacExprVal(expr->d.LINDEX.list, env, map, fp);
         FPRINT(fp, " ");
         if (strncmp(type + 6, "Z", 1) == 0) {
            FPRINT(fp, "0");
         } else {
            FPRINT(fp, "__default_%s",type + 6);
         }
         FPRINT(fp, ")");
         free(type);
         break;
      }
      default : {
         FPRINT(stderr, "unsupported at %s %d\n", __FILE__, __LINE__);
         exit(1);
      }
   }
}

void CoqPrintSacProposition(struct Proposition * prop, struct environment * env, struct RealNameMapping * map, FILE * fp) {
   if (prop == NULL) return;
   switch (prop->t) {
      case T_PROP_TRUE:
         FPRINT(fp, "True");
         break;
      case T_PROP_FALSE:
         FPRINT(fp, "False");
         break;
      case T_PROP_UNARY: {
         switch (prop->d.UNARY.op) {
            case PROP_NOT:
               FPRINT(fp, "~");
               FPRINT(fp, "(");
               CoqPrintSacProposition(prop->d.UNARY.prop, env, map, fp);
               FPRINT(fp, ")");
            break;
         }
         break;
      }
      case T_PROP_BINARY: {
         switch (prop->d.BINARY.op) {
            case PROP_AND:
               FPRINT(fp, "(");
               CoqPrintSacProposition(prop->d.BINARY.prop1, env, map, fp);
               FPRINT(fp, " /\\ ");
               CoqPrintSacProposition(prop->d.BINARY.prop2, env, map, fp);
               FPRINT(fp, ")");
               break;
            case PROP_OR:
               FPRINT(fp, "(");
               CoqPrintSacProposition(prop->d.BINARY.prop1, env, map, fp);
               FPRINT(fp, " \\/ ");
               CoqPrintSacProposition(prop->d.BINARY.prop2, env, map, fp);
               FPRINT(fp, ")");
               break;
            case PROP_IMPLY:
               FPRINT(fp, "(");
               CoqPrintSacProposition(prop->d.BINARY.prop1, env, map, fp);
               FPRINT(fp, " -> ");
               CoqPrintSacProposition(prop->d.BINARY.prop2, env, map, fp);
               FPRINT(fp, ")");
               break;
            case PROP_IFF:
               FPRINT(fp, "(");
               CoqPrintSacProposition(prop->d.BINARY.prop1, env, map, fp);
               FPRINT(fp, " <-> ");
               CoqPrintSacProposition(prop->d.BINARY.prop2, env, map, fp);
               FPRINT(fp, ")");
               break;
         }
         break;
      }
      case T_PROP_PTR:
         FPRINT(stderr, "Ptr Prop not supported at %s %d\n", __FILE__, __LINE__);
         break;
      case T_PROP_COMPARE:
         FPRINT(fp, "(");
         CoqPrintSacExprVal(prop->d.COMPARE.expr1, env, map, fp);
         FPRINT(fp, " ");
         CoqPrintPropCompOp(prop->d.COMPARE.op, fp);
         FPRINT(fp, " ");
         CoqPrintSacExprVal(prop->d.COMPARE.expr2, env, map, fp);
         FPRINT(fp, ")");
         break;
      case T_PROP_QUANTIFIER: {
         if (prop->d.QUANTIFIER.op == PROP_FORALL) {
            FPRINT(fp, "forall ");
         } else if (prop->d.QUANTIFIER.op == PROP_EXISTS) {
            FPRINT(fp, "exists ");
         } else {
            FPRINT(stderr, "unknown QUANTIFIER at %s %d\n", __FILE__, __LINE__);
         }
         CoqPrintSacVardef(prop->d.QUANTIFIER.ident, env, map, fp);
         FPRINT(fp, ", ");
         CoqPrintSacProposition(prop->d.QUANTIFIER.prop, env, map, fp);
         break;
      }
      case T_PROP_OTHER: {
         struct logic_var_info * var_info = find_logic_var_by_id(prop->d.OTHER.predicate, &env->persist);
         FPRINT(fp, "(%s ", var_info->name);
         struct ExprValListNode * node;
         for (node = prop->d.OTHER.args->head; node != NULL; node = node->next) {
            CoqPrintSacExprVal(node->data, env, map, fp);
            FPRINT(fp, " ");
         }
         FPRINT(fp, ")");
      }
   }
}

void CoqPrintSacPropList(struct PropList * prop_list, char * start, char * end, struct environment * env, struct RealNameMapping * map, FILE * fp) {
   if (prop_list == NULL) {
      return;
   }
   for (struct PropList * i = prop_list; i != NULL; i = i->next) {
      FPRINT(fp, "  ");
      if (i == prop_list) {
         FPRINT(fp, "%s", start);
      }
      FPRINT(fp, "[| ");
      CoqPrintSacProposition(i->head, env, map, fp);
      FPRINT(fp, " |]");
      if (i->next != NULL) {
         FPRINT(fp, " \n");
         FPRINT(fp, "  &&");
      }
   }
   if (end != NULL) {
      FPRINT(fp, "%s", end);
   }
}

void CoqPrintSacDataAtType(struct SimpleCtype * ty, struct environment * env, FILE * fp) {
   switch (ty->t) {
      case C_int8:
         if (ty->d.CINT8.s == Signed) {
            FPRINT(fp, "Char");
         } else {
            FPRINT(fp, "UChar");
         }
         break;
      case C_int16:
         if (ty->d.CINT16.s == Signed) {
            FPRINT(fp, "Short");
         } else {
            FPRINT(fp, "UShort");
         }
         break;
      case C_int32:
         if (ty->d.CINT32.s == Signed) {
            FPRINT(fp, "Int");
         } else {
            FPRINT(fp, "UInt");
         }
         break;
      case C_int64:
         if (ty->d.CINT64.s == Signed) {
            FPRINT(fp, "Int64");
         } else {
            FPRINT(fp, "UInt64");
         }
         break;
      default:
         FPRINT(stderr, "unsupported at %s %d\n", __FILE__, __LINE__);
         PrintSimpleCtype(ty, env);
         exit(0);
         break;
   }
}

void CoqPrintSacSeparation(struct Separation * sep, struct environment * env, struct RealNameMapping * map, FILE * fp) {
   if (sep == NULL) return;
   FPRINT(fp, "(");
   switch (sep->t) {
      case T_DATA_AT:
         FPRINT(fp, "(");
         CoqPrintSacExprVal(sep->d.DATA_AT.left, env, map, fp);
         FPRINT(fp, ") # ");
         switch (sep->d.DATA_AT.ty->t) {
            case C_int8:
            case C_int16:
            case C_int32:
            case C_int64:
               CoqPrintSacDataAtType(sep->d.DATA_AT.ty, env, fp);
               break;
            default:
               FPRINT(fp, "Ptr");
               break;
         }
         FPRINT(fp, " ");
         FPRINT(fp, " |-> ");
         CoqPrintSacExprVal(sep->d.DATA_AT.right, env, map, fp);
         break;
      case T_UNDEF_DATA_AT: {
         FPRINT(fp, "(");
         CoqPrintSacExprVal(sep->d.UNDEF_DATA_AT.left, env, map, fp);
         FPRINT(fp, ") # ");
         switch (sep->d.UNDEF_DATA_AT.ty->t) {
            case C_int8:
            case C_int16:
            case C_int32:
            case C_int64:
               CoqPrintSacDataAtType(sep->d.DATA_AT.ty, env, fp);
               break;
            default:
               FPRINT(fp, "Ptr");
               break;
         }
         FPRINT(fp, "  |->_");
         break;
      }
      case T_ARR:
         FPRINT(stderr, "Array not supported at %s %d\n", __FILE__, __LINE__);
         break;
      case T_OTHER: {
         struct logic_var_info * info = find_logic_var_by_id(sep->d.OTHER.sep_id, &env->persist);
         assert(info->category == LOGIC_SEPDEF ||
                info->category == LOGIC_FREE || 
                info->category == LOGIC_EXTERN);
         FPRINT(fp, "%s ", info->name);
         struct ExprValListNode * node;
         for (node = sep->d.OTHER.exprs->head; node != NULL; node = node->next) {
            CoqPrintSacExprVal(node->data, env, map, fp);
            FPRINT(fp, " ");
         }
         break;
      }
   }
   FPRINT(fp, ")");
}

void CoqPrintSacSepList(struct SepList * sep_list, int exhausted, char * start, char * end, struct environment * env, struct RealNameMapping * map, FILE * fp) {
   if (sep_list == NULL) {
      if (exhausted) {
         FPRINT(fp, "  %semp%s", start, end);
      }
      return;
   }
   for (struct SepList * i = sep_list; i != NULL; i = i->next) {
      FPRINT(fp, "  ");
      if (i == sep_list && start != NULL) {
         FPRINT(fp, "%s", start);
      }
      if (i != sep_list) {
         FPRINT(fp, "**  ");
      }
      CoqPrintSacSeparation(i->head, env, map, fp);
      if (i->next != NULL || !exhausted) {
         FPRINT(fp, "\n");
      }
   }
   if (!exhausted) {
      FPRINT(fp, "** TT");
   }
   FPRINT(fp, "%s", end);
}

void CoqPrintSacAssertion(struct Assertion * asrt, int exhausted, char * start, char * end, struct environment * env, struct RealNameMapping * map, FILE * fp) {
   if (asrt == NULL) return;
   struct ExistList * allvars = CollectAllVars(asrt, env);
   struct ExistList * exist = ExistListDeepCopy(asrt->exist_list);
   for (struct ExistList * i = exist; i != NULL; i = i->next) {
      if (!ExistListContains(i->id, allvars)) {
        asrt->exist_list = ExistListRemove(i->id,asrt->exist_list);
      }
   }
   if (asrt->exist_list != NULL) {
      CoqPrintSacExistList(asrt->exist_list, start, "\n", env, map, fp);
      start = "";
   }
   if (asrt->prop_list == NULL && asrt->sep_list == NULL) {
      FPRINT(fp, "  %sTT && emp %s", start, end);
      return;
   }
   if (asrt->prop_list != NULL) {
      if (asrt->sep_list != NULL || exhausted) {
         CoqPrintSacPropList(asrt->prop_list, start, "\n", env, map, fp);
      } else {
         CoqPrintSacPropList(asrt->prop_list, start, end, env, map, fp);
      }
      start = "";
   }
   char * sep_start = (char*) malloc(sizeof(char) * (strlen(start) + 5));;
   if (asrt->prop_list != NULL) {
      sprintf(sep_start, "&&  %s", start);
   } else {
      sprintf(sep_start, "%s", start);
   }
   CoqPrintSacSepList(asrt->sep_list, exhausted, sep_start, end, env, map, fp);
   free(sep_start);
}

void CoqPrintSacAsrtList(struct AsrtList * asrt_list, int exhausted, char * start, char * end, struct environment * env, struct RealNameMapping * map, FILE * fp) {
   if (asrt_list == NULL) return;
   int need_parren = (asrt_list->next != NULL);
   for (struct AsrtList * i = asrt_list; i != NULL; i = i->next) {
      if (i != asrt_list) {
         FPRINT(fp, "  ||\n");
      }
      char * real_start = malloc(sizeof(char) * (strlen(start) + 2));
      sprintf(real_start, "%s%s", i == asrt_list ? start : "", need_parren ? "(" : "");
      char * real_end = i->next == NULL ? (need_parren ? ")" : "") : (need_parren ? ")\n" : "\n");
      CoqPrintSacAssertion(i->head, exhausted, real_start, real_end, env, map, fp);
      free(real_start);
   }
   FPRINT(fp, "%s", end);
}

void CoqPrintSacProof(char * name, FILE * fp) {
   FPRINT(fp, "Lemma proof_of_%s : %s.\n", name, name);
   FPRINT(fp, "Proof. Admitted. \n\n");
   char * name_copy = malloc(sizeof(char) * (strlen(name) + 1));
   strcpy(name_copy, name);
   all_proof_goals = StringListSnoc(name_copy, all_proof_goals);
}

void CoqPrintSacGetRealNameInAsrt(struct Assertion * asrt, int ignore_o,
                                  struct RealNameMapping * map, struct environment * env) {
   struct ExistList * free_vars = CollectFreeVars(asrt, env);
   struct ExistList * all_vars = ExistListLink(ExistListDeepCopy(asrt->exist_list), free_vars);
   for (struct ExistList * i = all_vars; i != NULL; i = i->next) {
      // if (find_logic_var_by_id(i->id, &env->persist) == NULL) {
      //    fprintf(stderr, "Cannot find logic var for %d\n", i->id);
      //     exit(1);
      // }
      // printf("id: %d\n", i->id);
      char * real_name = CoqPrintSacGetRealName(find_logic_var_by_id(i->id, &env->persist)->renaming, ignore_o, env);
      // if (real_name == NULL) 
      //   real_name = CoqPrintSacGetRealName(find_projection_by_id(i->id, &env->persist)->var->renaming, ignore_o, env);
      RealNameMappingAdd(map, real_name, i->id);
   }
}

void CoqPrintSacGetRealNameInAsrtList(struct AsrtList * asrt_list, int ignore_o,
                                      struct RealNameMapping * map, struct environment * env) {
   for (struct AsrtList * i = asrt_list; i != NULL; i = i->next) {
      CoqPrintSacGetRealNameInAsrt(i->head, ignore_o, map, env);
   }
}

void CoqPrintSacEntailment(struct Assertion * ppre, struct AsrtList * ppost, 
                           int addressable, int exhausted, int ignore_o, char * name,
                           struct environment * env, FILE * fp) {
  FPRINT(fp, "Definition %s := \n", name);
  struct Assertion * pre = AsrtDeepCopy(ppre);
  struct AsrtList * post = AsrtListDeepCopy(ppost);
  if (addressable) {
    EliminateLocal(pre, post, env);
  }
  struct RealNameMapping * mapping = CreateRealNameMapping();
  CoqPrintSacGetRealNameInAsrtList(post, ignore_o, mapping, env);
  CoqPrintSacGetRealNameInAsrt(pre, ignore_o, mapping, env);
  ExistListFree(pre->exist_list);
  pre->exist_list = ExistListNil();
  struct ExistList * free_vars = CollectFreeVars(pre, env);
  // for (struct ExistList * i = free_vars; i != NULL; i = i->next) {
  //   printf("Pre free var %d\n", i->id);
  // }
  free_vars = ExistListUnique(ExistListLink(free_vars, AsrtListCollectFreeVars(post, env)));
  // for (struct ExistList * i = free_vars; i != NULL; i = i->next) {
  //   printf("All free var %d\n", i->id);
  // }
  int free_vars_counter = 0;
  for (struct ExistList * i = free_vars; i != NULL; i = i->next) {
    free_vars_counter += Not_Addr(i->id, env);
  }
  struct ExistList * type_vars = CollectTypeVars(pre, env);
  type_vars = ExistListUnique(ExistListLink(type_vars, AsrtListCollectTypeVars(post, env)));
  struct StringList * default_Typevars = CollectDefaultTypeVars(pre, env);
  default_Typevars = StringListUnique(StringListLink(default_Typevars, AsrtListCollectDefaultTypeVars(post, env)));
  if (free_vars_counter != 0 || type_vars != NULL || default_Typevars -> head != NULL) {
    FPRINT(fp, "forall ");
    for (struct ExistList * i = type_vars; i != NULL; i = i->next) {
      FPRINT(fp, "(");
      CoqPrintSacVari(i->id, env, mapping, fp);
      FPRINT(fp, ": Type) ");
    }
    for (struct ExistList * i = free_vars; i != NULL; i = i->next) {
      if (Not_Addr(i->id, env)) {
        CoqPrintSacVardef(i->id, env, mapping, fp);
      }
    }
    for (struct StringListNode * i = default_Typevars -> head; i != NULL; i = i->next) {
      FPRINT(fp, " __default_%s ", i->data);
    }
    FPRINT(fp, ",\n");
  }
  CoqPrintSacAssertion(pre, 1, "", "\n", env, mapping, fp);
  FPRINT(fp, "|--\n");
  CoqPrintSacAsrtList(post, exhausted, "", "\n", env, mapping, fp);
  FPRINT(fp, ".\n\n");
  ExistListFree(free_vars);
  ExistListFree(type_vars);
  StringListFree(default_Typevars);
  AsrtFree(pre);
  AsrtListFree(post);
  RealNameMappingFree(mapping);
}

void CoqPrintSacEntailmentCheckerWit(struct EntailmentCheckerWit * entailment_checker_wit, 
                                     struct environment * env, FILE * fp_goal, FILE * fp_auto, FILE * fp_manual) {
   if (entailment_checker_wit == NULL) return;
   CoqPrintSacEntailmentCheckerWit(entailment_checker_wit->next, env, fp_goal, fp_auto, fp_manual);
   ++entailment_wit_cnt;
   int total = 0;
   for (struct AsrtList * pre = entailment_checker_wit->pre; pre != NULL; pre = pre->next) {
      ++total;
   }
   int cnt = 0;
   char * name = malloc(sizeof(char) * (strlen(func_name) + 30));
   for (struct AsrtList * pre = entailment_checker_wit->pre; pre != NULL; pre = pre->next) {
      if (total == 1)
         sprintf(name, "%s_entail_wit_%d", func_name, entailment_wit_cnt);
      else
         sprintf(name, "%s_entail_wit_%d_%d", func_name, entailment_wit_cnt, ++cnt);
      if (entailment_checker_wit->auto_solved) {
         CoqPrintSacProof(name, fp_auto);
      } else {
         CoqPrintSacProof(name, fp_manual);
      }
      CoqPrintSacEntailment(pre->head, entailment_checker_wit->post, 1, 1, 0, name, env, fp_goal);
   }
   free(name);
}

void CoqPrintSacSafetyCheckerWit(struct SafetyCheckerWit * safety_checker_wit, 
                                 struct environment * env, FILE * fp_goal, FILE * fp_auto, FILE * fp_manual) {
   if (safety_checker_wit == NULL) return;
   CoqPrintSacSafetyCheckerWit(safety_checker_wit->next, env, fp_goal, fp_auto, fp_manual);
   ++safety_wit_cnt;
   char * name = malloc(sizeof(char) * (strlen(func_name) + 30));
   sprintf(name, "%s_safety_wit_%d", func_name, safety_wit_cnt);
   struct Assertion * post = CreateAsrt();
   post->prop_list = safety_checker_wit->constraits;
   if (safety_checker_wit->auto_solved) {
      CoqPrintSacProof(name, fp_auto);
   } else {
      CoqPrintSacProof(name, fp_manual);
   }
   void * local = safety_checker_wit->asrt->local_list;
   safety_checker_wit->asrt->local_list = CreateLocalLinkedHashMap();
   struct AsrtList * post_list = AsrtListCons(post, AsrtListNil());
   CoqPrintSacEntailment(safety_checker_wit->asrt, post_list, 1, 0, 1, name, env, fp_goal);
   LocalLinkedHashMapFree(safety_checker_wit->asrt->local_list);
   safety_checker_wit->asrt->local_list = local;
   AsrtListFree(post_list);
   free(name);
}

void CoqPrintSacReturnCheckerWit(struct ReturnCheckWit * return_checker_wit, 
                                 struct environment * env, FILE * fp_goal, FILE * fp_auto, FILE * fp_manual) {
   if (return_checker_wit == NULL) return;
   CoqPrintSacReturnCheckerWit(return_checker_wit->next, env, fp_goal, fp_auto, fp_manual);
   ++return_wit_cnt;
   int total = 0;
   for (struct FuncRetType * pre = return_checker_wit->pre; pre != NULL; pre = pre->next) {
      ++total;
   }
   int cnt = 0;
   char * name = malloc(sizeof(char) * (strlen(func_name) + 40));
   struct IntListNode * auto_solved = return_checker_wit->auto_solved->head;
   for (struct FuncRetType * ret_pre = return_checker_wit->pre; ret_pre != NULL; ret_pre = ret_pre->next, auto_solved = auto_solved->next) {
      assert(auto_solved != NULL);
      struct Assertion * pre = AsrtDeepCopy(ret_pre->asrt);
      struct AsrtList * post = AsrtListNil();
      for (struct FuncRetType * ret_post = return_checker_wit->post; ret_post != NULL; ret_post = ret_post->next) {
         struct Assertion * tmp = AsrtDeepCopy(ret_post->asrt);
         if (ret_post->val != NULL) {
            tmp->exist_list = ExistListRemove(ret_post->val->d.FUNCAPP.id, tmp->exist_list);
            tmp = AsrtSubst(tmp, ret_post->val, ret_pre->val);
         }
         post = AsrtListCons(tmp, post);
      }
      post = AsrtListReverse(post);
      if (total == 1)
         sprintf(name, "%s_return_wit_%d", func_name, return_wit_cnt);
      else
         sprintf(name, "%s_return_wit_%d_%d", func_name, return_wit_cnt, ++cnt);
      if (auto_solved->data) {
         CoqPrintSacProof(name, fp_auto);
      } else {
         CoqPrintSacProof(name, fp_manual);
      }
      CoqPrintSacEntailment(pre, post, 0, 1, 1, name, env, fp_goal);
      AsrtListFree(post);
      AsrtFree(pre);
   }
   free(name);
}

void CoqPrintSacWhichImpliesWit(struct WhichImpliesWit * which_implies_wit, 
                                struct environment * env, FILE * fp_goal, FILE * fp_auto, FILE * fp_manual) {
   if (which_implies_wit == NULL) return;
   CoqPrintSacWhichImpliesWit(which_implies_wit->next, env, fp_goal, fp_auto, fp_manual);
   ++which_implies_wit_cnt;
   char * name = malloc(sizeof(char) * (strlen(func_name) + 30));
   int total = 0;
   for (struct AsrtList * pre = which_implies_wit->pre; pre != NULL; pre = pre->next) {
      ++total;
   }
   int cnt = 0;
   struct AsrtList * i1;
   struct IntListNode * autosolved;
   for (i1 = which_implies_wit->pre, autosolved = which_implies_wit->auto_solved->head;
        i1 != NULL; 
        i1 = i1->next, autosolved = autosolved->next) {
      if (total == 1)
         sprintf(name, "%s_which_implies_wit_%d", func_name, which_implies_wit_cnt);
      else
         sprintf(name, "%s_which_implies_wit_%d_%d", func_name, which_implies_wit_cnt, ++cnt);
      CoqPrintSacEntailment(i1->head, which_implies_wit->post, 1, 1, 0, name, env, fp_goal);
      if (autosolved->data) {
         CoqPrintSacProof(name, fp_auto);
      } else {
         CoqPrintSacProof(name, fp_manual);
      }
   }
   free(name);
}

void CoqPrintSacProofGoalImplies(char * name, char * pre, char * post, FILE * fp) {
   FPRINT(fp, "Definition %s := %s -> %s.\n\n", name, pre, post);
}

void CoqPrintSacPartialSolveWit(struct PartialSolveWit * partial_solve_wit, 
                                struct environment * env, FILE * fp_goal, FILE * fp_auto, FILE * fp_manual) {
   if (partial_solve_wit == NULL) return;
   CoqPrintSacPartialSolveWit(partial_solve_wit->next, env, fp_goal, fp_auto, fp_manual);
   ++partial_solve_wit_cnt;
   struct Assertion * pre = partial_solve_wit->pre;
   struct Assertion * post = partial_solve_wit->post;
   struct Assertion * frame = partial_solve_wit->frame;
   char * primary = malloc(sizeof(char) * (strlen(func_name) + 40));
   char * pure = malloc(sizeof(char) * (strlen(func_name) + 40));
   char * primary_aux = malloc(sizeof(char) * (strlen(func_name) + 40));
   sprintf(primary, "%s_partial_solve_wit_%d", func_name, partial_solve_wit_cnt);
   sprintf(pure, "%s_partial_solve_wit_%d_pure", func_name, partial_solve_wit_cnt);
   sprintf(primary_aux, "%s_partial_solve_wit_%d_aux", func_name, partial_solve_wit_cnt);
   if (post->prop_list == NULL) {
      CoqPrintSacProof(primary, fp_auto);
      struct Assertion * tmp = AsrtMerge(AsrtDeepCopy(post), AsrtDeepCopy(frame));
      struct AsrtList * tmp_list = AsrtListCons(tmp, AsrtListNil());
      CoqPrintSacEntailment(pre, tmp_list, 1, 1, 0, primary, env, fp_goal);
      AsrtListFree(tmp_list);
   } else {
      if (partial_solve_wit->auto_solved) {
         CoqPrintSacProof(pure, fp_auto);
      } else {
         CoqPrintSacProof(pure, fp_manual);
      }
      struct Assertion * tmp = AsrtDeepCopy(post);
      SepListFree(tmp->sep_list);
      tmp->sep_list = NULL;
      struct AsrtList * tmp_list = AsrtListCons(tmp, AsrtListNil());
      CoqPrintSacEntailment(pre, tmp_list, 1, 0, 0, pure, env, fp_goal);
      AsrtListFree(tmp_list);
      tmp = AsrtMerge(AsrtDeepCopy(post), AsrtDeepCopy(frame));
      tmp_list = AsrtListCons(tmp, AsrtListNil());
      CoqPrintSacEntailment(pre, tmp_list, 1, 1, 0, primary_aux, env, fp_goal);
      AsrtListFree(tmp_list);
      CoqPrintSacProofGoalImplies(primary, pure, primary_aux, fp_goal);
      CoqPrintSacProof(primary, fp_auto);
   }
   free(primary);
   free(pure);
   free(primary_aux);
}

void CoqPrintSacWitness(struct Witness * witness, struct environment * env, FILE * fp_goal, FILE * fp_auto, FILE * fp_manual) {
   entailment_wit_cnt = 0;
   return_wit_cnt = 0;
   safety_wit_cnt = 0;
   which_implies_wit_cnt = 0;
   partial_solve_wit_cnt = 0;
   FPRINT(fp_goal, "(*----- Function %s -----*)\n\n", func_name);
   CoqPrintSacSafetyCheckerWit(witness->safety_checker_wit, env, fp_goal, fp_auto, fp_manual);
   CoqPrintSacEntailmentCheckerWit(witness->entailment_checker_wit, env, fp_goal, fp_auto, fp_manual);
   CoqPrintSacReturnCheckerWit(witness->return_checker_wit, env, fp_goal, fp_auto, fp_manual);
   CoqPrintSacPartialSolveWit(witness->partial_solve_wit, env, fp_goal, fp_auto, fp_manual);
   CoqPrintSacWhichImpliesWit(witness->which_implies_wit, env, fp_goal, fp_auto, fp_manual);
}

void CoqPrintSacVCCorrectInit() {
   all_proof_goals = StringListNil();
}

void CoqPrintSacWitnessList(struct WitnessList * list, struct environment * env, FILE * fp_goal, FILE * fp_auto, FILE * fp_manual) {
   if (list == NULL) return;
   CoqPrintSacWitnessList(list->next, env, fp_goal, fp_auto, fp_manual);
   func_name = list->func_name;
   CoqPrintSacWitness(list->witness, env, fp_goal, fp_auto, fp_manual);
}

void CoqPrintSacVCCorrect(FILE * fp_goal) {
   CoqPrintDefineModuleType(fp_goal, "VC_Correct");
   if (strategy_gen) {
      for (struct StringListNode * i = all_strategy_libs->head; i != NULL; i = i->next) {
         char * name = getFileName(i->data);
         FPRINT(fp_goal, "Include %s_Strategy_Correct.\n", name);
         free(name);
      }
      FPRINT(fp_goal, "\n");
   }
   for (struct StringListNode * i = all_proof_goals->head; i != NULL; i = i->next) {
      FPRINT(fp_goal, "Axiom proof_of_%s : %s.\n", i->data, i->data);
   }
   FPRINT(fp_goal, "\n");
   CoqPrintEndModuleType(fp_goal, "VC_Correct");
}

/*
   forall X, {P1(X)} c {Q1(X)}
   implies
   forall Y, {P2(Y)} c {Q2(Y)}

   if
   forall Y, exists X,
   P2(Y) |-- P1(X) * frame /\ Q1(X) * frame |-- Q2(Y)

   if
   forall Y, 
   P2(Y) |-- exists X, (P1(X) * (Q1(X) -* Q2(Y)))
*/
void CoqPrintSacSpecDerivationAux(struct func_info * func_info, struct func_spec * spec, struct func_spec * from,
                                  struct environment * env, FILE * fp_goal, FILE * fp_manual) {
  char * name = malloc(sizeof(char) * (strlen(func_info->name) + strlen(spec->name) + strlen(from->name) + 20));
  sprintf(name, "%s_derive_%s_by_%s", func_info->name, spec->name, from->name);
  from = func_spec_deep_copy(from);
  struct hashtbl * tmp = create_hashtbl(hash_int, int_equal);
  for (struct prog_var_info_list * i = func_info->param; i != NULL; i = i->tail) {
    hashtbl_add(tmp, cast_int(i->head->value->id), cast_int(i->head->value->id));
  }
  cpa_rename_func_spec(from, tmp, &env->persist);
  CoqPrintSacProof(name, fp_manual);
  FPRINT(fp_goal, "Definition %s := \n", name);
  struct RealNameMapping * mapping = CreateRealNameMapping();
  CoqPrintSacGetRealNameInAsrtList(spec->pre, 1, mapping, env);
  CoqPrintSacGetRealNameInAsrtList(spec->post, 1, mapping, env);
  CoqPrintSacGetRealNameInAsrtList(from->pre, 1, mapping, env);
  CoqPrintSacGetRealNameInAsrtList(from->post, 1, mapping, env);
  struct ExistList * all_spec = ExistListUnique(ExistListLink(
                                  AsrtListCollectFreeVars(spec->pre, env),
                                  AsrtListCollectFreeVars(spec->post, env)));
  struct ExistList * all_from = ExistListUnique(ExistListLink(
                                  AsrtListCollectFreeVars(from->pre, env),
                                  AsrtListCollectFreeVars(from->post, env)));
  for (struct prog_var_info_list * i = func_info->param; i != NULL; i = i->tail) {
    all_from = ExistListRemove(i->head->value->id, all_from);
  }
  struct ExistList * type_vars1 = ExistListUnique(ExistListLink(
                                    AsrtListCollectTypeVars(spec->pre, env),
                                    AsrtListCollectTypeVars(spec->post, env)));
  struct ExistList * type_vars2 = ExistListUnique(ExistListLink(
                                    AsrtListCollectTypeVars(from->pre, env),
                                    AsrtListCollectTypeVars(from->post, env)));
  if (type_vars1 != NULL) {
    FPRINT(fp_goal, "forall ");
    for (struct ExistList * i = type_vars1; i != NULL; i = i->next) {
      FPRINT(fp_goal, "(");
      CoqPrintSacVari(i->id, env, mapping, fp_goal);
      FPRINT(fp_goal, ": Type) ");
    }
    FPRINT(fp_goal, ",\n");
  }
  int all_spec_counter = 0;
  for (struct ExistList * i = all_spec; i != NULL; i = i->next) {
    all_spec_counter += Not_Addr(i->id, env);
  }
  if (all_spec_counter) {
    FPRINT(fp_goal, "forall ");
    for (struct ExistList * i = all_spec; i != NULL; i = i->next) {
      if (Not_Addr(i->id, env)) {
        CoqPrintSacVardef(i->id, env, mapping, fp_goal);
      }
    }
    FPRINT(fp_goal, ",\n");
  }
  struct StringList * default_Typevars = AsrtListCollectDefaultTypeVars(spec->pre, env);
  default_Typevars = StringListUnique(StringListLink(default_Typevars, AsrtListCollectDefaultTypeVars(spec->post, env)));
  if (default_Typevars -> head != NULL) {
    FPRINT(fp_goal, "forall ");
    for (struct StringListNode * i = default_Typevars -> head; i != NULL; i = i->next) {
      FPRINT(fp_goal, "__default_%s ", i->data);
    }
    FPRINT(fp_goal, ",\n");
  }
  CoqPrintSacAsrtList(spec->pre, 1, "", "\n", env, mapping, fp_goal);
  FPRINT(fp_goal, "|--\n");
  if (type_vars2 != NULL) {
    FPRINT(fp_goal, "EX ");
    for (struct ExistList * i = type_vars2; i != NULL; i = i->next) {
      FPRINT(fp_goal, "(");
      CoqPrintSacVari(i->id, env, mapping, fp_goal);
      FPRINT(fp_goal, ": Type) ");
    }
    FPRINT(fp_goal, ",\n");
  }
  StringListFree(default_Typevars);
  default_Typevars = AsrtListCollectDefaultTypeVars(from->pre, env);
  default_Typevars = StringListUnique(StringListLink(default_Typevars, AsrtListCollectDefaultTypeVars(from->post, env)));
  if (default_Typevars -> head != NULL) {
    FPRINT(fp_goal, "EX ");
    for (struct StringListNode * i = default_Typevars -> head; i != NULL; i = i->next) {
      FPRINT(fp_goal, "__default_%s ", i->data);
    }
    FPRINT(fp_goal, ",\n");
  }
  int all_from_counter = 0;
  for (struct ExistList * i = all_from; i != NULL; i = i->next) {
    all_from_counter += Not_Addr(i->id, env);
  }
  if (all_from_counter) {
    FPRINT(fp_goal, "EX ");
    for (struct ExistList * i = all_from; i != NULL; i = i->next) {
      if (Not_Addr(i->id, env)) {
        CoqPrintSacVardef(i->id, env, mapping, fp_goal);
      }
    }
    FPRINT(fp_goal, ",\n");
  }
  CoqPrintSacAsrtList(from->pre, 1, "(", ")\n", env, mapping, fp_goal);
  FPRINT(fp_goal, "  **\n");   
  CoqPrintSacAsrtList(from->post, 1, "((", ")\n", env, mapping, fp_goal);
  FPRINT(fp_goal, "  -*\n");   
  CoqPrintSacAsrtList(spec->post, 1, "(", "))\n", env, mapping, fp_goal);
  FPRINT(fp_goal, ".\n\n");
  ExistListFree(all_spec);
  ExistListFree(all_from);
  ExistListFree(type_vars1);
  ExistListFree(type_vars2);
  StringListFree(default_Typevars);
}

void CoqPrintSacSpecDerivation(struct func_info * func_info, struct environment * env, FILE * fp_goal, FILE * fp_manual) {
   for (struct func_spec * spec = func_info->spec; spec != NULL; spec = spec->next) {
      if (spec->derived_by == NULL) continue;
      struct func_spec * from;
      for (from = func_info->spec; from != NULL && strcmp(spec->derived_by, from->name) != 0; from = from->next);
      if (from == NULL) {
         fprintf(stderr, "function spec %s is derived by %s, but %s is undefined.\n", spec->name, spec->derived_by, spec->derived_by);
         exit(1);
      }
      CoqPrintSacSpecDerivationAux(func_info, spec, from, env, fp_goal, fp_manual);
   }
}

void CoqPrintSacAllFuncDerivation(struct environment * env, FILE * fp_goal, FILE * fp_manual) {
   for (struct blist * i = env->persist.func.top; i != NULL; i = i->down) {
      CoqPrintSacSpecDerivation((struct func_info*) i->val, env, fp_goal, fp_manual);
   }
}

void DebugPrintRealNameMapping(struct RealNameMapping * mapping, struct environment * env) {
   printf("Printing RealNameMapping\n");
   for (struct blist * i = mapping->id_to_name->top; i != NULL; i = i->down) {
      char * env_name = find_logic_var_by_id(cast_void(i->key), &env->persist)->name;
      printf("%d -> %s, by env name is %s\n", cast_void(i->key), (char*)(i->val), env_name);
   }
   printf("---------------------------------\n");
}

char * GetStrategyFileName(char * file) {
   int len = strlen(file), l = len - 1;
   while (l >= 0 && file[l] != '/') l--;
   ++l;
   int r = l;
   while (r < len && file[r] != '.') r++;
   char * ret = malloc(r - l + 1);
   int i, j;
   for (i = 0, j = l; j < r; i++, j++)
      ret[i] = file[j];
   ret[i] = '\0';
   return ret;
}

void CoqPrintSacStrategySoundness(char * path, struct environment * env) {
   if (!strategy_gen) {
      printf("strategy soundness not generated\n");
      return ;
   }
   struct StrategyLib * lib = initStrategyLib();
   char * filename = GetStrategyFileName(path);
   for (struct StrategyLibNode * cur = strategyLibInScopes; cur != NULL; cur = cur->next) {
      for (int i = 0; i < STRATEGY_LIB_MAX_PRIORITY; i++)
         for (struct StrategyLibRuleList * icur = cur->lib->rules[i]->head; icur != NULL; icur = icur->next) {
            if (!strcmp(icur->rule->filename, filename))
               addStrategyLibRule(lib, icur->rule);
            }
   }
   if (strategy_folder_path == NULL) {
      fprintf(stderr, "strategy_folder_path is not set\n");  
      exit(1);
   }
   char * strategy_goal = malloc(strlen(strategy_folder_path) + strlen(filename) + 20);
   char * strategy_manual = malloc(strlen(strategy_folder_path) + strlen(filename) + 20);
   char * strategy_goal_check = malloc(strlen(strategy_folder_path) + strlen(filename) + 30);
   sprintf(strategy_goal, "%s/%s_strategy_goal.v", strategy_folder_path, filename);
   sprintf(strategy_goal_check, "%s/%s_strategy_goal_check.v", strategy_folder_path, filename);
   sprintf(strategy_manual, "%s/%s_strategy_proof.v", strategy_folder_path, filename);
   FILE * fp_goal = OpenFile(strategy_goal, 0, 1);
   FILE * fp_goal_check = OpenFile(strategy_goal_check, 0, 1);
   FILE * fp_manual = OpenFile(strategy_manual, backup, 0);
   if (fp_manual == NULL) {
      if (backup) {
         printf("Warning: manual proof file not updated. file open failed\n");
      } else {
         printf("Warning: manual proof file not updated. file open failed or file already exists.\n");
      }
   }
   print_strategy_soundness(lib, fp_goal, fp_manual, fp_goal_check, filename, env);
   free(strategy_goal);
   free(strategy_goal_check);
   free(strategy_manual);
}

void CoqPrintSacStructUnionName(struct struct_union_info * info, int with_quote, FILE * fp) {
   if (with_quote) FPRINT(fp, "\"");
   if (info->name[0] == '<') {
      FPRINT(fp, "annonymous_%d", info->id);
   } else {
      FPRINT(fp, "%s", info->name);
   }
   if (with_quote) FPRINT(fp, "\"");
}

void CoqPrintSacEnumName(struct enum_info * info, int with_quote, FILE * fp) {
   if (with_quote) FPRINT(fp, "\"");
   if (info->name[0] == '<') {
      FPRINT(fp, "annonymous_%d", info->id);
   } else {
      FPRINT(fp, "%s", info->name);
   }   
   if (with_quote) FPRINT(fp, "\"");
}

void CoqPrintSacFrontendType(struct type * type, FILE * fp) {
   if (type == NULL) return;
   switch (type->t) {
      case T_BASIC: {
         switch (type->d.BASIC.ty) {
            case T_VOID:
               FPRINT(stderr, "Void type not supported at %s %d\n", __FILE__, __LINE__);
               break;
            case T_CHAR:
               FPRINT(fp, "FET_char");
               break;
            case T_U8:
               FPRINT(fp, "FET_uchar");
               break;
            case T_SHORT:
               FPRINT(fp, "FET_short");
               break;
            case T_U16:
               FPRINT(fp, "FET_ushort");
               break;
            case T_INT:
               FPRINT(fp, "FET_int");
               break;
            case T_UINT:
               FPRINT(fp, "FET_uint");
               break;
            case T_INT64:
               FPRINT(fp, "FET_int64");
               break;
            case T_UINT64:
               FPRINT(fp, "FET_uint64");
               break;
            default:
               FPRINT(stderr, "Unknown basic type %d at %s %d\n", type->d.BASIC.ty, __FILE__, __LINE__);
               break;
         }
         break;
      }
      case T_STRUCT:
         FPRINT(fp, "FET_struct ");
         CoqPrintSacStructUnionName(type->d.STRUCT.info, 1, fp);
         break;
      case T_UNION:
         FPRINT(fp, "FET_union ");
         CoqPrintSacStructUnionName(type->d.UNION.info, 1, fp);
         break;
      case T_ENUM:
         FPRINT(fp, "FET_enum ");
         CoqPrintSacEnumName(type->d.ENUM.info, 1, fp);
         break;
      case T_PTR:
         FPRINT(fp, "FET_ptr");
         break;
      case T_ARRAY:
         FPRINT(fp, "FET_ptr");
         break;
      case T_FUNCTION:
         FPRINT(fp, "FET_ptr");
         break;
      case T_TYPE_ALIAS:
         FPRINT(fp, "FET_alias \"%s\"", type->d.TYPE_ALIAS.info->name);
         break;
      default:
         FPRINT(stderr, "Unknown type %d at %s %d\n", type->t, __FILE__, __LINE__);
         break;
   }
}

void CoqPrintSacFields(struct field_info * field, FILE * fp) {
   FPRINT(fp, "    (");
   while (field != NULL) {
      FPRINT(fp, "(\"%s\", ", field->name);
      CoqPrintSacFrontendType(field->type, fp);
      FPRINT(fp, ") :: ");
      field = field->next;
   }
   FPRINT(fp, "nil)");
}

void CoqPrintSacStructDefinitions(struct environment * env, FILE * fp) {
   for (struct blist * i = env->persist.structs.top; i != NULL; i = i->down) {
      struct struct_union_info * info = (struct struct_union_info*) i->val;
      FPRINT(fp, "Definition struct_");
      CoqPrintSacStructUnionName(info, 0, fp);
      FPRINT(fp, "_def : composite_definition :=\n");
      FPRINT(fp, "  Composite ");
      CoqPrintSacStructUnionName(info, 1, fp);
      FPRINT(fp, " Struct\n");
      CoqPrintSacFields(info->first_field, fp);
      FPRINT(fp, ".\n");
      if (i->next == NULL) {
         FPRINT(fp, "\n");
      }
   }
}

void CoqPrintSacUnionDefinitions(struct environment * env, FILE * fp) {
   for (struct blist * i = env->persist.unions.top; i != NULL; i = i->down) {
      struct struct_union_info * info = (struct struct_union_info*) i->val;
      FPRINT(fp, "Definition union_");
      CoqPrintSacStructUnionName(info, 0, fp);
      FPRINT(fp, "_def : composite_definition :=\n");
      FPRINT(fp, "  Composite ");
      CoqPrintSacStructUnionName(info, 1, fp);
      FPRINT(fp, " Union\n");
      CoqPrintSacFields(info->first_field, fp);
      FPRINT(fp, ".\n");
      if (i->next == NULL) {
         FPRINT(fp, "\n");
      }
   }
}

void CoqPrintCompositeDefinitions(struct environment * env, FILE * fp) {
   CoqPrintSacStructDefinitions(env, fp);
   CoqPrintSacUnionDefinitions(env, fp);
   FPRINT(fp, "Definition composites : list composite_definition :=\n");
   FPRINT(fp, "  ");
   for (struct blist * i = env->persist.structs.top; i != NULL; i = i->down) {
      struct struct_union_info * info = (struct struct_union_info*) i->val;
      FPRINT(fp, "struct_");
      CoqPrintSacStructUnionName(info, 0, fp);
      FPRINT(fp, "_def :: ");
   }
   for (struct blist * i = env->persist.unions.top; i != NULL; i = i->down) {
      struct struct_union_info * info = (struct struct_union_info*) i->val;
      FPRINT(fp, "union_");
      CoqPrintSacStructUnionName(info, 0, fp);
      FPRINT(fp, "_def :: ");
   }
   FPRINT(fp, "nil.\n\n");
}

void CoqPrintSacProgram(struct environment * env, FILE * fp) {
   CoqPrintCompositeDefinitions(env, fp);
}

#undef FPRINT
#undef OPEN_FILE_WRITE
