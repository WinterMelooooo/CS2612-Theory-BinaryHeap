#include <assert.h>
#include "FuncCall.h"
#include "../../compiler/cp.h"
#include "../Automation/AutomationSolver/solver.h"
#include "../Automation/AutomationSolver/CustomSolver.h"
#include "../Utility/InnerAsrtPrinter.h"
#include "../Automation/StrategyLibDef/AsrtUnify.h"
#include "../../compiler/utils.h"

// for debug
#ifdef FUNC_CALL_DEBUG
extern void PrintWitness(struct Witness * wit, struct environment * env);
#endif

int call_id;

extern unsigned int cpa_rename_logic_var(unsigned int id, struct persistent_env *env);

struct func_spec * DeclareSpec(struct ExistList *witht,
                           struct ExistList *with,
                           struct AsrtList *pre,
                           struct AsrtList *post,
                           struct ExprVal * __return,
                           struct qvar_list *qv) {
  struct func_spec *spec;
  spec = (struct func_spec *)malloc(sizeof(struct func_spec));
  spec->witht = witht;
  spec->with = with;
  spec->pre = pre;
  spec->post = post;
  spec->__return = __return;
  spec->qv = qv;
  spec->name = spec->derived_by = NULL;
  spec->next = NULL;
  return spec;
}

struct PrefillValue * PrefillExprVal(struct ExprVal * value) {
   struct PrefillValue * ret = (struct PrefillValue *) malloc(sizeof(struct PrefillValue));
   ret->t = PREFILL_EXPRVAL;
   ret->d.value = value;
   return ret;
}

struct PrefillValue * PrefillType(struct PolyType * type) {
   struct PrefillValue * ret = (struct PrefillValue *) malloc(sizeof(struct PrefillValue));
   ret->t = PREFILL_TYPE;
   ret->d.type = type;
   return ret;
}

struct EntailRetType* EntailRetTypeNil() {
   return NULL;
}

struct EntailRetType * CreateEntailRetType(struct Assertion * frame, 
                                           struct IntList * introed_vars, 
                                           struct hashtbl * ex_instance, 
                                           struct Witness * witness) {
   struct EntailRetType * ret = (struct EntailRetType *) malloc(sizeof(struct EntailRetType));
   ret->frame = frame;
   ret->introed_vars = introed_vars;
   ret->ex_instance = ex_instance;
   ret->witness = witness;
   return ret;
}

void EntailRetTypeFree(struct EntailRetType * ret) {
   if (ret == NULL) return;
   IntListFree(ret->introed_vars);
   if (ret->ex_instance != NULL) 
      free_hashtbl(ret->ex_instance);
   free(ret);
}

struct FuncCallRetType * CreateFuncCallRetType(struct ExprExecRetType * ret, struct hashtbl * ex_instance) {
   struct FuncCallRetType * res;
   res = (struct FuncCallRetType *) malloc(sizeof(struct FuncCallRetType));
   res->ret = ret;
   res->ex_instance = ex_instance;
   return res;
}

void FuncCallRetTypeFree(struct FuncCallRetType * ret) {
   if (ret == NULL) return;
   ExprExecRetTypeFree(ret->ret);
   if (ret->ex_instance != NULL) 
      free_hashtbl(ret->ex_instance);
   free(ret);
}

int GetReid(char * name, struct hashtbl * id_mapping, struct environment * env) {
   for (struct blist * it = id_mapping->top; it != NULL; it = it->down) {
      struct logic_var_info * var_info = find_logic_var_by_id((int) it->key, &env->persist);
      if (var_info != NULL) {
         if (strcmp(var_info->name, name) == 0) {
            return (int) it->val;
         }
      }
      struct atype_info * type_info = find_atype_by_id((int) it->key, &env->persist);
      if (type_info != NULL) {
         if (strcmp(type_info->name, name) == 0) {
            return (int) it->val;
         }
      }
   }
   return -1;
}

struct hashtbl* PrefillReid(struct hashtbl * prefill, struct hashtbl * id_mapping, struct environment * env) {
   struct hashtbl * ret = create_hashtbl(hash_int, int_equal);
   struct blist * iter;
   for (iter = prefill->top; iter != NULL; iter = iter->down) {
      int id = GetReid(iter->key, id_mapping, env);
      hashtbl_add(ret, (void *)id, iter->val);
   }
   hashtbl_clear(prefill);
   return ret;
}

/*
   Let pre := Pure1 && P1, post := Pure2 && P2
   Pure1 && P1 |-- Pure2 && P2 ** frame   ---(reduce)--->  Pure1 && Q1 |-- Pure2 ** frame
   Let frame := Q1

   will change the momory of pre and remove the momory of post
*/
struct EntailRetType * SepLogicEntail(struct Assertion * pre, 
                                      struct Assertion * post, 
                                      struct StringList * scopes,
                                      struct environment * env) {
   struct Assertion * ppre = AsrtDeepCopy(pre);
   struct Assertion * ppost = AsrtDeepCopy(post);
   struct ExistList * pex = ExistListDeepCopy(post->exist_list);
   struct EntailRetType * ret = custom_solve(pre, post, env, scopes);
   if (post -> sep_list != NULL || post -> exist_list != NULL) {
    struct EntailRetType * ret1 = asrt_unify(pre, post, env);
    if (ret1 != NULL) {
      struct blist * iter;
      for (iter = ret1->ex_instance->top; iter != NULL; iter = iter->down) {
        // printf("key: %d -> ", (int)iter->key);
        // PrintExprVal((struct ExprVal *)iter->val, env);
        // puts("");
        if (iter->val == NULL) {
          continue;
        }
        post->exist_list = ExistListRemove((int)iter->key, post->exist_list);
        hashtbl_add(ret->ex_instance, (void *)iter->key, iter->val);
      }
      EntailRetTypeFree(ret1);
    }
   }
   int fail = (post->sep_list != NULL);
   ExistListFree(pex);
   if (fail) {
      AsrtFree(ppre);
      AsrtFree(ppost);
      return NULL;
   }
   ExistListFree(pre->exist_list);
   pre->exist_list = NULL;
   struct EntailRetType * pcancel_ret = tag_cancel_solve(pre, post, env);
   EntailRetTypeFree(pcancel_ret);
   struct Prop_solver_return * prop_ret = PropEntail(pre->prop_list, post->prop_list, env);
   if (prop_ret->result == -1) {
      if (exec_info){
        printf("SMT find a False Prop.\n");
        printf("Source Proposition:\n");
        PrintPropList(pre->prop_list, env);
        printf("Target Proposition:\n");
        PrintPropList(prop_ret ->res_prop, env);
      }
      AsrtFree(ppre);
      AsrtFree(ppost);
      Prop_solver_return_free(prop_ret);
      return NULL;
   }
   int auto_solved = prop_ret->result;
   struct Assertion * frame = AsrtDeepCopy(pre);
   struct IntListNode *introed_vars = ret->introed_vars->head;
   while (introed_vars != NULL) {
      frame->exist_list = ExistListCons(introed_vars->data, frame->exist_list);
      introed_vars = introed_vars->next;
   }
   // now pre = Pure1 && Q1, frame = Q1
   struct ExistList * unfilled = ExistListNil();
   for (struct ExistList * i = ppost->exist_list; i != NULL; i = i->next) {
      int valid;
      struct ExprVal * val = hashtbl_find(ret->ex_instance, (void *)i->id, &valid);
      if (valid) {
         if (val != NULL) {
            ppost = AsrtSubst(ppost, ExprVal_V_VARI(i->id), val);
         } else {
            unfilled = ExistListCons(i->id, unfilled);
         }
      } else {
         fprintf(stderr, "Error: exist variable (id = %d) not instantiated\n", i->id);
         exit(1);
      }
   }
   ExistListFree(ppost->exist_list);
   ppost->exist_list = unfilled;
   struct Witness * witness = NewWitness();
   ppost->prop_list = PropListLink(ppost->prop_list, PropListDeepCopy(prop_ret->res_prop));
   Prop_solver_return_free(prop_ret);
   witness->partial_solve_wit = PartialSolveWitCons(ppre, ppost, frame, scopes, witness->partial_solve_wit);
   witness->partial_solve_wit->auto_solved = auto_solved; 
   ret->frame = pre;
   ret->witness = WitnessMerge(witness, ret->witness);
   if (exec_info){
     printf("=============================================================================================\n");
   }
   return ret;
}

/* will remove the momory of asrt */
struct FuncCallRetType * FuncCallExec(
            struct Assertion * asrt, struct environment * env, 
            struct prog_var_info_list *param, struct func_spec *spec, struct hashtbl * prefill,
            struct ExprValList * args, enum CallType call_type, struct StringList * scopes) {
   ++call_id;

   /* When verifying a function, we use the logical variables defined in the function-spec 
      for symbolic execution. This may lead to variable naming conflicts when symbolically 
      executing statements that call the function recursively. Therefore, it is necessary 
      to rename the variables in the function-spec.
      id_mapping is the mapping from the original variable IDs to the new variable IDs.
   */
   /* Due to the possibility of multiple specs for a function, the logical variables defined 
      in these specs may share the same name but have different IDs. Therefore, the prefill 
      passed to the function is a mapping from names to values. After variable renaming, we 
      can adjust it to a mapping from IDs to values.
   */
#ifdef FUNC_CALL_DEBUG
   printf("Precondition before reid :\n");
   PrintAsrt(spec->pre->head, env);
   printf("Postcondition before reid:\n");
   PrintAsrtList(spec->post, env);
#endif

   // for FuncCallWit
   struct ExprValList * arg_vals = ExprValListNil();
   struct ExprValList * with_vals = ExprValListNil();
   struct ExprValList * param_vals = ExprValListNil();
   struct ExistList * post_exist_inst = ExistListNil();

   struct hashtbl * id_mapping = create_hashtbl(hash_int, int_equal);
   for (struct prog_var_info_list * i = param; i != NULL; i = i->tail) {
      int vid = i->head->value->id;
      int new_id = cpa_rename_logic_var(vid, &env->persist);
      hashtbl_add(id_mapping, (void *)vid, (void *)new_id);
   }
   for (struct ExistList * i = spec->witht; i != NULL; i = i->next) {
      hashtbl_add(id_mapping, (void *)i->id, (void *)i->id);
   }
   struct func_spec * origin_spec = spec;
   spec = func_spec_deep_copy(origin_spec);
   cpa_rename_func_spec(spec, id_mapping, &env->persist);

#ifdef FUNC_CALL_DEBUG
   printf("spec with list:\n");
   PrintExistList(spec->with, env);
   printf("spec witht list:\n");
   PrintExistList(spec->witht, env);
#endif

   if (prefill != NULL) {
      #ifdef FUNC_CALL_DEBUG   
         printf("Prefill before reid:\n");
         PrintPrefillCharIndex(prefill, env);
      #endif

      prefill = PrefillReid(prefill, id_mapping, env);

      #ifdef FUNC_CALL_DEBUG 
         printf("Prefill after reid:\n");
         PrintPrefillIntIndex(prefill, env);
      #endif

      for (struct blist * it = prefill->top; it != NULL; it = it->down) {
         int id = (int) it->key;
         struct PrefillValue * val = (struct PrefillValue *) it->val;
         #ifdef FUNC_CALL_DEBUG
            printf("Prefill variable %d with type %d with value ", id, val->t);
            if (val->t == PREFILL_EXPRVAL) {
               PrintExprVal(val->d.value, env);
            } else {
               PrintPolyType(val->d.type, env);
            }
            printf("\n");
         #endif 
         if (val->t == PREFILL_EXPRVAL) {
            spec->with = ExistListRemove(id, spec->with);
            spec->pre->head->exist_list = ExistListRemove(id, spec->pre->head->exist_list);
            spec->pre->head = AsrtSubst(spec->pre->head, ExprVal_V_VARI(id), val->d.value);
            spec->post = AsrtListSubst(spec->post, ExprVal_V_VARI(id), val->d.value);
         } else {
            spec->witht = ExistListRemove(id, spec->witht);
            spec->pre->head = AsrtSubstPolyType(spec->pre->head, PolyTypeFuncApp(id, PolyTypeListNil()), val->d.type, &env->persist);
            spec->post = AsrtListSubstPolyType(spec->post, PolyTypeFuncApp(id, PolyTypeListNil()), val->d.type, &env->persist);
         }
      }
   }
   if (spec->witht != NULL) {
      fprintf(stderr, "Error: Need to Fill the Type Arguments.\n");
      PrintExistListFile(spec->witht, env,stderr);
      exit(1);
   }

   if (spec->witht != NULL) {
      fprintf(stderr, "Error: Need to Fill the Type Arguments.\n");
      PrintExistListFile(spec->witht, env,stderr);
      exit(1);
   }

   struct ExprExecRetType * ret = NewExprExecRetType();
   struct Assertion * precond = AsrtDeepCopy(spec->pre->head);
   struct AsrtList * postcond = AsrtListDeepCopy(spec->post);

   struct ExprValListNode * arg_iter;
   struct prog_var_info_list * annot_iter;

#ifdef FUNC_CALL_DEBUG
   printf("Precondition:\n");
   PrintAsrt(precond, env);
   printf("Postcondition:\n");
   PrintAsrtList(postcond, env);
   printf("Arguments:\n");
   for (arg_iter = args->head; arg_iter != NULL; arg_iter = arg_iter->next) {
      PrintExprVal(arg_iter->data, env);
      if (arg_iter->next != NULL) {
         printf(", ");
      } else {
         printf("\n");
      }
   }
   printf("Formal parameters:\n"); 
   for (annot_iter = param; annot_iter != NULL; annot_iter = annot_iter->tail) {
      struct prog_var_info * var;
      var = find_prog_var_by_id(annot_iter->head->id, &env->persist);
      printf("%s: %d", annot_iter->head->name, var->id);
      int valid;
      int new_id = hashtbl_find(id_mapping, var->value->id, &valid);
      printf(", with pre value : %d, now value %d", var->value->id, new_id);
      printf("\n");
   }
#endif

   // Substitute the formal parameters with actual parameters
   arg_iter = args->head;
   annot_iter = param;
   while (arg_iter != NULL) {
      struct ExprVal * pre;
      struct prog_var_info * var = find_prog_var_by_id(annot_iter->head->id, &env->persist);
      int valid;
      int new_value_id = (int)hashtbl_find(id_mapping, (void *)var->value->id, &valid);
      pre = ExprVal_V_VARI(new_value_id);
      precond = AsrtSubst(precond, pre, arg_iter->data);
      precond->exist_list = ExistListRemove(new_value_id, precond->exist_list);
      spec->with = ExistListRemove(new_value_id, spec->with);
      for (struct AsrtList * asrt_iter = postcond; asrt_iter != NULL; asrt_iter = asrt_iter->next) {
         asrt_iter->head = AsrtSubst(asrt_iter->head, pre, arg_iter->data);
         asrt_iter->head->exist_list = ExistListRemove(new_value_id, asrt_iter->head->exist_list);
         spec->with = ExistListRemove(new_value_id, spec->with);
      }
      param_vals = ExprValListSnoc(pre, param_vals);
      arg_vals = ExprValListSnoc(ExprValDeepCopy(arg_iter->data), arg_vals);
      arg_iter = arg_iter->next;
      annot_iter = annot_iter->tail;
   }

#ifdef FUNC_CALL_DEBUG
   printf("Precondition after substitution:\n");
   PrintAsrt(precond, env);
   printf("Postcondition after substitution:\n");
   PrintAsrtList(postcond, env);
   printf("With variables after substitution:\n");
   PrintExistList(spec->with, env);
#endif

   // Recognize variables in with_list as existential variables
   precond->exist_list = ExistListLink(precond->exist_list, ExistListDeepCopy(spec->with));

#ifdef FUNC_CALL_DEBUG
   printf("Precondition after adding exist variables:\n");
   PrintAsrt(precond, env);
#endif 

   // precond is non-addressable assertion, so clear the local
   LocalLinkedHashMapFree(precond->local_list);
   precond->local_list = CreateLocalLinkedHashMap();

#ifdef FUNC_CALL_DEBUG
   printf("Precondition after clearing local:\n");
   PrintAsrt(precond, env);
#endif 

   // Entail the precond
   struct EntailRetType *entail_ret = NULL;
   entail_ret = SepLogicEntail(AsrtDeepCopy(asrt), precond, scopes, env);
   AsrtFree(precond);
   if (entail_ret == NULL) return NULL;
   ret->witness = WitnessMerge(entail_ret->witness, ret->witness);

   struct AsrtList * post_iter;
   post_iter = postcond;
   while (post_iter != NULL) {
      struct Assertion * frame = entail_ret->frame;
      struct Assertion * func_post = AsrtDeepCopy(post_iter->head);
#ifdef FUNC_CALL_DEBUG
      printf("Process Postcondition:\n");
      PrintAsrt(func_post, env);
      printf("Frame:\n");
      PrintAsrt(frame, env);
#endif
      struct ExprVal * ret_val = NULL;
      struct IntList * introed_vars = entail_ret->introed_vars; 
      // Substitute the with variables in postcond
      for (struct ExistList * exist_iter = spec->with; exist_iter != NULL; exist_iter = exist_iter->next) {
         int valid;
         struct ExprVal * val = hashtbl_find(entail_ret->ex_instance, (void *)exist_iter->id, &valid);
         //printf("exist_iter->id = %d\n", exist_iter->id);
         //PrintExprVal(val, env);
         if (valid && val != NULL) {
            with_vals = ExprValListSnoc(ExprValDeepCopy(val), with_vals);
            func_post = AsrtSubst(func_post, ExprVal_V_VARI(exist_iter->id), val);
            if (spec->__return != NULL && exist_iter->id == spec->__return->d.FUNCAPP.id) {
               ret_val = ExprValDeepCopy(val);
            }
         } else {
            fprintf(stderr, "Error: with variable (id = %d) not instantiated\n", exist_iter->id);
            exit(1);
         }
      }
#ifdef FUNC_CALL_DEBUG
      printf("After substitute the with variables in postcond:\n");
      PrintAsrt(func_post, env);
#endif
      /* Consider the following function spec:
            void * malloc_int_array(int s)
            @Require: s > 0
            @Ensure:  exists p, undef_store_int_array(p, s)
         Every time we call malloc_int_array, we expect to get a *new* pointer p that points to an 
         array of integers of size size.
         So it is necessary to introduce new variables corresponding to the existential variables 
         in the postcondition.
         Be careful when tackling renaming info.
      */
      for (struct ExistList * exist_iter = func_post->exist_list; exist_iter != NULL; exist_iter = exist_iter->next) {
         struct ExprVal * pre = ExprVal_V_VARI(exist_iter->id);
         int found;
         struct ExprVal * post = hashtbl_find(entail_ret->ex_instance, (void *)exist_iter->id, &found);
         struct logic_var_info * origin = find_logic_var_by_id(exist_iter->id, &env->persist);
         assert(origin != NULL && origin->atype != NULL);
         struct logic_var_info * new_var = add_anonymous_logic_var(LOGIC_USER_EXISTS, origin->name, &env->persist);
         new_var->atype = atype_deep_copy(origin->atype);
         if (origin->renaming != NULL) {
            new_var->renaming = renaming_info_deep_copy(origin->renaming);
         } else if (new_var->name != NULL) {
            switch (call_type) {
               case NORMAL_CALL:
                  new_var->renaming = renaming_info_post_introed(new_var->name, call_id);
                  break;
               case FIELD_CALL:
                  new_var->renaming = renaming_info_free_var("field");
                  break;
               default:
                  new_var->renaming = renaming_info_free_var(new_var->name);
                  break;
            }
         } else {
            new_var->renaming = NULL;
         }
         int id = new_var->id;
         post_exist_inst = ExistListCons(id, post_exist_inst);
         post = ExprVal_V_VARI(id);
         func_post = AsrtSubst(func_post, pre, post);
         if (ExprValCheckEqual(pre, spec->__return)) {
            ret_val = ExprValDeepCopy(post);
         }
         ExprValFree(pre);
      }
      post_exist_inst = ExistListReverse(post_exist_inst);
#ifdef FUNC_CALL_DEBUG
      printf("After instantiate the exist variables in postcond:\n");
      PrintAsrt(func_post, env);
#endif
      // Merge the frame and postcond
      func_post = AsrtMerge(func_post, AsrtDeepCopy(frame));
      struct Assertion * asrt_tmp = AsrtDeepCopy(asrt);
      struct EntailRetType * Pcancel_ret = prop_cancel_solve(asrt_tmp, func_post, env);    
      AsrtFree(asrt_tmp);
      EntailRetTypeFree(Pcancel_ret);
#ifdef FUNC_CALL_DEBUG
      printf("After merge the frame and postcond:\n");
      PrintAsrt(func_post, env);
#endif
      ret->ret_value = ExprExecRetValueCons(func_post, ret_val, PropListNil(), IntListDeepCopy(introed_vars), ret->ret_value);
      post_iter = post_iter->next;
   }
#ifdef FUNC_CALL_DEBUG
    printf("After processing all postconditions:\n");
    for (struct ExprExecRetValue * iter = ret->ret_value; iter != NULL; iter = iter->next) {
       printf("============================================================\n");
       PrintAsrt(iter->asrt, env);
       printf("============================================================\n");
    }
#endif
   if (call_type == PREFILL_CALL) {
      struct hashtbl * ex_instance = create_hashtbl(hash_int, int_equal);
      for (struct ExistList * it = origin_spec->with; it != NULL; it = it->next) {
         int id = it->id, valid, new_id;
         new_id = (int)hashtbl_find(id_mapping, (void *)id, &valid);
         assert(valid);
         struct ExprVal * val = hashtbl_find(entail_ret->ex_instance, (void *)new_id, &valid);
         assert(valid);
         hashtbl_add(ex_instance, (void *)id, ExprValDeepCopy(val));
      }
      struct FuncCallRetType * func_ret = CreateFuncCallRetType(ret, ex_instance);
      EntailRetTypeFree(entail_ret);
      return func_ret;
   }
   ret->witness->func_call_wit = FuncCallWitCons(spec, param_vals, arg_vals, with_vals, 
                                                 AsrtDeepCopy(asrt), AsrtDeepCopy(entail_ret->frame),
                                                 post_exist_inst, ret->witness->func_call_wit);
   AsrtFree(asrt);
   EntailRetTypeFree(entail_ret);
   return CreateFuncCallRetType(ret, NULL);
}

struct WhichImpliesRetType * CreateWhichImpliesRetType(struct AsrtList * asrt, struct Witness * witness) {
   struct WhichImpliesRetType * ret = (struct WhichImpliesRetType *) malloc(sizeof(struct WhichImpliesRetType));
   ret->asrt = asrt;
   ret->witness = witness;
   return ret;
}

struct WhichImpliesRetType * WhichImpliesRetTypeMerge(struct WhichImpliesRetType * w1, struct WhichImpliesRetType * w2) {
   if (w1 == NULL) return w2;
   if (w2 == NULL) return w1;
   w1->asrt = AsrtListLink(w1->asrt, w2->asrt);
   w1->witness = WitnessMerge(w1->witness, w2->witness);
   free(w2);
   return w1;
}

void WhichImpliesRetTypeFree(struct WhichImpliesRetType * ret) {
   if (ret == NULL) return;
   AsrtListFree(ret->asrt);
   if (ret->witness != NULL) 
      WitnessFree(ret->witness);
   free(ret);
}

struct WhichImpliesRetType * PartialSolveSingleImplies(struct Assertion * pre, 
                                                       struct func_spec * specs, 
                                                       struct StringList * scopes,
                                                       struct environment * env, enum CallType call_type) {
  struct WhichImpliesRetType * Wiret = NULL;
  if (exec_info) {
    printf("-----------This is the Partial Solve Spec to be Implies-----------\n");
  }
  struct func_spec * spec = DeclareSpec(ExistListNil(), ExistListDeepCopy(specs->with), 
                                        AsrtListDeepCopy(specs->pre),
                                        AsrtListDeepCopy(specs->post), NULL, NULL);
  struct FuncCallRetType * func_call_ret = FuncCallExec(AsrtDeepCopy(pre), env, VILNil(), 
                                                        spec, NULL, ExprValListNil(), call_type, scopes);
  free_spec(spec);
  if (exec_info) {
      printf("------------The result is %s------------------------------------------\n", func_call_ret == NULL ? "Fail" : "SUCCESS");
  }
  if (func_call_ret != NULL) {
    struct AsrtList *ret = NULL;
    for (struct ExprExecRetValue * iter = func_call_ret->ret->ret_value; iter != NULL; iter = iter->next) {
      ret = AsrtListCons(AsrtDeepCopy(iter->asrt), ret);
    }
    struct Witness * wit = func_call_ret->ret->witness;
    func_call_ret->ret->witness = NULL;
    FuncCallRetTypeFree(func_call_ret);
    Wiret = WhichImpliesRetTypeMerge(Wiret, CreateWhichImpliesRetType(ret, wit));
  }
  return Wiret;
}

void PrintPartialSolveImpliesError(struct Assertion * pre, 
                                   struct func_spec * specs, 
                                   struct StringList * scopes,
                                   struct environment * env, enum CallType call_type) {
    printf("-----------This is the assertion that Partial Solve Failed-----------\n");
    struct func_spec * spec = DeclareSpec(ExistListNil(), ExistListDeepCopy(specs->with), 
                                          AsrtListDeepCopy(specs->pre),
                                          AsrtListDeepCopy(specs->post), NULL, NULL);
    exec_info = 1;
    struct FuncCallRetType * func_call_ret = FuncCallExec(AsrtDeepCopy(pre), env, VILNil(), 
                                                          spec, NULL, ExprValListNil(), call_type, scopes);
    free_spec(spec);
    if (func_call_ret != NULL) {
        FuncCallRetTypeFree(func_call_ret);
    }
    exec_info = 0;
    printf("-----------------------------------------------------------------------------\n");
}


struct WhichImpliesRetType * PartialSolveImplies(struct AsrtList * pre, 
                                                 struct func_spec * specs, 
                                                 struct StringList * scopes,
                                                 struct environment * env) {
  struct AsrtList *cur = pre;
  struct func_spec * cur_spec = specs;
  struct WhichImpliesRetType *ret = NULL;
  int cnt = 0;
  int cnt_spec = 0;
  for (struct AsrtList * i = pre; i != NULL; i = i->next) {
    cnt = cnt + 1;
  }
  for (struct func_spec * i = specs; i != NULL; i = i->next) {
    cnt_spec = cnt_spec + 1;
  }
  if (cnt != cnt_spec && cnt_spec != 1) {
    fprintf(stderr, "The number of now assertions and which implies pre assertions does not match. \n");
    exit(1);
  }
  cnt = 1;
  while (cur != NULL) {
    if (exec_info) {
      printf("-----------This is the %d-%s assertion try to do Which Implies -----------\n", cnt, cnt == 1 ? "st" : (cnt == 2 ? "nd" : (cnt == 3 ? "rd" : "th")));
      PrintAsrt(cur->head, env);
    }
    struct WhichImpliesRetType *now_ret = PartialSolveSingleImplies(cur->head, cur_spec, scopes, env, WHICH_IMPLIES_CALL);
    if (exec_info) {
      printf("-----------This is the %d-%s assertion %s for Which Implies -----------\n", cnt, cnt == 1 ? "st" : (cnt == 2 ? "nd" : (cnt == 3 ? "rd" : "th")), now_ret == NULL ? "Fail" : "SUCCESS");
    }
    if (now_ret == NULL) {
        fprintf(stderr,"Partial Solve Failed for Which Implies\n");
        fprintf(stderr, "Here are the checked results:\n");
        PrintPartialSolveImpliesError(cur->head, cur_spec, scopes, env, WHICH_IMPLIES_CALL);
        if (cur -> next != NULL) {
            fprintf(stderr, "The remaining assertions have not been checked.\n");
        }
        failwith("Finish Printing Partial Solve Which Implies Error\n"); 
    } 
    cur = cur->next;
    if (cnt_spec != 1) cur_spec = cur_spec->next;
    ret = WhichImpliesRetTypeMerge(ret, now_ret);
    cnt = cnt + 1;
  }
  if (exec_info)
  printf("Partial Solve Which Implies Done\n");
  return ret;
}

/* Notes: the difference between Partial invariant and Partial Assert
   both of them will be transformed to the form of 
      P which implies P
   but for a program variable i, Partial Inv i < n means: every time executing to the program point, i < n
   but for Partial Assert i < n, it means: When sequentially executing to the program point, i < n
   so Partial Inv i < n should later be transformed to:
      exists i. i < n which implies exists i. i < n
   and Partial Assert i < n should later be transformed to:
      With i
      i < n which implies i < n
*/
struct WhichImpliesRetType * PartialSolveSingleInv(struct Assertion * pre, 
                                             struct Assertion * post, 
                                             struct StringList * scopes,
                                             struct environment * env) {
  struct func_spec * spec = DeclareSpec(ExistListNil(), ExistListNil(),
                                          AsrtListCons(AsrtDeepCopy(post), AsrtListNil()),
                                          AsrtListCons(AsrtDeepCopy(post), AsrtListNil()), NULL, NULL);
  struct WhichImpliesRetType *ret = PartialSolveSingleImplies(pre, spec, scopes, env, PARTIAL_CALL);
  free_spec(spec);  
  return ret;
}

void PrintPartialSolveInvError(struct Assertion *pre, struct Assertion *post, struct StringList *scopes, struct environment *env) {
  struct func_spec * spec = DeclareSpec(ExistListNil(), ExistListNil(),
                                          AsrtListCons(AsrtDeepCopy(post), AsrtListNil()),
                                          AsrtListCons(AsrtDeepCopy(post), AsrtListNil()), NULL, NULL);
  PrintPartialSolveImpliesError(pre, spec, scopes, env, PARTIAL_CALL);
  free_spec(spec);  
}

struct WhichImpliesRetType * PartialSolveInv(struct AsrtList * pre, 
                                             struct AsrtList * post, 
                                             struct StringList * scopes,
                                             struct environment * env) {
    struct AsrtList *cur_pre = pre;
    struct AsrtList *cur_post = post;
    struct WhichImpliesRetType *ret = NULL;
    int cnt = 0;
    for (struct AsrtList * i = pre; i != NULL; i = i->next) {
      cnt = cnt + 1;
    }
    for (struct AsrtList * i = post; i != NULL; i = i->next) {
      cnt = cnt - 1;
    }
    if (cnt != 0) {
      fprintf(stderr, "The number of now assertions and loop inv pre assertions does not match. \n");
      exit(1);
    }
    cnt = 1;
    while (cur_pre != NULL) {
      if (exec_info) {
        printf("-----------This is the %d-%s assertion try to do Partial Inv Check -----------\n", cnt, cnt == 1 ? "st" : (cnt == 2 ? "nd" : (cnt == 3 ? "rd" : "th")));
        PrintAsrt(cur_pre->head, env);
      }
      struct WhichImpliesRetType *now_ret = PartialSolveSingleInv(cur_pre->head, cur_post->head, scopes, env);
      if (now_ret == NULL) {
          fprintf(stderr,"Partial Solve Failed for Partial Invariant\n");
          fprintf(stderr, "Here are the checked results:\n");
          PrintPartialSolveInvError(cur_pre->head, cur_post->head, scopes, env);
          if (cur_pre -> next != NULL) {
              fprintf(stderr, "The remaining assertions have not been checked.\n");
          }
          fprintf(stderr, "Finish Printing Partial Solve Invariant Error\n");
          exit(1);
      } 
      cur_pre = cur_pre->next;
      cur_post = cur_post->next;
      ret = WhichImpliesRetTypeMerge(ret, now_ret);
      cnt = cnt + 1;
    }
    if (exec_info)
    printf("Partial Solve Invariant Done\n");
    return ret;
}

struct WhichImpliesRetType * PartialSolveSingleAssert(struct Assertion * pre, 
                                                struct Assertion * post, 
                                                struct StringList * scopes,
                                                struct environment * env) {
  struct ExistList * with = ExistListNil();
  struct Assertion * cur_post = AsrtDeepCopy(post);
  for (struct ExistList * i = cur_post->exist_list; i != NULL; i = i->next) {
    struct logic_var_info * var_info = find_logic_var_by_id(i->id, &env->persist);
    if (var_info->category == LOGIC_GEN_EXISTS) {
      with = ExistListCons(i->id, with);
    }
  }
  with = ExistListUnique(with); // maybe this is a unnecessary step
  for (struct ExistList * j = with; j != NULL; j = j->next) {
    cur_post->exist_list = ExistListRemove(j->id, cur_post->exist_list);
  }
  // this step change the LOGIC_GEN_EXISTS into With, which means it will change the value of the variable after partial solve
  struct func_spec * spec = DeclareSpec(ExistListNil(), with,
                                        AsrtListCons(AsrtDeepCopy(cur_post), AsrtListNil()),
                                        AsrtListCons(cur_post, AsrtListNil()), NULL, NULL);
  struct WhichImpliesRetType *ret = PartialSolveSingleImplies(pre, spec, scopes, env, PARTIAL_CALL);
  free_spec(spec);  
  return ret; 
}

void PrintPartialSolveAssertError(struct Assertion *pre, struct Assertion *post, struct StringList *scopes, struct environment *env) {
  struct ExistList * with = ExistListNil();
  struct Assertion * cur_post = AsrtDeepCopy(post);
  for (struct ExistList * i = cur_post->exist_list; i != NULL; i = i->next) {
    struct logic_var_info * var_info = find_logic_var_by_id(i->id, &env->persist);
    if (var_info->category == LOGIC_GEN_EXISTS) {
      with = ExistListCons(i->id, with);
    }
  }
  with = ExistListUnique(with); // maybe this is a unnecessary step
  for (struct ExistList * j = with; j != NULL; j = j->next) {
    cur_post->exist_list = ExistListRemove(j->id, cur_post->exist_list);
  }
  // this step change the LOGIC_GEN_EXISTS into With, which means it will change the value of the variable after partial solve
  struct func_spec * spec = DeclareSpec(ExistListNil(), with,
                                        AsrtListCons(AsrtDeepCopy(cur_post), AsrtListNil()),
                                        AsrtListCons(cur_post, AsrtListNil()), NULL, NULL);
  PrintPartialSolveImpliesError(pre, spec, scopes, env, PARTIAL_CALL);
  free_spec(spec);  
}

struct WhichImpliesRetType * PartialSolveAssert(struct AsrtList * pre, 
                                             struct AsrtList * post, 
                                             struct StringList * scopes,
                                             struct environment * env) {
    struct AsrtList *cur_pre = pre;
    struct AsrtList *cur_post = post;
    struct WhichImpliesRetType *ret = NULL;
    int cnt = 0;
    int cnt_spec = 0;
    for (struct AsrtList * i = pre; i != NULL; i = i->next) {
      cnt = cnt + 1;
    }
    for (struct AsrtList * i = post; i != NULL; i = i->next) {
      cnt_spec = cnt_spec + 1;
    }
    if (cnt != cnt_spec && cnt_spec != 1) {
      fprintf(stderr, "The number of now assertions and partial assertions does not match. \n");
      exit(1);
    }
    cnt = 1;
    while (cur_pre != NULL) {
        if (exec_info) {
          printf("-----------This is the %d-%s assertion try to do Partial Assert Check -----------\n", cnt, cnt == 1 ? "st" : (cnt == 2 ? "nd" : (cnt == 3 ? "rd" : "th")));
          PrintAsrt(cur_pre->head, env);
        }
        struct WhichImpliesRetType *now_ret = PartialSolveSingleAssert(cur_pre->head, cur_post->head, scopes, env);
        if (now_ret == NULL) {
            fprintf(stderr,"Partial Solve Failed for Partial Assertion\n");
            fprintf(stderr, "Here are the checked results:\n");
            PrintPartialSolveAssertError(cur_pre->head, cur_post->head, scopes, env);
            if (cur_pre -> next != NULL) {
                fprintf(stderr, "The remaining assertions have not been checked.\n");
            }
            fprintf(stderr, "Finish Printing Partial Solve Assertion Error\n");
            exit(1);
        } 
        cur_pre = cur_pre->next;
        if (cnt_spec != 1) cur_post = cur_post->next;
        ret = WhichImpliesRetTypeMerge(ret, now_ret);
        cnt = cnt + 1;
    }
    if (exec_info)
    printf("Partial Solve Assert Done\n");
    return ret;
}

struct ExprExecRetType * GetFuncPrefill(struct Assertion * asrt, struct VirtArg * varg, struct hashtbl * prefill, struct environment * env) {
   if (varg == NULL) {
      AsrtFree(asrt);
      struct ExprExecRetType * ret = NewExprExecRetType();
      ret->ret_value = ExprExecRetValueCons(CreateAsrt(), NULL, PropListNil(), IntListNil(), ret->ret_value);
      return ret;
   }
   

#ifdef PREFILL_DEBUG
   printf("enter GetFuncPrefill\n");
   printf("Assertion: \n");
   PrintAsrt(asrt, env);
   printf("Function Spec: \n");
   PrintFuncSpec(varg->ctx, env);
   printf("Arguments: \n");
   for (struct VirtArgListNode * va = varg->args->head; va != NULL; va = va->next) {
      printf("%s: ", va->name);
      PrintExprVal(va->val, env);
      printf("\n");
   }
#endif 
   struct FuncCallRetType * ret = FuncCallExec(asrt, env, VILNil(), varg->ctx, NULL, ExprValListNil(), PREFILL_CALL, NULL);
   if (ret->ret->ret_value->next != NULL) {
      fprintf(stderr, "Error: multiple branches not allowed in prefill\n");
      exit(1);
   }
   struct hashtbl * ex_instance = ret->ex_instance;
#ifdef PREFILL_DEBUG
   printf("ex_instance:\n");
   for (struct blist * iter = ex_instance->top; iter != NULL; iter = iter->down) {
      printf("%d: ", (int) iter->key);
      PrintExprVal((struct ExprVal *) iter->val, env);
      printf("\n");
   }
#endif
   for (struct VirtArgListNode * va = varg->args->head; va != NULL; va = va->next) {
      struct ExprVal * val = ExprValDeepCopy(va->val);
      for (struct ExistList * iter = varg->ctx->with; iter != NULL; iter = iter->next) {
         int valid;
         struct ExprVal * post = hashtbl_find(ex_instance, (void *)iter->id, &valid);
         if (!valid) {
            struct logic_var_info * var = find_logic_var_by_id(iter->id, &env->persist);
            fprintf(stderr, "Prefill Evaluation failed: variable (id = %d) not instantiated\n", iter->id);
            struct ExprVal * tmp = ExprVal_V_VARI(iter->id);
            PrintExprVal(tmp, env); 
            printf("\n");
            ExprValFree(tmp);
            exit(0);
         }
         val = ExprValSubst(val, ExprVal_V_VARI(iter->id), post);
      }
      hashtbl_add(prefill, va->name, PrefillExprVal(val));
   }
   for (struct TypeArgListNode * arg = varg->type_args->head; arg != NULL; arg = arg->next) {
      hashtbl_add(prefill, arg->name, PrefillType(PolyTypeDeepCopy(arg->type)));
   }

#ifdef PREFILL_DEBUG
   printf("exit GetFuncPrefill\n");
   printf("Assertion: \n");
   PrintAsrt(ret->ret->ret_value->asrt, env);
   PrintPrefillCharIndex(prefill, env);
#endif
   free_hashtbl(ret->ex_instance);
   struct ExprExecRetType * tmp = ret->ret;
   free(ret);
   return tmp;
}

void PrintPrefillCharIndex(struct hashtbl * prefill, struct environment * env) {
   printf("Prefill:\n");
   for (struct blist * iter = prefill->top; iter != NULL; iter = iter->down) {
      printf("%s: ", (char *) iter->key);
      struct PrefillValue * val = (struct PrefillValue *) iter->val;
      if (val->t == PREFILL_EXPRVAL) {
         PrintExprVal(val->d.value, env);
      } else {
         PrintPolyType(val->d.type, env);
      }
      printf("\n");
   }
}

void PrintPrefillIntIndex(struct hashtbl * prefill, struct environment * env) {
   printf("Prefill:\n");
   for (struct blist * iter = prefill->top; iter != NULL; iter = iter->down) {
      printf("%d: ", (int) iter->key);
      struct PrefillValue * val = (struct PrefillValue *) iter->val;
      if (val->t == PREFILL_EXPRVAL) {
         PrintExprVal(val->d.value, env);
      } else {
         PrintPolyType(val->d.type, env);
      }
      printf("\n");
   }
}