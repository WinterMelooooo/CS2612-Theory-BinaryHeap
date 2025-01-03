#include "StateDef.h"
#include "FuncCall.h"
#include "../AsrtDef/AssDef.h"

extern int exec_outflag;

struct AsrtTuple * CreateAsrtTuple(struct AsrtList * nrm, struct AsrtList * brk,
                                    struct AsrtList * cnt, struct FuncRetTypeList * ret) {
   struct AsrtTuple * AsrtTuple = malloc(sizeof(struct AsrtTuple));
   AsrtTuple->nrm = nrm;
   AsrtTuple->brk = brk;
   AsrtTuple->cnt = cnt;
   AsrtTuple->ret = ret;
   return AsrtTuple;
}

struct Assertion * RemoveMemPermission(struct Assertion * asrt, int id, struct environment * env) {
   int removed = 0;
   struct ExprVal * addr = LocalFind(id, asrt->local_list);
   for (struct SepList * sep_list = asrt->sep_list; sep_list != NULL; sep_list = sep_list->next) {
      if (sep_list->head->t == T_DATA_AT) {
         if (ExprValCheckEqual(addr, sep_list->head->d.DATA_AT.left) || 
             (sep_list->head->d.DATA_AT.left->t == VFIELD_ADDRESS && 
               ExprValCheckEqual(addr, sep_list->head->d.DATA_AT.left->d.VFIELD_ADDRESS.expr))) {
            asrt->sep_list = SepListRemove(sep_list, asrt->sep_list);
            removed = 1;
            break;
         }
      } else if (sep_list->head->t == T_UNDEF_DATA_AT) {
         if (ExprValCheckEqual(addr, sep_list->head->d.UNDEF_DATA_AT.left) || 
             (sep_list->head->d.UNDEF_DATA_AT.left->t == VFIELD_ADDRESS && 
               ExprValCheckEqual(addr, sep_list->head->d.UNDEF_DATA_AT.left->d.VFIELD_ADDRESS.expr))) {
            asrt->sep_list = SepListRemove(sep_list, asrt->sep_list);
            removed = 1;
            break;
         }
      } else if (sep_list->head->t == T_ARR) {
         if (ExprValCheckEqual(addr, sep_list->head->d.ARR.addr)) {
            asrt->sep_list = SepListRemove(sep_list, asrt->sep_list);
            removed = 1;
            break;
         }
      }
   }
   if (removed) return asrt;
   else {
      struct prog_var_info * info = find_prog_var_by_id(id, &env->persist);
      fprintf(stderr, "Error: Fail to Remove Memory Permission of %s\n", info->name);
      exit(1);
   }
   struct prog_var_info * var_info = find_prog_var_by_id(id, &env->persist);
   struct func_spec * spec;
   switch (var_info->type->t) {
      case T_STRUCT:
      case T_UNION:
         fprintf(stderr, "Error: RemoveMemPermission: struct/union not supported yet\n");
         break;
      case T_ARRAY: {
         if (var_info->type->d.ARRAY.ty == T_BASIC && var_info->type->d.ARRAY.ty->d.BASIC.ty == T_INT) {
         struct Assertion * tmp = CreateAsrt();
         struct logic_var_info * var_info = add_anonymous_logic_var(LOGIC_FREE, "uf_l", &env->persist);
         var_info->renaming = renaming_info_free_var("uf_l");
         var_info->atype = ATApp(ATList(&env->persist), ATZ(&env->persist));
         var_info->qv = NULL;
         int log_id = var_info->id;
         // todo : add proper sep to tmp
         struct func_spec * spec = DeclareSpec(ExistListNil(), ExistListCons(log_id, ExistListNil()),
                                                AsrtListCons(tmp, AsrtListNil()),
                                                AsrtListNil(),
                                                ExprVal_V_VARI(log_id), NULL);

         } else {
            fprintf(stderr, "Error: RemoveMemPermission: array type only supported int array yet\n");
         }
         break;
      }
   }
}

struct Assertion * SingleVarDelete(struct Assertion * asrt, int id, struct environment * env) {
   asrt = RemoveMemPermission(asrt, id, env);
   LocalErase(id, asrt->local_list);
   return asrt;
}

struct Assertion * AssertionVarPerish(struct Assertion * asrt, struct State * state, struct environment * env) {
   struct PSVarDefList * vars = state->defined_vars;
   while (vars != NULL) {
      asrt = SingleVarDelete(asrt, vars->data->id, env);
      vars = vars->next;
   }
   return asrt;
}

struct AsrtList * AsrtListVarPerish(struct AsrtList * asrt_list, struct State * state, struct environment * env) {
   for (struct AsrtList * i = asrt_list; i != NULL; i = i->next) {
      i->head = AssertionVarPerish(i->head, state, env);
   }
   return asrt_list;
}

struct State * CreateState(enum StateType type, struct StateStack * stack) {
   struct State * state = malloc(sizeof(struct State));
   state->t = type;
   switch (type) {
      case In_Global:
         break;
      case In_func_block:
         break;
      case Get_Inv:
         break;
      case In_while_block:
         state->d.In_while_block.asrt = CreateAsrtTuple(AsrtListNil(), AsrtListNil(), AsrtListNil(), FuncRetTypeListNil());
         state->d.In_while_block.condition = NULL;
         state->d.In_while_block.inv = AsrtListNil();
         state->d.In_while_block.precondition = AsrtListNil();
         state->d.In_while_block.start = NULL;
         state->d.In_while_block.inv_explicit = 0;
         break;
      case In_do_block:
         state->d.In_do_block.asrt = CreateAsrtTuple(AsrtListNil(), AsrtListNil(), AsrtListNil(), FuncRetTypeListNil());
         state->d.In_do_block.condition = NULL;
         state->d.In_do_block.inv = AsrtListNil();
         state->d.In_do_block.start = NULL;
         state->d.In_do_block.inv_explicit = 0;
         break;
      case In_for_block:
         state->d.In_for_block.asrt = CreateAsrtTuple(AsrtListNil(), AsrtListNil(), AsrtListNil(), FuncRetTypeListNil());
         state->d.In_for_block.condition = NULL;
         state->d.In_for_block.inv = AsrtListNil();
         state->d.In_for_block.start = NULL;
         state->d.In_for_block.inv_explicit = 0;
         break;
      case In_switch_block:
         state->d.In_switch_block.asrt = CreateAsrtTuple(AsrtListNil(), AsrtListNil(), AsrtListNil(), FuncRetTypeListNil());
         break;
      case In_switch_cases_block:
         state->d.In_switch_cases_block.asrt = CreateAsrtTuple(AsrtListNil(), AsrtListNil(), AsrtListNil(), FuncRetTypeListNil());
         break;
      case In_switch_default_block:
         state->d.In_switch_default_block.asrt = CreateAsrtTuple(AsrtListNil(), AsrtListNil(), AsrtListNil(), FuncRetTypeListNil());
         break;
      case In_if_then_block:
         state->d.In_if_then_block.false_part_asrt = AsrtListNil();
         break;
      case In_if_else_block:
         state->d.In_if_else_block.true_part_asrt = AsrtListNil();
         break;
      case In_block:
         break;
   }
   state->defined_vars = PSVarDefListNil();
   if (stack != NULL) {
      state->depth = stack->state->depth + 1;
   } else {
      state->depth = 0;
   }
   return state;
}

void StateFree(struct State * state) {
   switch (state->t) {
      case In_Global:
         break;
      case In_func_block:
         break;
      case Get_Inv:
         break;
      case In_while_block:
         free(state->d.In_while_block.asrt);
         break;
      case In_do_block:
         break;
      case In_for_block:
         free(state->d.In_for_block.asrt);
         break;
      case In_switch_block:
         free(state->d.In_switch_block.asrt);
         break;
      case In_switch_cases_block:
         free(state->d.In_switch_cases_block.asrt);
         break;
      case In_switch_default_block:
         free(state->d.In_switch_default_block.asrt);
         break;
      case In_if_then_block:
         break;
      case In_if_else_block:
         break;
      case In_block:
         break;
   }
   free(state);
}

// for debug
char* StateTypeToString(enum StateType t) {
   switch (t) {
      case In_Global: return "In_Global";
      case In_func_block: return "In_func_block";
      case Get_Inv: return "Get_Inv";
      case In_while_block: return "In_while_block";
      case In_do_block: return "In_do_block";
      case In_for_block: return "In_for_block";
      case In_switch_block: return "In_switch_block";
      case In_switch_cases_block: return "In_switch_cases_block";
      case In_switch_default_block: return "In_switch_default_block";
      case In_if_then_block: return "In_if_then_block";
      case In_if_else_block: return "In_if_else_block";
      case In_block: return "In_block";
      default: return "Unknown StateType";
   }
}

int IsContinueRelatedType(enum StateType t) {
   switch (t) {
      case In_while_block:
      case In_do_block:
      case In_for_block:
         return 1;
      default:
         return 0;
   }
}

int IsBreakRelatedType(enum StateType t) {
   switch (t) {
      case In_while_block:
      case In_do_block:
      case In_for_block:
      case In_switch_block:
         return 1;
      default:
         return 0;
   }
}

struct StateStack * StateStackPush(struct StateStack * stack, struct State * state) {
   if (exec_outflag) {
      printf("Push: %s\n", StateTypeToString(state->t));
   }
   struct StateStack * new_stack = malloc(sizeof(struct StateStack));
   new_stack->state = state;
   new_stack->next = stack;
   return new_stack;
}

struct StateStack * StateStackPop(struct StateStack * stack) {
   struct State * state = stack->state;
   if (exec_outflag) {
      printf("Pop: %s\n", StateTypeToString(state->t));
   }
   struct StateStack * tmp = stack;
   stack = stack->next;
   StateFree(state);
   free(tmp);
   return stack;
}

struct State * StateStackPeek(struct StateStack * stack) {
   return stack->state;
}
