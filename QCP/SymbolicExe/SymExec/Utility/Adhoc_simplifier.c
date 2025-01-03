#include "../../compiler/env.h"
#include "Adhoc_simplifier.h"

struct Proposition * Forall_instantiate(int index_name, struct Proposition *cond, struct Proposition *goal) {
  if (cond == NULL) {
    fprintf(stderr, "Error Forall prop : empty condition %s %d \n", __FILE__, __LINE__);
    exit(-1);
  }
  if (!Used_ExprVal_in_Prop(cond,ExprVal_V_VARI(index_name))) return PropTrue();
  switch (cond->t) {
    case T_PROP_BINARY: {
      if (cond->d.BINARY.op == PROP_AND) {
        return PropBinary(PROP_AND,Forall_instantiate(index_name,cond->d.BINARY.prop1,goal),Forall_instantiate(index_name,cond->d.BINARY.prop2,goal));
      } 
      else return PropTrue(); 
    }
    case T_PROP_COMPARE:{
      struct ExprVal *bound = NULL;
      switch (cond->d.COMPARE.op) {
        case PROP_GE: {
          if (ExprValCheckEqual(cond->d.COMPARE.expr1,ExprVal_V_VARI(index_name))) bound = cond->d.COMPARE.expr2;
          else bound = cond->d.COMPARE.expr1;
          break;
        }
        case PROP_LE: {
          if (ExprValCheckEqual(cond->d.COMPARE.expr1,ExprVal_V_VARI(index_name))) bound = cond->d.COMPARE.expr2;
          else bound = cond->d.COMPARE.expr1;
          break;
        }
        case PROP_LT: {
          if (ExprValCheckEqual(cond->d.COMPARE.expr1,ExprVal_V_VARI(index_name))) bound = ExprVal_VBOP(Osub,cond->d.COMPARE.expr2,ExprVal_EZ_VAL(1));
          else bound = ExprVal_VBOP(Oadd,cond->d.COMPARE.expr1,ExprVal_EZ_VAL(1));
          break;
        }
        case PROP_GT: {
          if (ExprValCheckEqual(cond->d.COMPARE.expr1,ExprVal_V_VARI(index_name))) bound = ExprVal_VBOP(Oadd,cond->d.COMPARE.expr2,ExprVal_EZ_VAL(1));
          else bound = ExprVal_VBOP(Osub,cond->d.COMPARE.expr1,ExprVal_EZ_VAL(1));
          break;
        }
        default : 
          bound = NULL;
      }
      if (bound == NULL) return PropTrue();
      return PropSubst(PropDeepCopy(goal),ExprVal_V_VARI(index_name),bound);
    }
    default:
      return PropTrue();
  }

}

struct PropList * Forall_instantiate_list(struct PropList *source_list){
  if (source_list == NULL) return PropListNil();
  switch (source_list->head->t) {
     case T_PROP_QUANTIFIER:
       if (source_list->head->d.QUANTIFIER.op == PROP_FORALL) {
          if (source_list -> head->d.QUANTIFIER.prop->t == T_PROP_BINARY && source_list -> head->d.QUANTIFIER.prop->d.BINARY.op == PROP_IMPLY) {
            return PropListCons(Forall_instantiate(source_list -> head->d.QUANTIFIER.ident, source_list -> head->d.QUANTIFIER.prop->d.BINARY.prop1,
                source_list -> head->d.QUANTIFIER.prop->d.BINARY.prop2), Forall_instantiate_list(source_list->next));
          }
          else return PropListCons(PropDeepCopy(source_list->head),Forall_instantiate_list(source_list->next));
       }
       else return PropListCons(PropDeepCopy(source_list->head),Forall_instantiate_list(source_list->next)); 
     default:
       return PropListCons(PropDeepCopy(source_list->head),Forall_instantiate_list(source_list->next));
   }
}

struct Proposition *Mentioned_prop(struct ExprVal * list_name, struct ExprVal *index_name, struct Proposition *source) {
  if (!Used_ExprVal_in_Prop(source, list_name)) return NULL;
  if (Used_ExprVal_in_Prop(source, ExprVal_LINDEX(list_name,index_name))) return PropTrue();
  switch (source->t) {
     case T_PROP_QUANTIFIER:
       if (source->d.QUANTIFIER.op == PROP_FORALL) {
          if (source->d.QUANTIFIER.prop->t == T_PROP_BINARY && source->d.QUANTIFIER.prop->d.BINARY.op == PROP_IMPLY) {
            struct Proposition *now = PropSubst(source->d.QUANTIFIER.prop->d.BINARY.prop1, ExprVal_V_VARI(source->d.QUANTIFIER.ident) ,index_name);
            struct Proposition *goal = PropSubst(source->d.QUANTIFIER.prop->d.BINARY.prop2, ExprVal_V_VARI(source->d.QUANTIFIER.ident), index_name);
            if (Used_ExprVal_in_Prop(goal,ExprVal_LINDEX(list_name,index_name))) {
              PropFree(goal);
              return now; 
            }
            PropFree(goal);
            PropFree(now);
            return NULL;
          }
          else return NULL;
       }
       else return NULL; 
     default:
       return NULL;
   }
}


struct Proposition * Mentioned(struct ExprVal * list_name, struct ExprVal *index_name, struct PropList *source_list) 
// 这个函数是用来查询source_list中是否有提及list_name中index的position的
{
   if (source_list == NULL) return NULL;
   struct Proposition *res = Mentioned(list_name,index_name,source_list->next);
   struct Proposition *now = Mentioned_prop(list_name,index_name, source_list->head);
   if (now == NULL) return res;
   if (res == NULL) return now;
   return PropBinary(PROP_OR,now,res);
}

struct PropList *Quantifier_Adhoc_change(struct PropList *target_list, struct PropList *source_list, struct environment * env) {
   if (target_list == NULL) return PropListNil();
   switch (target_list->head->t) {
     case T_PROP_COMPARE:
       if (target_list->head->d.COMPARE.op == PROP_EQ) {
          struct Proposition * new_prop ;
          if (target_list->head->d.COMPARE.expr1->t == LINDEX && target_list->head->d.COMPARE.expr2->t == FUNCAPP) {
             new_prop = Mentioned(target_list->head->d.COMPARE.expr1->d.LINDEX.list, target_list->head->d.COMPARE.expr1->d.LINDEX.index, source_list);
          }
          else if (target_list->head->d.COMPARE.expr1->t == FUNCAPP && target_list->head->d.COMPARE.expr2->t == LINDEX) {
             new_prop = Mentioned(target_list->head->d.COMPARE.expr2->d.LINDEX.list, target_list->head->d.COMPARE.expr2->d.LINDEX.index, source_list);
          }
          else new_prop = PropDeepCopy(target_list->head);
          return PropListCons(new_prop, Quantifier_Adhoc_change(target_list->next,source_list, env));
       }
       else return PropListCons(PropDeepCopy(target_list->head),Quantifier_Adhoc_change(target_list->next, source_list, env));
     case T_PROP_QUANTIFIER:
       if (target_list->head->d.QUANTIFIER.op == PROP_FORALL) {
          if (target_list -> head->d.QUANTIFIER.prop->t == T_PROP_BINARY && target_list -> head->d.QUANTIFIER.prop->d.BINARY.op == PROP_IMPLY) {
            return PropListCons(Forall_instantiate(target_list -> head->d.QUANTIFIER.ident, target_list -> head->d.QUANTIFIER.prop->d.BINARY.prop1,
                target_list -> head->d.QUANTIFIER.prop->d.BINARY.prop2), Quantifier_Adhoc_change(target_list->next, source_list, env));
          }
          else return PropListCons(PropDeepCopy(target_list->head),Quantifier_Adhoc_change(target_list->next, source_list, env));
       }
       else return PropListCons(PropDeepCopy(target_list->head),Quantifier_Adhoc_change(target_list->next, source_list, env)); 
     default:
       return PropListCons(PropDeepCopy(target_list->head),Quantifier_Adhoc_change(target_list->next, source_list, env));
   }
   
}

struct PropList *Adhoc_change_tar(struct PropList* target_list,struct PropList* source_list, struct environment * env){
  return Quantifier_Adhoc_change(target_list,source_list, env);
}




struct PropList *Adhoc_change_src(struct PropList* source_list) {

  return Forall_instantiate_list(source_list);
}