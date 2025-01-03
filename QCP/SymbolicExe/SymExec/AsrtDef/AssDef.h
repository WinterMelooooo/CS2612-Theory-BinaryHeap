#ifndef ASSDEF_INCLUDED
#define ASSDEF_INCLUDED

#include "ExprValDef.h"
#include "PropDef.h"
#include "LocalDef.h"
#include "SepDef.h"
#include "ExistDef.h"
#include "FpSpecDef.h"
#include "../Utility/List.h"

struct persistent_env;

/* Assertion : single case of InnerAssertion, disjunction will not appear */
/* AserList: means P || Q || R || ... */
/* AsrtLabeledGroup: for old value. 
    For example, UserAssertion: P || Q || R @mark1  will be translated to
    AsrtLabeledGroup: {
      label: mark1,
      asrt_list: InnerAssertion of P, InnerAssertion of Q, InnerAssertion of R
    }
*/

struct Assertion {
  struct PropList * prop_list;   // memory unrelated proposition
  void * local_list;  // relation between program var and logic var
  struct SepList * sep_list;     // memory related proposition
  struct ExistList * exist_list; // existential logic variables
  struct FPSpecList * fp_spec_list; // function pointer specification
};

struct Assertion * CreateAsrt();

struct AsrtList {
  struct Assertion * head;
  struct AsrtList * next;
};

struct AsrtList* AsrtListNil();

struct AsrtList* AsrtListCons(struct Assertion * asrt, struct AsrtList * next);

struct AsrtList* AsrtListLink(struct AsrtList * left, struct AsrtList * right);

struct AsrtList * AsrtListReverse(struct AsrtList * asrt_list);

struct AsrtLabeledGroup {
  char * label;
  struct AsrtList * asrt_list;
};

struct AsrtLabeledGroup * CreateAsrtLabeledGroupf(char * label, struct AsrtList * asrt_list);

struct AsrtLabeledGroupList {
  struct AsrtLabeledGroup * head;
  struct AsrtLabeledGroupList * next;
};

struct AsrtLabeledGroupList * AsrtLabeledGroupListNil();

struct AsrtLabeledGroupList * AsrtLabeledGroupListCons(struct AsrtLabeledGroup * group, struct AsrtLabeledGroupList * next);

struct AsrtLabeledGroupList * AsrtLabeledGroupListLink(struct AsrtLabeledGroupList * left, struct AsrtLabeledGroupList * right);

struct ExprVal * GetDataAtValue(struct Assertion * inner_asrt, struct ExprVal * expr);

int ReplaceDataAtValue(struct Assertion * inner_asrt, struct ExprVal * lexpr, struct ExprVal * rexpr);

struct Assertion * AsrtDeepCopy(struct Assertion * asrt);

struct AsrtList * AsrtListDeepCopy(struct AsrtList * asrt_list);

void AsrtFree(struct Assertion *asrt);

void AsrtListFree(struct AsrtList *asrt_list);

void AsrtLabeledGroupFree(struct AsrtLabeledGroup *asrt_group);

void AsrtLabeledGroupListFree(struct AsrtLabeledGroupList *asrt_group_list);

struct FuncRetType {
   struct Assertion * asrt;
   struct ExprVal * val;       // maybe null
   struct FuncRetType * next;
};

struct FuncRetType * FuncRetTypeNil();
struct FuncRetType * FuncRetTypeCons(struct Assertion * asrt, 
                                     struct ExprVal * val, struct FuncRetType * next);
struct FuncRetType * FuncRetTypeLink(struct FuncRetType * list1, struct FuncRetType * list2);
struct FuncRetType * FuncRetTypeDeepCopy(struct FuncRetType * ret);
void FuncRetTypeFree(struct FuncRetType * ret);

struct FuncRetTypeList {
    struct FuncRetType * head;
    struct StringList * scopes;
    struct FuncRetTypeList * next;
};

struct FuncRetTypeList * FuncRetTypeListNil();
struct FuncRetTypeList * FuncRetTypeListCons(struct FuncRetType * ret, struct StringList * scopes, struct FuncRetTypeList * next);
struct FuncRetTypeList * FuncRetTypeListLink(struct FuncRetTypeList * list1, struct FuncRetTypeList * list2);

struct Assertion * AsrtSubst(struct Assertion * asrt, struct ExprVal * pre, struct ExprVal * post);
struct Assertion * AsrtSubstPolyType(struct Assertion * asrt, struct PolyType * pre, struct PolyType * post, struct persistent_env * env);
struct AsrtList * AsrtListSubst(struct AsrtList * asrt_list, struct ExprVal * pre, struct ExprVal * post);
struct AsrtList * AsrtListSubstPolyType(struct AsrtList * asrt_list, struct PolyType * pre, struct PolyType * post, struct persistent_env * env);

struct Assertion * AsrtMerge(struct Assertion * asrt1, struct Assertion * asrt2);

#endif  // ASSDEF_INCLUDED