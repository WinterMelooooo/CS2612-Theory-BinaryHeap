#ifndef POLY_TYPE_DEF_H
#define POLY_TYPE_DEF_H

#include "../Utility/List.h"

enum PrimitiveType {
   NAT_TYPE, Z_TYPE, BOOL_TYPE, PROP_TYPE, ASRT_TYPE
};

enum PolyTypeType {
   POLY_VAR, POLY_FUNCAPP, POLY_ARROW
};

struct PolyType;

DECLARE_LIST(PolyTypeList, struct PolyType *, data);

struct PolyType {
   enum PolyTypeType t;
   union {
      struct { int id; } VAR;
      struct { int func; struct PolyTypeList * args; } FUNCAPP;
      struct { struct PolyType * left; struct PolyType * right; } ARROW;
   }d;
};

struct PolyType * PolyTypeAsrt();
struct PolyType * PolyTypeProp();
struct PolyType * PolyTypePrimitive(enum PrimitiveType type);
struct PolyType * PolyTypeVar(int id);
struct PolyType * PolyTypeFuncApp(int func, struct PolyTypeList * args);
struct PolyType * PolyTypeArrow(struct PolyType * left, struct PolyType * right);
struct PolyType * PolyTypeList(struct PolyType * inner_type);
struct PolyType * PolyTypeDeepCopy(struct PolyType * t);
void PolyTypeFree(struct PolyType * t);

int PolyTypeCheckEqual(struct PolyType * t1, struct PolyType * t2);
int PolyTypeListCheckEqual(struct PolyTypeList * l1, struct PolyTypeList * l2);

struct PolyType * PolyTypeSubst(struct PolyType * t, struct PolyType * pre, struct PolyType * post);
struct PolyTypeList * PolyTypeListSubst(struct PolyTypeList * l, struct PolyType * pre, struct PolyType * post);

#endif // POLY_TYPE_DEF_H
