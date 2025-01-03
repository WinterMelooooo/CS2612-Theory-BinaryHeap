#ifndef SIMPLE_C_TYPE_DEF_H
#define SIMPLE_C_TYPE_DEF_H

#include "stdio.h"
#include "stddef.h"
#include "../Utility/List.h"

enum Signedness {
  Signed, Unsigned
};

enum SimpleCtype_type {
   C_void,
   C_int8,
   C_int16,
   C_int32,
   C_int64,
   C_pointer,
   C_array,
   C_function,
   C_struct,
   C_union,
   C_enum,
};

struct SimpleCtypeList;

struct SimpleCtype {
   enum SimpleCtype_type t;
   union {
      struct { } VOID;
      struct { enum Signedness s; } CINT8;     // char & U8
      struct { enum Signedness s; } CINT16;
      struct { enum Signedness s; } CINT32;
      struct { enum Signedness s; } CINT64;
      struct { struct SimpleCtype * type; } CPOINTER;
      struct { struct SimpleCtype * type; int length; } CARRAY;
      struct { struct SimpleCtype * ret_type; struct SimpleCtypeList * arg_list; } CFUNC;
      struct { int struct_id; } CSTRUCT;
      struct { int union_id; } CUNION;
      struct { int enum_id; } CENUM;
   } d;
};

struct SimpleCtype* SimpleCtypeVoid();
struct SimpleCtype* SimpleCtypeInt8(enum Signedness s);
struct SimpleCtype* SimpleCtypeInt16(enum Signedness s);
struct SimpleCtype* SimpleCtypeInt32(enum Signedness s);
struct SimpleCtype* SimpleCtypeInt64(enum Signedness s);
struct SimpleCtype* SimpleCtypePointer(struct SimpleCtype * type);
struct SimpleCtype* SimpleCtypeArray(struct SimpleCtype * type, int length);
struct SimpleCtype* SimpleCtypeFunction(struct SimpleCtype * ret_type, struct SimpleCtypeList * arg_list);
struct SimpleCtype* SimpleCtypeStruct(int struct_id);
struct SimpleCtype* SimpleCtypeUnion(int union_id);
struct SimpleCtype* SimpleCtypeEnum(int enum_id);

int GetInnerTypeSize(struct SimpleCtype * ty);

struct SimpleCtype * SimpleCtypeDeepCopy(struct SimpleCtype * ty);

void SimpleCtypeFree(struct SimpleCtype *ty);

DECLARE_LIST(SimpleCtypeList, struct SimpleCtype*, data)

int SimpleCtypeCheckEqual(struct SimpleCtype * ty1, struct SimpleCtype * ty2);
int SimpleCtypeListCheckEqual(struct SimpleCtypeList * list1, struct SimpleCtypeList * list2);
int SimpleCtypeCheckAcceptable(struct SimpleCtype * ty1, struct SimpleCtype * ty2);
int SimpleCtypeListCheckAcceptable(struct SimpleCtypeList * list1, struct SimpleCtypeList * list2);

int SimpleCtypeIsPointer(struct SimpleCtype * ty);
int SimpleCtypeIsIntType(struct SimpleCtype * ty);
struct SimpleCtype * GetPointedType(struct SimpleCtype * ty);

#endif // SIMPLE_C_TYPE_DEF_H
