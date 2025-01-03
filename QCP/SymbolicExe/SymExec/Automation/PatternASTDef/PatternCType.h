#ifndef __PATTERN_C_TYPE_H__
#define __PATTERN_C_TYPE_H__

#include "../../AsrtDef/SimpleCtypeDef.h"
#include "../Util/Error.h"
#include <string.h>

struct PatternCType;
struct PatternCTypeList;

enum PatternCTypeType {
    PATTERN_CTYPE_VOID,
    PATTERN_CTYPE_C8,
    PATTERN_CTYPE_C16,
    PATTERN_CTYPE_C32,
    PATTERN_CTYPE_C64,
    PATTERN_CTYPE_PTR,
    PATTERN_CTYPE_ARR,
    PATTERN_CTYPE_FUNC,
    PATTERN_CTYPE_STRUCT,
    PATTERN_CTYPE_UNION,
    PATTERN_CTYPE_ENUM,
    PATTERN_CTYPE_VAR
};

struct PatternCTypeInt {
    enum Signedness s;
};

struct PatternCTypePtr {
    struct PatternCType * type;
};

struct PatternCTypeArray {
    struct PatternCType * type;
    int length;
};

struct PatternCTypeFunc {
    struct PatternCType * ret_type;
    struct PatternCTypeList * arg_list;
};

struct PatternCTypeStruct {
    char * struct_name;
};

struct PatternCTypeUnion {
    char * union_name;
};

struct PatternCTypeEnum {
    char * enum_name;
};

struct PatternCType {
    enum PatternCTypeType ty;
    union {
        char * var;
        struct PatternCTypeInt * ti;
        struct PatternCTypePtr * tptr;
        struct PatternCTypeArray * tarr;
        struct PatternCTypeFunc * tfunc;
        struct PatternCTypeStruct * tstruct;
        struct PatternCTypeUnion * tunion;
        struct PatternCTypeEnum * tenum;
   } data;
};

struct PatternCTypeList {
    struct PatternCType * type;
    struct PatternCTypeList * next;
};

struct PatternCType * initPatternCTypeVoid();
struct PatternCType * initPatternCTypeI8(enum Signedness s);
struct PatternCType * initPatternCTypeI16(enum Signedness s);
struct PatternCType * initPatternCTypeI32(enum Signedness s);
struct PatternCType * initPatternCTypeI64(enum Signedness s);
struct PatternCType * initPatternCTypePtr(struct PatternCType * type);
struct PatternCType * initPatternCTypeArray(struct PatternCType * type, int length);
struct PatternCType * initPatternCTypeFunc(struct PatternCType * ret_type, struct PatternCTypeList * arg_list);
struct PatternCType * initPatternCTypeStruct(char * struct_name);
struct PatternCType * initPatternCTypeUnion(char * union_name);
struct PatternCType * initPatternCTypeEnum(char * enum_name);
struct PatternCType * initPatternCTypeVar(char * var);

struct PatternCTypeList * initPatternCTypeList(struct PatternCType * type, struct PatternCTypeList * next);
void PatternCTypeListFree(struct PatternCTypeList * head);

void PatternCTypeFree(struct PatternCType * type);

struct PatternCType * PatternCTypeDeepCopy(struct PatternCType * type);
struct PatternCTypeList * PatternCTypeListDeepCopy(struct PatternCTypeList * type_list);
int PatternCTypeEqual(struct PatternCType * type1, struct PatternCType * type2);
int PatternCTypeListEqual(struct PatternCTypeList * type_list1, struct PatternCTypeList * type_list2);

void PatternCTypePrint(struct PatternCType * type);
void PatternCTypeListPrint(struct PatternCTypeList * type_list);
#endif