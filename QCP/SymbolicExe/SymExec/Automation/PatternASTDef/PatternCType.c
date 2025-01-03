#include "PatternCType.h"

struct PatternCType * initPatternCTypeVoid() {
    struct PatternCType * ret = (struct PatternCType *) malloc(sizeof(struct PatternCType));
    ret->ty = PATTERN_CTYPE_VOID;
    return ret;
}

struct PatternCType * initPatternCTypeI8(enum Signedness s) {
    struct PatternCType * ret = (struct PatternCType *) malloc(sizeof(struct PatternCType));
    ret->ty = PATTERN_CTYPE_C8;
    ret->data.ti = malloc(sizeof(struct PatternCTypeInt));
    ret->data.ti->s = s;
    return ret;
}

struct PatternCType * initPatternCTypeI16(enum Signedness s) {
    struct PatternCType * ret = (struct PatternCType *) malloc(sizeof(struct PatternCType));
    ret->ty = PATTERN_CTYPE_C16;
    ret->data.ti = malloc(sizeof(struct PatternCTypeInt));
    ret->data.ti->s = s;
    return ret;
}

struct PatternCType * initPatternCTypeI32(enum Signedness s) {
    struct PatternCType * ret = (struct PatternCType *) malloc(sizeof(struct PatternCType));
    ret->ty = PATTERN_CTYPE_C32;
    ret->data.ti = malloc(sizeof(struct PatternCTypeInt));
    ret->data.ti->s = s;
    return ret;
}

struct PatternCType * initPatternCTypeI64(enum Signedness s) {
    struct PatternCType * ret = (struct PatternCType *) malloc(sizeof(struct PatternCType));
    ret->ty = PATTERN_CTYPE_C64;
    ret->data.ti = malloc(sizeof(struct PatternCTypeInt));
    ret->data.ti->s = s;
    return ret;
}

struct PatternCType * initPatternCTypePtr(struct PatternCType * type) {
    struct PatternCType * ret = (struct PatternCType *) malloc(sizeof(struct PatternCType));
    ret->ty = PATTERN_CTYPE_PTR;
    ret->data.tptr = malloc(sizeof(struct PatternCTypePtr));
    ret->data.tptr->type = type;
    return ret;
}

struct PatternCType * initPatternCTypeArray(struct PatternCType * type, int length) {
    struct PatternCType * ret = (struct PatternCType *) malloc(sizeof(struct PatternCType));
    ret->ty = PATTERN_CTYPE_ARR;
    ret->data.tarr = malloc(sizeof(struct PatternCTypeArray));
    ret->data.tarr->type = type;
    ret->data.tarr->length = length;
    return ret;
}

struct PatternCType * initPatternCTypeFunc(struct PatternCType * ret_type, struct PatternCTypeList * arg_list) {
    struct PatternCType * ret = (struct PatternCType *) malloc(sizeof(struct PatternCType));
    ret->ty = PATTERN_CTYPE_FUNC;
    ret->data.tfunc = malloc(sizeof(struct PatternCTypeFunc));
    ret->data.tfunc->ret_type = ret_type;
    ret->data.tfunc->arg_list = arg_list;
    return ret;
}

struct PatternCType * initPatternCTypeStruct(char * struct_name) {
    struct PatternCType * ret = (struct PatternCType *) malloc(sizeof(struct PatternCType));
    ret->ty = PATTERN_CTYPE_STRUCT;
    ret->data.tstruct = malloc(sizeof(struct PatternCTypeStruct));
    ret->data.tstruct->struct_name = struct_name;
    return ret;
}

struct PatternCType * initPatternCTypeUnion(char * union_name) {
    struct PatternCType * ret = (struct PatternCType *) malloc(sizeof(struct PatternCType));
    ret->ty = PATTERN_CTYPE_UNION;
    ret->data.tunion = malloc(sizeof(struct PatternCTypeUnion));
    ret->data.tunion->union_name = union_name;
    return ret;
}

struct PatternCType * initPatternCTypeEnum(char * enum_name) {
    struct PatternCType * ret = (struct PatternCType *) malloc(sizeof(struct PatternCType));
    ret->ty = PATTERN_CTYPE_ENUM;
    ret->data.tenum = malloc(sizeof(struct PatternCTypeEnum));
    ret->data.tenum->enum_name = enum_name;
    return ret;
}

struct PatternCType * initPatternCTypeVar(char * var) {
    struct PatternCType * ret = (struct PatternCType *) malloc(sizeof(struct PatternCType));
    ret->ty = PATTERN_CTYPE_VAR;
    ret->data.var = var;
    return ret;
}

void PatternCTypeFree(struct PatternCType * type) {
    if (type == NULL) {
        return;
    }
    switch (type->ty) {
        case PATTERN_CTYPE_VOID: {
            break;
        }
        case PATTERN_CTYPE_C8:
        case PATTERN_CTYPE_C16:
        case PATTERN_CTYPE_C32:
        case PATTERN_CTYPE_C64: {
            free(type->data.ti);
            break;
        }
        case PATTERN_CTYPE_PTR: {
            PatternCTypeFree(type->data.tptr->type);
            free(type->data.tptr);
            break;
        }
        case PATTERN_CTYPE_ARR: {
            PatternCTypeFree(type->data.tarr->type);
            free(type->data.tarr);
            break;
        }
        case PATTERN_CTYPE_FUNC: {
            PatternCTypeFree(type->data.tfunc->ret_type);
            PatternCTypeListFree(type->data.tfunc->arg_list);
            free(type->data.tfunc);
            break;
        }
        case PATTERN_CTYPE_STRUCT: {
            free(type->data.tstruct->struct_name);
            free(type->data.tstruct);
            break;
        }
        case PATTERN_CTYPE_UNION: {
            free(type->data.tunion->union_name);
            free(type->data.tunion);
            break;
        }
        case PATTERN_CTYPE_ENUM: {
            free(type->data.tenum->enum_name);
            free(type->data.tenum);
            break;
        }
        case PATTERN_CTYPE_VAR: {
            free(type->data.var);
            break;
        }
        default: {
            ERROR("Unknown type in PatternCTypeFree");
        }
    }
    free(type);
}

struct PatternCTypeList * initPatternCTypeList(struct PatternCType * type, struct PatternCTypeList * next) {
    struct PatternCTypeList * ret = (struct PatternCTypeList *) malloc(sizeof(struct PatternCTypeList));
    ret->type = type;
    ret->next = next;
    return ret;
}

void PatternCTypeListFree(struct PatternCTypeList * head) {
    if (head == NULL) {
        return;
    }
    PatternCTypeFree(head->type);
    PatternCTypeListFree(head->next);
    free(head);
}

struct PatternCType * PatternCTypeDeepCopy(struct PatternCType * type) {
    if (type == NULL) {
        return NULL;
    }
    switch (type->ty) {
        case PATTERN_CTYPE_VOID: {
            return initPatternCTypeVoid();
            break;
        }
        case PATTERN_CTYPE_C8: {
            return initPatternCTypeI8(type->data.ti->s);
            break;
        }
        case PATTERN_CTYPE_C16: {
            return initPatternCTypeI16(type->data.ti->s);
            break;
        }
        case PATTERN_CTYPE_C32: {
            return initPatternCTypeI32(type->data.ti->s);
            break;
        }
        case PATTERN_CTYPE_C64: {
            return initPatternCTypeI64(type->data.ti->s);
            break;
        }
        case PATTERN_CTYPE_PTR: {
            return initPatternCTypePtr(PatternCTypeDeepCopy(type->data.tptr->type));
            break;
        }
        case PATTERN_CTYPE_ARR: {
            return initPatternCTypeArray(PatternCTypeDeepCopy(type->data.tarr->type), type->data.tarr->length);
            break;
        }
        case PATTERN_CTYPE_FUNC: {
            return initPatternCTypeFunc(PatternCTypeDeepCopy(type->data.tfunc->ret_type), PatternCTypeListDeepCopy(type->data.tfunc->arg_list));
            break;
        }
        case PATTERN_CTYPE_STRUCT: {
            return initPatternCTypeStruct(strdup(type->data.tstruct->struct_name));
            break;
        }
        case PATTERN_CTYPE_UNION: {
            return initPatternCTypeUnion(strdup(type->data.tunion->union_name));
            break;
        }
        case PATTERN_CTYPE_ENUM: {
            return initPatternCTypeEnum(strdup(type->data.tenum->enum_name));
            break;
        }
        case PATTERN_CTYPE_VAR: {
            return initPatternCTypeVar(strdup(type->data.var));
            break;
        }
        default: {
            ERROR("Unknown type in PatternCTypeDeepCopy");
        }
    }
    return NULL;
}

struct PatternCTypeList * PatternCTypeListDeepCopy(struct PatternCTypeList * type_list) {
    if (type_list == NULL) return NULL;
    struct PatternCTypeList * ret = (struct PatternCTypeList *) malloc(sizeof(struct PatternCTypeList));
    ret->type = PatternCTypeDeepCopy(type_list->type);
    ret->next = PatternCTypeListDeepCopy(type_list->next);
    return ret;
}

int PatternCTypeEqual(struct PatternCType * type1, struct PatternCType * type2) {
    if (type1 == NULL && type2 == NULL) return 1;
    if (type1 == NULL || type2 == NULL) return 0;
    if (type1->ty != type2->ty) {
        return 0;
    }
    switch (type1->ty) {
        case PATTERN_CTYPE_VOID: {
            return 1;
        }
        case PATTERN_CTYPE_C8:
        case PATTERN_CTYPE_C16:
        case PATTERN_CTYPE_C32:
        case PATTERN_CTYPE_C64: {
            return type1->data.ti->s == type2->data.ti->s;
        }
        case PATTERN_CTYPE_PTR: {
            return PatternCTypeEqual(type1->data.tptr->type, type2->data.tptr->type);
        }
        case PATTERN_CTYPE_ARR: {
            return type1->data.tarr->length == type2->data.tarr->length && PatternCTypeEqual(type1->data.tarr->type, type2->data.tarr->type);
        }
        case PATTERN_CTYPE_FUNC: {
            return PatternCTypeEqual(type1->data.tfunc->ret_type, type2->data.tfunc->ret_type) && PatternCTypeListEqual(type1->data.tfunc->arg_list, type2->data.tfunc->arg_list);
        }
        case PATTERN_CTYPE_STRUCT: {
            return !strcmp(type1->data.tstruct->struct_name, type2->data.tstruct->struct_name);
        }
        case PATTERN_CTYPE_UNION: {
            return !strcmp(type1->data.tunion->union_name, type2->data.tunion->union_name);
        }
        case PATTERN_CTYPE_ENUM: {
            return !strcmp(type1->data.tenum->enum_name, type2->data.tenum->enum_name);
        }
        case PATTERN_CTYPE_VAR: {
            return !strcmp(type1->data.var, type2->data.var);
        }
        default: {
            ERROR("Unknown type in PatternCTypeEqual");
        }
    }
    return 0;
}

int PatternCTypeListEqual(struct PatternCTypeList * type_list1, struct PatternCTypeList * type_list2) {
    if (type_list1 == NULL && type_list2 == NULL) return 1;
    if (type_list1 == NULL || type_list2 == NULL) return 0;
    return PatternCTypeEqual(type_list1->type, type_list2->type) && PatternCTypeListEqual(type_list1->next, type_list2->next);
}

void PatternCTypePrint(struct PatternCType * type) {
    printf("PatternCType(");
    if (type == NULL) {
        return;
    }
    switch (type->ty) {
        case PATTERN_CTYPE_VOID: {
            printf("void");
            break;
        }
        case PATTERN_CTYPE_C8: {
            printf("%c8", type->data.ti->s == Signed ? 'I' : 'U');
            break;
        }
        case PATTERN_CTYPE_C16: {
            printf("%c16", type->data.ti->s == Signed ? 'I' : 'U');
            break;
        }
        case PATTERN_CTYPE_C32: {
            printf("%c32", type->data.ti->s == Signed ? 'I' : 'U');
            break;
        }
        case PATTERN_CTYPE_C64: {
            printf("%c64", type->data.ti->s == Signed ? 'I' : 'U');
            break;
        }
        case PATTERN_CTYPE_PTR: {
            printf("*");
            PatternCTypePrint(type->data.tptr->type);
            break;
        }
        case PATTERN_CTYPE_ARR: {
            PatternCTypePrint(type->data.tarr->type);
            printf("[%d]", type->data.tarr->length);
            break;
        }
        case PATTERN_CTYPE_FUNC: {
            PatternCTypePrint(type->data.tfunc->ret_type);
            PatternCTypeListPrint(type->data.tfunc->arg_list);
            break;
        }
        case PATTERN_CTYPE_STRUCT: {
            printf("struct %s", type->data.tstruct->struct_name);
            break;
        }
        case PATTERN_CTYPE_UNION: {
            printf("union %s", type->data.tunion->union_name);
            break;
        }
        case PATTERN_CTYPE_ENUM: {
            printf("enum %s", type->data.tenum->enum_name);
            break;
        }
        case PATTERN_CTYPE_VAR: {
            printf("%s", type->data.var);
            break;
        }
        default: {
            ERROR("Unknown type in PatternCTypePrint");
        }
    }
    printf(")");
}


void PatternCTypeListPrint(struct PatternCTypeList * type_list) {
    printf("PatternCTypeList(");
    struct PatternCTypeList * cur = type_list;
    while (cur != NULL) {
        PatternCTypePrint(cur->type);
        cur = cur->next;
        if (cur != NULL) {
            printf(",");
        }
    }
    printf(")");
}