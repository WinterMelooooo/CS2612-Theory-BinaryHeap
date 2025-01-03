#include "MappingValue.h"

struct mappingValue * initExprValMappingValue(struct ExprVal * val, int own) {
    struct mappingValue * ret = malloc(sizeof(struct mappingValue));
    ret->ty = MAPPING_VALUE_EXPRVAL;
    ret->val = val;
    ret->own = own;
    return ret;
}

struct mappingValue * initPolyTypeMappingValue(struct PolyType * val, int own) {
    struct mappingValue * ret = malloc(sizeof(struct mappingValue));
    ret->ty = MAPPING_VALUE_POLYTYPE;
    ret->val = val;
    ret->own = own;
    return ret;
}

struct mappingValue * initPatternPolyTypeMappingValue(struct PatternPolyType * val, int own) {
    struct mappingValue * ret = malloc(sizeof(struct mappingValue));
    ret->ty = MAPPING_VALUE_PATPOLYTYPE;
    ret->val = val;
    ret->own = own;
    return ret;
}

struct mappingValue * initCTypeMappingValue(struct SimpleCtype * val, int own) {
    struct mappingValue * ret = malloc(sizeof(struct mappingValue));
    ret->ty = MAPPING_VALUE_CTYPE;
    ret->val = val;
    ret->own = own;
    return ret;
}

struct mappingValue * initPtrMappingValue(void * ptr) {
    struct mappingValue * ret = malloc(sizeof(struct mappingValue));
    ret->ty = MAPPING_VALUE_PTR;
    ret->val = ptr;
    ret->own = 1;
    return ret;
}

void finiMappingValue(struct mappingValue * val) {
    if (val == NULL) return;
    if (val->own) {
        switch (val->ty) {
        case MAPPING_VALUE_EXPRVAL: {
            ExprValFree(val->val);
            break;
        }
        case MAPPING_VALUE_POLYTYPE: {
            PolyTypeFree(val->val);
            break;
        }
        case MAPPING_VALUE_PATPOLYTYPE: {
            PatternPolyTypeFree(val->val);
            break;
        }
        case MAPPING_VALUE_CTYPE: {
            SimpleCtypeFree(val->val);
            break;
        }
        case MAPPING_VALUE_PTR: {
            break;
        }
        default: {
            ERROR("Unknown mapping value type");
            break;
        }
        }
    }
    free(val);
}

void * mappingValueInnerCopy(struct mappingValue * val) {
    if (val == NULL) return NULL;
    switch (val->ty) {
    case MAPPING_VALUE_EXPRVAL: {
        return ExprValDeepCopy(val->val);
    }
    case MAPPING_VALUE_POLYTYPE: {
        return PolyTypeDeepCopy(val->val);
    }
    case MAPPING_VALUE_PATPOLYTYPE: {
        return PatternPolyTypeDeepCopy(val->val);
    }
    case MAPPING_VALUE_CTYPE: {
        return SimpleCtypeDeepCopy(val->val);
    }
    case MAPPING_VALUE_PTR: {
        return val->val;
    }
    default: {
        ERROR("Unknown mapping value type");
        return NULL;
    }
    }
    return NULL;
}

struct mappingValue * mappingValueCopy(struct mappingValue * val) {
    if (val == NULL) return NULL;
    struct mappingValue * ret = malloc(sizeof(struct mappingValue));
    ret->ty = val->ty;
    ret->own = val->own;
    if (val->own) ret->val = mappingValueInnerCopy(val);
    else ret->val = val->val;
    return ret;
}

struct mappingValue * mappingValueDeepCopy(struct mappingValue * val) {
    if (val == NULL) return NULL;
    struct mappingValue * ret = malloc(sizeof(struct mappingValue));
    ret->ty = val->ty;
    ret->own = 1;
    ret->val = mappingValueInnerCopy(val);
    return ret;
}