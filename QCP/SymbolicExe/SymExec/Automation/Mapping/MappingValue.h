#ifndef __MAPPING_VALUE_H__
#define __MAPPING_VALUE_H__

#include <stdlib.h>
#include "../../AsrtDef/AssDef.h"
#include "../PatternASTDef/PatternPolyType.h"
#include "../Util/Error.h"

enum mappingValueType {
    MAPPING_VALUE_EXPRVAL,
    MAPPING_VALUE_POLYTYPE,
    MAPPING_VALUE_PATPOLYTYPE,
    MAPPING_VALUE_CTYPE,
    MAPPING_VALUE_PTR,
};

struct mappingValue {
    enum mappingValueType ty;
    int own;
    void * val;
};

struct mappingValue * initExprValMappingValue(struct ExprVal * val, int own);
struct mappingValue * initPolyTypeMappingValue(struct PolyType * val, int own);
struct mappingValue * initPatternPolyTypeMappingValue(struct PatternPolyType * val, int own);
struct mappingValue * initCTypeMappingValue(struct SimpleCtype * val, int own);
struct mappingValue * initPtrMappingValue(void * ptr);

void finiMappingValue(struct mappingValue * val);
void * mappingValueInnerCopy(struct mappingValue * val);
struct mappingValue * mappingValueCopy(struct mappingValue * val);
struct mappingValue * mappingValueDeepCopy(struct mappingValue * val);

#endif