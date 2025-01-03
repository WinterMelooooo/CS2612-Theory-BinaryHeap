#ifndef __INT_MAPPING_H__
#define __INT_MAPPING_H__

#include <stdlib.h>
#include "MappingValue.h"
#include "../../AsrtDef/AssDef.h"
#include "../Util/Config.h"

struct intMappingNode {
    int id;
    struct mappingValue * val;
    struct intMappingNode * next, * prev;
    struct intMappingNode * next_in_hash;
};

struct intMapping {
    struct intMappingNode * head;
    struct intMappingNode * node[MAPPING_SIZE];
};

struct intMapping * initIntMapping();
struct mappingValue * intMappingFind(int id, struct intMapping * matching);
int intMappingIn(int id, struct intMapping * matching);
void intMappingErase(int id, struct intMapping * matching);
void intMappingInsert(int id, struct mappingValue * val, struct intMapping * matching);
struct intMapping * intMappingCopy(struct intMapping * matching);
struct intMapping * intMappingDeepCopy(struct intMapping * matching);
void finiIntMapping(struct intMapping * matching);

#endif