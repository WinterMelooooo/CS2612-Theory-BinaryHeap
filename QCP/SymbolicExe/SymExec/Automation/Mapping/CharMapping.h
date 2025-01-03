#ifndef __CHAR_MAPPING_H__
#define __CHAR_MAPPING_H__

#include <string.h>
#include <stdlib.h>
#include "MappingValue.h"
#include "../../AsrtDef/AssDef.h"
#include "../Util/Config.h"

struct charMappingNode {
    char * var;
    struct mappingValue * val;
    struct charMappingNode * next, * prev;
    struct charMappingNode * next_in_hash;
};

struct charMapping {
    int own_key;
    struct charMappingNode * head;
    struct charMappingNode * node[MAPPING_SIZE];
};


struct charMapping * initCharMapping(int own_key);
struct mappingValue * charMappingFind(char * var, struct charMapping * matching);
int charMappingIn(char * var, struct charMapping * matching);
void charMappingErase(char * var, struct charMapping * matching);
void charMappingInsert(char * var, struct mappingValue * val, struct charMapping * matching);
struct charMapping * charMappingCopy(struct charMapping * matching);
struct charMapping * charMappingDeepCopy(struct charMapping * matching);
void finiCharMapping(struct charMapping * matching);

#endif