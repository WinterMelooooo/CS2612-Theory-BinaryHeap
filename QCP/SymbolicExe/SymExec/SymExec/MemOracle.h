#ifndef MEM_ORACLE_H
#define MEM_ORACLE_H

#include "../AsrtDef/AssDef.h"

struct ExprVal * AsrtReadMem(struct Assertion * asrt, struct ExprVal * addr, int chunk_size);

// int AsrtWriteMem(struct Assertion * asrt, struct ExprVal * addr, struct ExprVal * val, int chunk_size);
#endif 