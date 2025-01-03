#ifndef TYPE_TRNAS_H
#define TYPE_TRNAS_H

#include "../AsrtDef/AssDef.h"
#include "../AsrtDef/ExistDef.h"
#include "../AsrtDef/LocalDef.h"
#include "../AsrtDef/PropDef.h"
#include "../AsrtDef/SepDef.h"
#include "../AsrtDef/ExprValDef.h"
#include "../../compiler/lang.h"

struct SimpleCtype * TransBasicType(enum BasicType ty);
struct SimpleCtype * TransType(struct type * rtype);

#endif // TYPE_TRNAS_H