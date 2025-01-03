#ifndef ADDRESSABILITYTRANS_H_
#define ADDRESSABILITYTRANS_H_

#include "../../compiler/env.h"
#include "../AsrtDef/AssDef.h"

struct Assertion * ToAddressableSingle(struct Assertion * asrt, struct environment * env);

struct Assertion * ToNonaddressableSingle(struct Assertion * asrt);

struct AsrtList * ToAddressable(struct AsrtList * asrt, struct environment * env);

struct AsrtList * ToNonaddressable(struct AsrtList * asrt);

#endif // ADDRESSABILITYTRANS_H_