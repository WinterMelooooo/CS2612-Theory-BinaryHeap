#ifndef INNER_ASRT_COLLECTOR_H
#define INNER_ASRT_COLLECTOR_H

#include "../AsrtDef/AssDef.h"

struct InnerAsrtCollector {
   int length;
   int capacity;
   struct AsrtList** asrt;
};

struct InnerAsrtCollector* InnerAsrtCollectorInit();

void InnerAsrtCollectorAdd(struct InnerAsrtCollector* collector, struct AsrtList* asrt);

struct AsrtList* InnerAsrtCollectorGet(struct InnerAsrtCollector* collector, int index);

void InnerAsrtCollectorFree(struct InnerAsrtCollector* collector);

#endif // INNER_ASRT_COLLECTOR_H