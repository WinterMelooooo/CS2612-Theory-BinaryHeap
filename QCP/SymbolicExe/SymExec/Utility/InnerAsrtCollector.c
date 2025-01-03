#include "InnerAsrtCollector.h"

struct InnerAsrtCollector* InnerAsrtCollectorInit() {
   struct InnerAsrtCollector* collector = (struct InnerAsrtCollector*)malloc(sizeof(struct InnerAsrtCollector));
   collector->length = 0;
   collector->capacity = 10;
   collector->asrt = (struct AsrtList**)malloc(sizeof(struct AsrtList*) * collector->capacity);
   return collector;
}

void InnerAsrtCollectorAdd(struct InnerAsrtCollector* collector, struct AsrtList* asrt) {
   if (collector->length == collector->capacity) {
      collector->capacity *= 2;
      collector->asrt = (struct AsrtList**)realloc(collector->asrt, sizeof(struct AsrtList*) * collector->capacity);
   }
   collector->asrt[collector->length++] = asrt;
}

struct AsrtList* InnerAsrtCollectorGet(struct InnerAsrtCollector* collector, int index) {
   return collector->asrt[index];
}

void InnerAsrtCollectorFree(struct InnerAsrtCollector* collector) {
   // Todo: asrtList free
   free(collector->asrt);
   free(collector);
}