#include "IntMapping.h"

static struct intMappingNode * initIntMappingNode(int id, struct mappingValue * val) {
   struct intMappingNode * node = (struct intMappingNode *)malloc(sizeof(struct intMappingNode));
   node->id = id;
   node->val = val;
   node->next = node->prev = node->next_in_hash = NULL;
   return node;
}

struct intMapping * initIntMapping() {
   struct intMapping * matching = (struct intMapping *)malloc(sizeof(struct intMapping));
   matching->head = NULL;
   for (int i = 0; i < MAPPING_SIZE; i++)
      matching->node[i] = NULL;
   return matching;
}

static void finiIntMappingNode(struct intMappingNode * node) {
   finiMappingValue(node->val);
   free(node);
}

void intMappingInsert(int id, struct mappingValue * val, struct intMapping * matching) {
   unsigned int pos = id % MAPPING_SIZE;
   struct intMappingNode * head = matching->node[pos];
   while (head != NULL) {
      if (id == head->id) {
         finiMappingValue(head->val);
         head->val = val;
         return;
      }
      head = head->next_in_hash;
   }
   struct intMappingNode * node = initIntMappingNode(id, val);

   // maintain next & prev
   if (matching->head == NULL) {
      matching->head = node;
   } else {
      matching->head->prev = node;
      node->next = matching->head;
      matching->head = node;
   }

   // maintain next_in_hash
   node->next_in_hash = matching->node[pos];
   matching->node[pos] = node;
}

void intMappingErase(int id, struct intMapping * matching) {
   unsigned int pos = id % MAPPING_SIZE;
   struct intMappingNode * head = matching->node[pos];
   while (head != NULL) {
      if (head->id == id) {
         if (head->prev) head->prev->next = head->next;
         if (head->next) head->next->prev = head->prev;
         if (head == matching->head) matching->head = head->next;
         if (matching->node[pos] == head) matching->node[pos] = head->next_in_hash;
         finiIntMappingNode(head);
         break;
      }
      head = head->next_in_hash;
   }
}

struct mappingValue * intMappingFind(int id, struct intMapping * matching) {
   unsigned int pos = id % MAPPING_SIZE;
   struct intMappingNode * head = matching->node[pos];
   while (head != NULL) {
      if (id == head->id) return head->val;
      head = head->next_in_hash;
   }
   return NULL;
}

int intMappingIn(int id, struct intMapping * matching) {
   unsigned int pos = id % MAPPING_SIZE;
   struct intMappingNode * head = matching->node[pos];
   while (head != NULL) {
      if (id == head->id) return 1;
      head = head->next_in_hash;
   }
   return 0;
}

struct intMapping * intMappingCopy(struct intMapping * matching) {
   struct intMapping * ret = initIntMapping();
   for (struct intMappingNode * cur = matching->head; cur != NULL; cur = cur->next)
      intMappingInsert(cur->id, mappingValueCopy(cur->val), ret);
   return ret;
}

struct intMapping * intMappingDeepCopy(struct intMapping * matching) {
   struct intMapping * ret = initIntMapping();
   for (struct intMappingNode * cur = matching->head; cur != NULL; cur = cur->next)
      intMappingInsert(cur->id, mappingValueDeepCopy(cur->val), ret);
   return ret;
}

void finiIntMapping(struct intMapping * matching) {
   struct intMappingNode * cur = matching->head;
   while (cur != NULL) {
      struct intMappingNode * next = cur->next;
      finiIntMappingNode(cur);
      cur = next;
   }
   free(matching);
}