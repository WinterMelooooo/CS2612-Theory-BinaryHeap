#include "CharMapping.h"

static unsigned StringHash(const char* str)
{
    // One-byte-at-a-time hash based on Murmur's mix
    // Source: https://github.com/aappleby/smhasher/blob/master/src/Hashes.cpp
   unsigned h = 0;
    for (; *str; ++str) {
        h ^= *str;
        h *= 0x5bd1e995;
        h ^= h >> 15;
    }
    return h;
}

static struct charMappingNode * initCharMappingNode(char * var, struct mappingValue * val, int isown) {
   struct charMappingNode * node = (struct charMappingNode *)malloc(sizeof(struct charMappingNode));
   node->var = isown ? strdup(var) : var;
   node->val = val;
   node->next = node->prev = node->next_in_hash = NULL;
   return node;
}

static void finiCharMappingNode(struct charMappingNode * node, int isown) {
   if (isown) free(node->var);
   finiMappingValue(node->val);
   free(node);
}

struct charMapping * initCharMapping(int own_key) {
   struct charMapping * matching = (struct charMapping *)malloc(sizeof(struct charMapping));
   matching->own_key = own_key;
   matching->head = NULL;
   for (int i = 0; i < MAPPING_SIZE; i++)
      matching->node[i] = NULL;
   return matching;
}

void charMappingInsert(char * var, struct mappingValue * val, struct charMapping * matching) {
   unsigned pos = StringHash(var) % MAPPING_SIZE;
   struct charMappingNode * head = matching->node[pos];
   while (head != NULL) {
      if (strcmp(head->var, var) == 0) {
         finiMappingValue(head->val);
         head->val = val;
         return;
      }
      head = head->next_in_hash;
   }
   struct charMappingNode * node = initCharMappingNode(var, val, matching->own_key);

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

void charMappingErase(char * var, struct charMapping * matching) {
   unsigned pos = StringHash(var) % MAPPING_SIZE;
   struct charMappingNode * head = matching->node[pos];
   while (head != NULL) {
      if (strcmp(head->var, var) == 0) {
         if (head->prev) head->prev->next = head->next;
         if (head->next) head->next->prev = head->prev;
         if (head == matching->head) matching->head = head->next;
         if (matching->node[pos] == head) matching->node[pos] = head->next_in_hash;
         finiCharMappingNode(head, matching->own_key);
         break;
      }
      head = head->next_in_hash;
   }
}

struct mappingValue * charMappingFind(char * var, struct charMapping * matching) {
   unsigned pos = StringHash(var) % MAPPING_SIZE;
   struct charMappingNode * head = matching->node[pos];
   while (head != NULL) {
      if (strcmp(head->var, var) == 0) return head->val;
      head = head->next_in_hash;
   }
   return NULL;
}

int charMappingIn(char * var, struct charMapping * matching) {
   unsigned pos = StringHash(var) % MAPPING_SIZE;
   struct charMappingNode * head = matching->node[pos];
   while (head != NULL) {
      if (strcmp(head->var, var) == 0) return 1;
      head = head->next_in_hash;
   }
   return 0;
}

struct charMapping * charMappingCopy(struct charMapping * matching) {
   struct charMapping * ret = initCharMapping(matching->own_key);
   for (struct charMappingNode * cur = matching->head; cur != NULL; cur = cur->next)
      charMappingInsert(cur->var, mappingValueCopy(cur->val), ret);
   return ret;
}

struct charMapping * charMappingDeepCopy(struct charMapping * matching) {
   struct charMapping * ret = initCharMapping(1);
   for (struct charMappingNode * cur = matching->head; cur != NULL; cur = cur->next)
      charMappingInsert(cur->var, mappingValueDeepCopy(cur->val), ret);
   return ret;
}

void finiCharMapping(struct charMapping * matching) {
   struct charMappingNode * cur = matching->head;
   while (cur != NULL) {
      struct charMappingNode * next = cur->next;
      finiCharMappingNode(cur, matching->own_key);
      cur = next;
   }
   free(matching);
}