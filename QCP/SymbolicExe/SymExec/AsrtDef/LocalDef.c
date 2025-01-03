#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <stdio.h>

#include "LocalDef.h"

unsigned char IntHash(int id) {
   return id % LOCALMOD;
}

struct LocalLinkedHashMap * CreateLocalLinkedHashMap() {
   struct LocalLinkedHashMap * res = malloc(sizeof(struct LocalLinkedHashMap));
   res->head = NULL;
   for (int i = 0; i < LOCALMOD; ++i) {
      res->node[i].state = 0;
   }
   res->size = 0;
   return res;
}

// return 1 if success, 0 if fail
int LocalInsert(int id, struct ExprVal * expr, struct LocalLinkedHashMap * map) {
   if (map->size == LOCALMOD) return 0;
   unsigned char h = IntHash(id);
   unsigned char p = h;
   do {
      if (map->node[p].state != 1) {
         map->node[p].hash_code = h;
         map->node[p].id = id;
         map->node[p].value = ExprValDeepCopy(expr);
         map->node[p].next = map->head;
         map->node[p].prev = NULL;
         if (map->head != NULL) {
            map->head->prev = &(map->node[p]);
         }
         map->node[p].state = 1;
         map->head = &(map->node[p]);
         ++map->size;
         return 1;
      } else if (map->node[p].id == id) {
         return 0;
      }
      ++p;
   } while (p != h);
   return 0;
}

struct ExprVal * LocalFind (int id, struct LocalLinkedHashMap * map) {
   unsigned char h = IntHash(id);
   unsigned char p = h;
   do {
      if (map->node[p].state == 0) {
         return NULL;
      } else if (map->node[p].state == 1 && map->node[p].id == id) {
         return map->node[p].value;
      }
      ++p;
   } while (p != h);
   return NULL;
}

struct LocalLinkedHashMap * LocalListDeepCopy(struct LocalLinkedHashMap * local) {
   struct LocalLinkedHashMap * ret = CreateLocalLinkedHashMap();
   for (int i = 0; i < LOCALMOD; ++i) {
      if (local->node[i].state == 1) {
         LocalInsert(local->node[i].id, local->node[i].value, ret);
      }
   }
   return ret;
}

// return 1 if success, 0 if fail(not found)
int LocalErase(int id, struct LocalLinkedHashMap * map) {
   unsigned char h = IntHash(id);
   unsigned char p = h;
   do {
      if (map->node[p].state == 0) {
         return 0;
      }
      if (map->node[p].state == 1 && map->node[p].id == id) {
         if (map->node[p].prev != NULL) {
            map->node[p].prev->next = map->node[p].next;
         }
         if (map->node[p].next != NULL) {
            map->node[p].next->prev = map->node[p].prev;
         }
         if (map->head == &(map->node[p])) {
            map->head = map->node[p].next;
         }
         ExprValFree(map->node[p].value);
         map->node[p].state = 2;
         --map->size;
         return 1;
      }
      ++p;
   } while (p != h);
   return 0;
}

struct LocalLinkedHashMap * LocalLinkedHashMapSubst(struct LocalLinkedHashMap * local, 
                                                    struct ExprVal * pre, struct ExprVal * post) {
   struct LocalLinkedHashMapNode * node = local->head;
   while (node != NULL) {
      node->value = ExprValSubst(node->value, pre, post);
      node = node->next;
   }
   return local;
}

struct LocalLinkedHashMap * LocalLinkedHashMapSubstPolyType(struct LocalLinkedHashMap * local, 
                                                        struct PolyType * pre, struct PolyType * post) {
   struct LocalLinkedHashMapNode * node = local->head;
   while (node != NULL) {
      node->value = ExprValSubstPolyType(node->value, pre, post);
      node = node->next;
   }
   return local;
}

struct LocalLinkedHashMap * LocalLinkedHashMapMerge(struct LocalLinkedHashMap * left, 
                                                    struct LocalLinkedHashMap * right) {
   struct LocalLinkedHashMapNode * node = right->head;
   while (node != NULL) {
      LocalInsert(node->id, node->value, left);
      node = node->next;
   }
   LocalLinkedHashMapFree(right);
   return left;
}

void LocalLinkedHashMapFree(struct LocalLinkedHashMap * map) {
   struct LocalLinkedHashMapNode * node = map->head;
   while (node != NULL) {
      struct LocalLinkedHashMapNode * next = node->next;
      ExprValFree(node->value);
      node = next;
   }
   free(map);
}
