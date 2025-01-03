#ifndef LOCAL_INCLUDED
#define LOCAL_INCLUDED

#include "ExprValDef.h"

#define LOCALMOD 256 // 自然溢出
#define LOCALBASE 131

enum LocalType {
   T_AVAR,
};

struct Local {
   enum LocalType t;
   union {
      struct { int id; struct ExprVal * expr; } AVAR;
   }d;
};

// state = 0, unused
// state = 1, used
// state = 2, tombstone
struct LocalLinkedHashMapNode { // only for T_AVAR
   int id;
   struct ExprVal * value;      // Hashmap own the memory of value
   unsigned char hash_code, state;
   struct LocalLinkedHashMapNode *next, * prev;  // for linked hashmap
};

struct LocalLinkedHashMap {
   int size;
   struct LocalLinkedHashMapNode * head;
   struct LocalLinkedHashMapNode node[LOCALMOD];
};

unsigned char IntHash(int id);

struct LocalLinkedHashMap * CreateLocalLinkedHashMap();
int LocalInsert(int id, struct ExprVal * expr, struct LocalLinkedHashMap * map);
struct ExprVal * LocalFind (int id, struct LocalLinkedHashMap * map);
struct LocalLinkedHashMap * LocalListDeepCopy(struct LocalLinkedHashMap * local);
int LocalErase(int id, struct LocalLinkedHashMap * map);
struct LocalLinkedHashMap * LocalLinkedHashMapSubst(struct LocalLinkedHashMap * local, 
                                                    struct ExprVal * pre, struct ExprVal * post);
struct LocalLinkedHashMap * LocalLinkedHashMapSubstPolyType(struct LocalLinkedHashMap * local, 
                                                        struct PolyType * pre, struct PolyType * post);
struct LocalLinkedHashMap * LocalLinkedHashMapMerge(struct LocalLinkedHashMap * left, 
                                                    struct LocalLinkedHashMap * right);
void LocalLinkedHashMapFree(struct LocalLinkedHashMap * map);

#endif