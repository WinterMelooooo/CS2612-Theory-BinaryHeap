#include "List.h"

DEFINE_LIST(IntList, int, data)

struct IntListNode* IntListNodeDeepCopy(struct IntListNode * node) {
   if (node == NULL) return NULL;
   struct IntListNode * res = (struct IntListNode *) malloc(sizeof(struct IntListNode));
   res->data = node->data;
   res->next = node->next;
   return res;
}

void IntListNodeFree(struct IntListNode * node) {
   if (node == NULL) return;
   free(node);
}

DEFINE_LIST(StringList, char *, data)

struct StringListNode* StringListNodeDeepCopy(struct StringListNode * node) {
   if (node == NULL) return NULL;
   struct StringListNode * res = (struct StringListNode *) malloc(sizeof(struct StringListNode));
   res->data = malloc(strlen(node->data) + 1);
   strcpy(res->data, node->data);
   res->next = node->next;
   return res;
}

void StringListNodeFree(struct StringListNode * node) {
   if (node == NULL) return;
   free(node->data);
   free(node);
}

struct StringListNode* StringListNodeSort(struct StringListNode * list) {
   if (list == NULL) return NULL;
   struct StringListNode *i, *j;
   for (i = list; i != NULL; i = i->next) {
      for (j = list; j->next != NULL; j = j->next) {
         if (strcmp(j->data, j->next->data) > 0) {
            char * tmp = j->data;
            j->data = j->next->data;
            j->next->data = tmp;
         }
      }
   }
   return list;
}

struct StringList * StringListSort(struct StringList *list) {
    if (list == NULL) return NULL;
    list -> head = StringListNodeSort(list -> head);
    return list;
}

struct StringList * StringListUnique(struct StringList *list) {
    if (list == NULL) return NULL;
    list = StringListSort(list);
    struct StringListNode *i = list ->head;
    while (i != NULL && i -> next != NULL) {
        if (strcmp(i -> data, i -> next -> data) == 0) {
            struct StringListNode *tmp = i -> next;
            i -> next = i -> next -> next;
            if (list -> tail == tmp) list -> tail = i;
            StringListNodeFree(tmp);
        } else {
            i = i -> next;
        }
    }
    return list;
}

DEFINE_LIST2(GlobVarList,char *,name,char *,value)

struct GlobVarListNode* GlobVarListNodeDeepCopy(struct GlobVarListNode *node){
   if (node == NULL) return NULL;
   struct GlobVarListNode * res = (struct GlobVarListNode *) malloc(sizeof(struct GlobVarListNode));
   res->name = malloc(strlen(node->name)+1);
   res->value = malloc(strlen(node->value)+1);
   strcpy(res->name,node->name);
   strcpy(res->value,node->value);
   res->next = node->next;
   return res;

}

void GlobVarListNodeFree(struct GlobVarListNode *node) {
   if (node == NULL) return;
   free(node->name);
   free(node->value);
   free(node);
}