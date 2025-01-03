#ifndef LIST_H
#define LIST_H

#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#define DECLARE_LIST(LISTNAME, TYPE1, FIELD1) \
      struct LISTNAME##Node { \
         TYPE1 FIELD1; \
         struct LISTNAME##Node *next; \
      }; \
      struct LISTNAME { \
         struct LISTNAME##Node *head; \
         struct LISTNAME##Node *tail; \
      }; \
      \
      int LISTNAME##IsEmpty(struct LISTNAME *list); \
      int LISTNAME##Length(struct LISTNAME *list); \
      struct LISTNAME *LISTNAME##Nil(); \
      struct LISTNAME *LISTNAME##Cons(TYPE1 FIELD1, struct LISTNAME *list); \
      struct LISTNAME *LISTNAME##Snoc(TYPE1 FIELD1, struct LISTNAME *list); \
      struct LISTNAME *LISTNAME##ConsByNode(struct LISTNAME##Node *node, struct LISTNAME *list); \
      struct LISTNAME *LISTNAME##Snoc(TYPE1 FIELD1, struct LISTNAME *list); \
      struct LISTNAME *LISTNAME##SnocByNode(struct LISTNAME##Node *node, struct LISTNAME *list); \
      struct LISTNAME *LISTNAME##Remove(struct LISTNAME *list, struct LISTNAME##Node *node); \
      struct LISTNAME *LISTNAME##Link(struct LISTNAME *list1, struct LISTNAME *list2); \
      struct LISTNAME *LISTNAME##Reverse(struct LISTNAME *list); \
      struct LISTNAME##Node *LISTNAME##NodeDeepCopy(struct LISTNAME##Node *node); \
      struct LISTNAME *LISTNAME##DeepCopy(struct LISTNAME *list); \
      void LISTNAME##NodeFree(struct LISTNAME##Node *node); \
      void LISTNAME##Free(struct LISTNAME *list); \
      void LISTNAME##Print(struct LISTNAME *list); \

#define DEFINE_LIST(LISTNAME, TYPE1, FIELD1) \
      int LISTNAME##IsEmpty(struct LISTNAME *list) { \
         return list->head == NULL; \
      } \
      int LISTNAME##Length(struct LISTNAME *list) { \
         int len = 0; \
         struct LISTNAME##Node *node = list->head; \
         while (node != NULL) { \
            len++; \
            node = node->next; \
         } \
         return len; \
      } \
      struct LISTNAME *LISTNAME##Nil() { \
         struct LISTNAME *list = (struct LISTNAME *)malloc(sizeof(struct LISTNAME)); \
         list->head = NULL; \
         list->tail = NULL; \
         return list; \
      } \
      \
      struct LISTNAME *LISTNAME##Cons(TYPE1 FIELD1, struct LISTNAME *list) { \
         struct LISTNAME##Node *node = (struct LISTNAME##Node *)malloc(sizeof(struct LISTNAME##Node)); \
         node->FIELD1 = FIELD1; \
         node->next = NULL; \
         if (list->head == NULL) { \
            list->head = node; \
            list->tail = node; \
         } else { \
            node->next = list->head; \
            list->head = node; \
         } \
         return list; \
      } \
      \
      struct LISTNAME *LISTNAME##ConsByNode(struct LISTNAME##Node *node, struct LISTNAME *list) { \
         node->next = NULL; \
         if (list->head == NULL) { \
            list->head = node; \
            list->tail = node; \
         } else { \
            node->next = list->head; \
            list->head = node; \
         } \
         return list; \
      } \
      struct LISTNAME *LISTNAME##Snoc(TYPE1 FIELD1, struct LISTNAME *list) { \
         struct LISTNAME##Node *node = (struct LISTNAME##Node *)malloc(sizeof(struct LISTNAME##Node)); \
         node->FIELD1 = FIELD1; \
         node->next = NULL; \
         if (list->head == NULL) { \
            list->head = node; \
            list->tail = node; \
         } else { \
            list->tail->next = node; \
            list->tail = node; \
         } \
         return list; \
      } \
      \
      struct LISTNAME *LISTNAME##SnocByNode(struct LISTNAME##Node *node, struct LISTNAME *list) { \
         node->next = NULL; \
         if (list->head == NULL) { \
            list->head = node; \
            list->tail = node; \
         } else { \
            list->tail->next = node; \
            list->tail = node; \
         } \
         return list; \
      } \
      struct LISTNAME *LISTNAME##Remove(struct LISTNAME *list, struct LISTNAME##Node *node) { \
         if (list->head == node) { \
            list->head = node->next; \
            if (list->tail == node) { \
               list->tail = NULL; \
            } \
         } else { \
            struct LISTNAME##Node *prev = list->head; \
            while (prev->next != node) { \
               prev = prev->next; \
            } \
            prev->next = node->next; \
            if (list->tail == node) { \
               list->tail = prev; \
            } \
         } \
         LISTNAME##NodeFree(node); \
         return list; \
      } \
      \
      struct LISTNAME *LISTNAME##Link(struct LISTNAME *list1, struct LISTNAME *list2) { \
         if (list1->head == NULL) { \
            return list2; \
         } else if (list2->head == NULL) { \
            return list1; \
         } else { \
            list1->tail->next = list2->head; \
            list1->tail = list2->tail; \
            free(list2); \
            return list1; \
         } \
      } \
      \
      struct LISTNAME *LISTNAME##Reverse(struct LISTNAME *list) { \
         struct LISTNAME##Node *prev = NULL; \
         struct LISTNAME##Node *curr = list->head; \
         while (curr != NULL) { \
            struct LISTNAME##Node *next; \
            next = curr->next; \
            curr->next = prev; \
            prev = curr; \
            curr = next; \
         } \
         list->tail = list->head; \
         list->head = prev; \
         return list; \
      } \
      \
      struct LISTNAME *LISTNAME##DeepCopy(struct LISTNAME *list) { \
         struct LISTNAME *new_list = LISTNAME##Nil(); \
         struct LISTNAME##Node *node = list->head; \
         while (node != NULL) { \
            new_list = LISTNAME##SnocByNode(LISTNAME##NodeDeepCopy(node), new_list); \
            node = node->next; \
         } \
         return new_list; \
      } \
      \
      void LISTNAME##Free(struct LISTNAME *list) { \
         struct LISTNAME##Node *node = list->head; \
         while (node != NULL) { \
            struct LISTNAME##Node *next = node->next; \
            LISTNAME##NodeFree(node); \
            node = next; \
         } \
         free(list); \
      } \

#define DECLARE_LIST2(LISTNAME, TYPE1, FIELD1, TYPE2, FIELD2) \
      struct LISTNAME##Node { \
         TYPE1 FIELD1; \
         TYPE2 FIELD2; \
         struct LISTNAME##Node *next; \
      }; \
      struct LISTNAME { \
         struct LISTNAME##Node *head; \
         struct LISTNAME##Node *tail; \
      }; \
      \
      int LISTNAME##IsEmpty(struct LISTNAME *list); \
      int LISTNAME##Length(struct LISTNAME *list); \
      struct LISTNAME *LISTNAME##Nil(); \
      struct LISTNAME *LISTNAME##Cons(TYPE1 FIELD1, TYPE2 FIELD2, struct LISTNAME *list); \
      struct LISTNAME *LISTNAME##ConsByNode(struct LISTNAME##Node *node, struct LISTNAME *list); \
      struct LISTNAME *LISTNAME##Snoc(TYPE1 FIELD1, TYPE2 FIELD2, struct LISTNAME *list); \
      struct LISTNAME *LISTNAME##SnocByNode(struct LISTNAME##Node *node, struct LISTNAME *list); \
      struct LISTNAME *LISTNAME##Remove(struct LISTNAME *list, struct LISTNAME##Node *node); \
      struct LISTNAME *LISTNAME##Link(struct LISTNAME *list1, struct LISTNAME *list2); \
      struct LISTNAME *LISTNAME##Reverse(struct LISTNAME *list); \
      struct LISTNAME##Node *LISTNAME##NodeDeepCopy(struct LISTNAME##Node *node); \
      struct LISTNAME *LISTNAME##DeepCopy(struct LISTNAME *list); \
      void LISTNAME##NodeFree(struct LISTNAME##Node *node); \
      void LISTNAME##Free(struct LISTNAME *list); \
      void LISTNAME##Print(struct LISTNAME *list); \

#define DEFINE_LIST2(LISTNAME, TYPE1, FIELD1, TYPE2, FIELD2) \
      int LISTNAME##IsEmpty(struct LISTNAME *list) { \
         return list->head == NULL; \
      } \
      int LISTNAME##Length(struct LISTNAME *list) { \
         int len = 0; \
         struct LISTNAME##Node *node = list->head; \
         while (node != NULL) { \
            len++; \
            node = node->next; \
         } \
         return len; \
      } \
      struct LISTNAME *LISTNAME##Nil() { \
         struct LISTNAME *list = (struct LISTNAME *)malloc(sizeof(struct LISTNAME)); \
         list->head = NULL; \
         list->tail = NULL; \
         return list; \
      } \
      \
      struct LISTNAME *LISTNAME##Cons(TYPE1 FIELD1, TYPE2 FIELD2, struct LISTNAME *list) { \
         struct LISTNAME##Node *node = (struct LISTNAME##Node *)malloc(sizeof(struct LISTNAME##Node)); \
         node->FIELD1 = FIELD1; \
         node->FIELD2 = FIELD2; \
         node->next = NULL; \
         if (list->head == NULL) { \
            list->head = node; \
            list->tail = node; \
         } else { \
            node->next = list->head; \
            list->head = node; \
         } \
         return list; \
      } \
      \
      struct LISTNAME *LISTNAME##ConsByNode(struct LISTNAME##Node *node, struct LISTNAME *list) { \
         node->next = NULL; \
         if (list->head == NULL) { \
            list->head = node; \
            list->tail = node; \
         } else { \
            node->next = list->head; \
            list->head = node; \
         } \
         return list; \
      } \
      struct LISTNAME *LISTNAME##Snoc(TYPE1 FIELD1, TYPE2 FIELD2, struct LISTNAME *list) { \
         struct LISTNAME##Node *node = (struct LISTNAME##Node *)malloc(sizeof(struct LISTNAME##Node)); \
         node->FIELD1 = FIELD1; \
         node->FIELD2 = FIELD2; \
         node->next = NULL; \
         if (list->head == NULL) { \
            list->head = node; \
            list->tail = node; \
         } else { \
            list->tail->next = node; \
            list->tail = node; \
         } \
         return list; \
      } \
      \
      struct LISTNAME *LISTNAME##SnocByNode(struct LISTNAME##Node *node, struct LISTNAME *list) { \
         node->next = NULL; \
         if (list->head == NULL) { \
            list->head = node; \
            list->tail = node; \
         } else { \
            list->tail->next = node; \
            list->tail = node; \
         } \
         return list; \
      } \
      struct LISTNAME *LISTNAME##Remove(struct LISTNAME *list, struct LISTNAME##Node *node) { \
         if (list->head == node) { \
            list->head = node->next; \
            if (list->tail == node) { \
               list->tail = NULL; \
            } \
         } else { \
            struct LISTNAME##Node *prev = list->head; \
            while (prev->next != node) { \
               prev = prev->next; \
            } \
            prev->next = node->next; \
            if (list->tail == node) { \
               list->tail = prev; \
            } \
         } \
         LISTNAME##NodeFree(node); \
         return list; \
      } \
      \
      struct LISTNAME *LISTNAME##Link(struct LISTNAME *list1, struct LISTNAME *list2) { \
         if (list1->head == NULL) { \
            return list2; \
         } else if (list2->head == NULL) { \
            return list1; \
         } else { \
            list1->tail->next = list2->head; \
            list1->tail = list2->tail; \
            free(list2); \
            return list1; \
         } \
      } \
      \
      struct LISTNAME *LISTNAME##Reverse(struct LISTNAME *list) { \
         struct LISTNAME##Node *prev = NULL; \
         struct LISTNAME##Node *curr = list->head; \
         while (curr != NULL) { \
            struct LISTNAME##Node *next; \
            next = curr->next; \
            curr->next = prev; \
            prev = curr; \
            curr = next; \
         } \
         list->tail = list->head; \
         list->head = prev; \
         return list; \
      } \
      \
      struct LISTNAME *LISTNAME##DeepCopy(struct LISTNAME *list) { \
         struct LISTNAME *new_list = LISTNAME##Nil(); \
         struct LISTNAME##Node *node = list->head; \
         while (node != NULL) { \
            new_list = LISTNAME##SnocByNode(LISTNAME##NodeDeepCopy(node), new_list); \
            node = node->next; \
         } \
         return new_list; \
      } \
      \
      void LISTNAME##Free(struct LISTNAME *list) { \
         struct LISTNAME##Node *node = list->head; \
         while (node != NULL) { \
            struct LISTNAME##Node *next = node->next; \
            LISTNAME##NodeFree(node); \
            node = next; \
         } \
         free(list); \
      } \

#define DECLARE_LIST3(LISTNAME, TYPE1, FIELD1, TYPE2, FIELD2, TYPE3, FIELD3) \
      struct LISTNAME##Node { \
         TYPE1 FIELD1; \
         TYPE2 FIELD2; \
         TYPE3 FIELD3; \
         struct LISTNAME##Node *next; \
      }; \
      struct LISTNAME { \
         struct LISTNAME##Node *head; \
         struct LISTNAME##Node *tail; \
      }; \
      \
      int LISTNAME##IsEmpty(struct LISTNAME *list); \
      int LISTNAME##Length(struct LISTNAME *list); \
      struct LISTNAME *LISTNAME##Nil(); \
      struct LISTNAME *LISTNAME##Cons(TYPE1 FIELD1, TYPE2 FIELD2, TYPE3 FIELD3, struct LISTNAME *list); \
      struct LISTNAME *LISTNAME##ConsByNode(struct LISTNAME##Node *node, struct LISTNAME *list); \
      struct LISTNAME *LISTNAME##Snoc(TYPE1 FIELD1, TYPE2 FIELD2, TYPE3 FIELD3, struct LISTNAME *list); \
      struct LISTNAME *LISTNAME##SnocByNode(struct LISTNAME##Node *node, struct LISTNAME *list); \
      struct LISTNAME *LISTNAME##Remove(struct LISTNAME *list, struct LISTNAME##Node *node); \
      struct LISTNAME *LISTNAME##Link(struct LISTNAME *list1, struct LISTNAME *list2); \
      struct LISTNAME *LISTNAME##Reverse(struct LISTNAME *list); \
      struct LISTNAME##Node *LISTNAME##NodeDeepCopy(struct LISTNAME##Node *node); \
      struct LISTNAME *LISTNAME##DeepCopy(struct LISTNAME *list); \
      void LISTNAME##NodeFree(struct LISTNAME##Node *node); \
      void LISTNAME##Free(struct LISTNAME *list); \
      void LISTNAME##Print(struct LISTNAME *list); \

#define DEFINE_LIST3(LISTNAME, TYPE1, FIELD1, TYPE2, FIELD2, TYPE3, FIELD3) \
      int LISTNAME##IsEmpty(struct LISTNAME *list) { \
         return list->head == NULL; \
      } \
      int LISTNAME##Length(struct LISTNAME *list) { \
         int len = 0; \
         struct LISTNAME##Node *node = list->head; \
         while (node != NULL) { \
            len++; \
            node = node->next; \
         } \
         return len; \
      } \
      struct LISTNAME *LISTNAME##Nil() { \
         struct LISTNAME *list = (struct LISTNAME *)malloc(sizeof(struct LISTNAME)); \
         list->head = NULL; \
         list->tail = NULL; \
         return list; \
      } \
      \
      struct LISTNAME *LISTNAME##Cons(TYPE1 FIELD1, TYPE2 FIELD2, TYPE3 FIELD3, struct LISTNAME *list) { \
         struct LISTNAME##Node *node = (struct LISTNAME##Node *)malloc(sizeof(struct LISTNAME##Node)); \
         node->FIELD1 = FIELD1; \
         node->FIELD2 = FIELD2; \
         node->FIELD3 = FIELD3; \
         node->next = NULL; \
         if (list->head == NULL) { \
            list->head = node; \
            list->tail = node; \
         } else { \
            node->next = list->head; \
            list->head = node; \
         } \
         return list; \
      } \
      \
      struct LISTNAME *LISTNAME##ConsByNode(struct LISTNAME##Node *node, struct LISTNAME *list) { \
         node->next = NULL; \
         if (list->head == NULL) { \
            list->head = node; \
            list->tail = node; \
         } else { \
            node->next = list->head; \
            list->head = node; \
         } \
         return list; \
      } \
      struct LISTNAME *LISTNAME##Snoc(TYPE1 FIELD1, TYPE2 FIELD2, TYPE3 FIELD3, struct LISTNAME *list) { \
         struct LISTNAME##Node *node = (struct LISTNAME##Node *)malloc(sizeof(struct LISTNAME##Node)); \
         node->FIELD1 = FIELD1; \
         node->FIELD2 = FIELD2; \
         node->FIELD3 = FIELD3; \
         node->next = NULL; \
         if (list->head == NULL) { \
            list->head = node; \
            list->tail = node; \
         } else { \
            list->tail->next = node; \
            list->tail = node; \
         } \
         return list; \
      } \
      \
      struct LISTNAME *LISTNAME##SnocByNode(struct LISTNAME##Node *node, struct LISTNAME *list) { \
         node->next = NULL; \
         if (list->head == NULL) { \
            list->head = node; \
            list->tail = node; \
         } else { \
            list->tail->next = node; \
            list->tail = node; \
         } \
         return list; \
      } \
      \
      struct LISTNAME *LISTNAME##Remove(struct LISTNAME *list, struct LISTNAME##Node *node) { \
         if (list->head == node) { \
            list->head = node->next; \
            if (list->tail == node) { \
               list->tail = NULL; \
            } \
         } else { \
            struct LISTNAME##Node *prev = list->head; \
            while (prev->next != node) { \
               prev = prev->next; \
            } \
            prev->next = node->next; \
            if (list->tail == node) { \
               list->tail = prev; \
            } \
         } \
         LISTNAME##NodeFree(node); \
         return list; \
      } \
      \
      struct LISTNAME *LISTNAME##Link(struct LISTNAME *list1, struct LISTNAME *list2) { \
         if (list1->head == NULL) { \
            return list2; \
         } else if (list2->head == NULL) { \
            return list1; \
         } else { \
            list1->tail->next = list2->head; \
            list1->tail = list2->tail; \
            free(list2); \
            return list1; \
         } \
      } \
      \
      struct LISTNAME *LISTNAME##Reverse(struct LISTNAME *list) { \
         struct LISTNAME##Node *prev = NULL; \
         struct LISTNAME##Node *curr = list->head; \
         while (curr != NULL) { \
            struct LISTNAME##Node *next; \
            next = curr->next; \
            curr->next = prev; \
            prev = curr; \
            curr = next; \
         } \
         list->tail = list->head; \
         list->head = prev; \
         return list; \
      } \
      \
      struct LISTNAME *LISTNAME##DeepCopy(struct LISTNAME *list) { \
         struct LISTNAME *new_list = LISTNAME##Nil(); \
         struct LISTNAME##Node *node = list->head; \
         while (node != NULL) { \
            new_list = LISTNAME##SnocByNode(LISTNAME##NodeDeepCopy(node), new_list); \
            node = node->next; \
         } \
         return new_list; \
      } \
      \
      void LISTNAME##Free(struct LISTNAME *list) { \
         struct LISTNAME##Node *node = list->head; \
         while (node != NULL) { \
            struct LISTNAME##Node *next = node->next; \
            LISTNAME##NodeFree(node); \
            node = next; \
         } \
         free(list); \
      } \

DECLARE_LIST(IntList, int, data)
DECLARE_LIST(StringList, char*, data)
DECLARE_LIST2(GlobVarList,char*,name,char*,value)

struct StringList *StringListSort(struct StringList * list);

struct StringList *StringListUnique(struct StringList * list);

/* test code */

/*

struct IntData {
   int data;
};

DECLARE_LIST(IntList, struct IntData*, data)
DEFINE_LIST(IntList, struct IntData*, data)

struct IntListNode * IntListNodeDeepCopy(struct IntListNode *node) {
   struct IntListNode *new_node = (struct IntListNode *) malloc(sizeof(struct IntListNode));
   new_node->data = (struct IntData *) malloc(sizeof(struct IntData));
   new_node->data->data = node->data->data;
   new_node->next = NULL;
   return new_node;
}

void IntListNodeFree(struct IntListNode *node) {
   free(node->data);
   free(node);
}

int main() {
   struct IntList * l;
   l = IntListNil();
   struct IntData * d = (struct IntData *) malloc(sizeof(struct IntData));
   d->data = 1;
   l = IntListCons(d, l);
   d = (struct IntData *) malloc(sizeof(struct IntData));
   d->data = 2;
   l = IntListCons(d, l);
   d = (struct IntData *) malloc(sizeof(struct IntData));
   d->data = 3;
   l = IntListCons(d, l);
   struct IntListNode * iter;
   printf("l:\n");
   for (iter = l->head; iter != NULL; iter = iter->next) {
      printf("%d ", iter->data->data);
      if (iter->next == NULL) {
         printf("\n");
      }
   }
   struct IntList * l2 = IntListDeepCopy(l);
   IntListFree(l);
   printf("l2:\n");
   for (iter = l2->head; iter != NULL; iter = iter->next) {
      printf("%d ", iter->data->data);
      if (iter->next == NULL) {
         printf("\n");
      }
   }

   l = IntListNil();
   d = (struct IntData *) malloc(sizeof(struct IntData));
   d->data = 1;
   l = IntListSnoc(d, l);
   d = (struct IntData *) malloc(sizeof(struct IntData));
   d->data = 2;
   l = IntListSnoc(d, l);
   d = (struct IntData *) malloc(sizeof(struct IntData));
   d->data = 3;
   l = IntListSnoc(d, l);
   printf("l:\n");
   for (iter = l->head; iter != NULL; iter = iter->next) {
      printf("%d ", iter->data->data);
   }
   struct IntList * l3 = IntListDeepCopy(l);
   IntListFree(l);
   printf("\nl3:\n");
   for (iter = l3->head; iter != NULL; iter = iter->next) {
      printf("%d ", iter->data->data);
      if (iter->next == NULL) {
         printf("\n");
      }
   }

   l2 = IntListLink(l2, l3);
   printf("l2:\n");
   for (iter = l2->head; iter != NULL; iter = iter->next) {
      printf("%d ", iter->data->data);
      if (iter->next == NULL) {
         printf("\n");
      }
   }

   struct IntListNode * node1 = l2->head;
   struct IntListNode * node2 = node1->next->next;
   l2 = IntListRemove(l2, node1);
   l2 = IntListRemove(l2, node2);
   printf("l2:\n");
   for (iter = l2->head; iter != NULL; iter = iter->next) {
      printf("%d ", iter->data->data);
      if (iter->next == NULL) {
         printf("\n");
      }
   }

   l2 = IntListReverse(l2);
   printf("l2:\n");
   for (iter = l2->head; iter != NULL; iter = iter->next) {
      printf("%d ", iter->data->data);
      if (iter->next == NULL) {
         printf("\n");
      }
   }

   IntListFree(l2);

   return 0;
}

*/

#endif // LIST_H