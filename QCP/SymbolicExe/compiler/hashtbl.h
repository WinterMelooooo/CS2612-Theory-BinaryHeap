#ifndef HASHTBL_H
#define HASHTBL_H

#define NBUCK 211

struct blist {
  void *key;
  void *val;
  struct blist *next;
  /* for traversal */
  struct blist *down;
  struct blist *up;
};

struct hashtbl {
  unsigned int (*hash)(void *x);
  int (*equal)(void *l, void *r);
  struct blist **bucks;
  struct blist *top;
};

void init_hashtbl(struct hashtbl *h, unsigned int (*hash)(void *x), int (*equal)(void *l, void *r));
struct hashtbl *create_hashtbl(unsigned int (*hash)(void *x), int (*equal)(void *l, void *r));
void hashtbl_add(struct hashtbl *h, void *key, void *val);
void *hashtbl_find(struct hashtbl *h, void *key, int *valid);
void **hashtbl_findref(struct hashtbl *h, void *key);
/* do not free anything */
void *hashtbl_remove(struct hashtbl *h, void *key, int *removed);
void hashtbl_clear(struct hashtbl *h);
void free_hashtbl(struct hashtbl *h);
void hashtbl_iter(struct hashtbl *h, void (f)(void *key, void *val));

unsigned int hash_string(void *str);
int string_equal(void *src, void *dst);
unsigned int hash_int(void *n);
int int_equal(void *a, void *b);
unsigned int hash_uint(void *n);
int uint_equal(void *a, void *b);
unsigned int hash_ptr(void *n);
int ptr_equal(void *a, void *b);

#endif
