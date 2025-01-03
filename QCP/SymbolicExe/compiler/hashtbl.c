#include "hashtbl.h"
#include "utils.h"

void ensure_bucks(struct hashtbl *h) {
  if (h->bucks != NULL)
    return;
  int i;
  h->bucks = (struct blist **)malloc(NBUCK * sizeof(struct blist *));
  for (i = 0; i < NBUCK; i++)
    h->bucks[i] = NULL;
}

void init_hashtbl(struct hashtbl *h, unsigned int (*hash)(void *x), int (*equal)(void *l, void *r)) {
  h->hash = hash;
  h->equal = equal;
  h->bucks = NULL;
  h->top = NULL;
}

struct hashtbl *create_hashtbl(unsigned int (*hash)(void *x), int (*equal)(void *l, void *r)) {
  struct hashtbl *h;
  h = malloc(sizeof(struct hashtbl));
  if (h == NULL)
    failwith("failure in malloc().");
  init_hashtbl(h, hash, equal);
  return h;
}

void hashtbl_add(struct hashtbl *h, void *key, void *val) {
  unsigned int ind;
  struct blist *buc;

  ensure_bucks(h);

  ind = h->hash(key) % NBUCK;
  buc = malloc(sizeof(struct blist));
  if (buc == NULL)
    failwith("failure in malloc().");
  buc->key = key;
  buc->val = val;

  buc->up = NULL;
  buc->down = h->top;
  if (h->top != NULL)
    h->top->up = buc;
  h->top = buc;

  buc->next = h->bucks[ind];
  h->bucks[ind] = buc;
}

void *hashtbl_find(struct hashtbl *h, void *key, int *valid) {
  unsigned int ind;
  struct blist **i;

  if (h->bucks == NULL) {
    *valid = 0;
    return NULL;
  }

  ind = h->hash(key) % NBUCK;
  for (i = &h->bucks[ind]; *i != NULL; i = &(*i)->next)
    if (h->equal(key, (*i)->key)) {
      struct blist *b = *i;
      // LRU
      *i = b->next;
      b->next = h->bucks[ind];
      h->bucks[ind] = b;

      *valid = 1;
      return b->val;
    }
  *valid = 0;
  return NULL;
}

void **hashtbl_findref(struct hashtbl *h, void *key) {
  unsigned int ind;
  struct blist **i;

  if (h->bucks == NULL) {
    return NULL;
  }

  ind = h->hash(key) % NBUCK;
  for (i = &h->bucks[ind]; *i != NULL; i = &(*i)->next)
    if (h->equal(key, (*i)->key)) {
      struct blist *b = *i;
      // LRU
      *i = b->next;
      b->next = h->bucks[ind];
      h->bucks[ind] = b;

      return &b->val;
    }
  return NULL;
}


void *hashtbl_remove(struct hashtbl *h, void *key, int *removed) {
  unsigned int ind;
  struct blist **it;

  if (h->bucks == NULL)
    return 0;

  ind = h->hash(key) % NBUCK;
  for (it = &h->bucks[ind]; *it != NULL; it = &(*it)->next) {
    struct blist *b = *it;
    if (h->equal(key, b->key)) {
      if (h->top == b)
        h->top = b->down;

      if (b->up != NULL)
        b->up->down = b->down;
      if (b->down != NULL)
        b->down->up = b->up;

      *it = b->next;
      void *res = b->val;
      free(b);
      *removed = 1;
      return res;
    }
  }
  *removed = 0;
  return NULL;
}

void hashtbl_iter(struct hashtbl *h, void (*f)(void *key, void *val)) {
  struct blist *it;

  for (it = h->top; it != NULL;) {
    struct blist *down = it->down;
     f(it->key, it->val);
    it = down;
  }
}

void hashtbl_free_blist(struct blist *bl) {
  if (bl != NULL) {
    hashtbl_free_blist(bl->next);
    free(bl);
  }
}

void hashtbl_clear(struct hashtbl *h) {
  int i;

  if (h->bucks == NULL)
    return;

  for (i = 0; i < NBUCK; i++) {
    hashtbl_free_blist(h->bucks[i]);
    h->bucks[i] = NULL;
  }

  free(h->bucks);
  h->bucks = NULL;
  h->top = NULL;
}

void free_hashtbl(struct hashtbl *h) {
  hashtbl_clear(h);
  free(h);
}

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpointer-to-int-cast"

unsigned int hash_int(void *n) {
  return (unsigned int)n;
}
int int_equal(void *a, void *b) {
  return a == b;
}
unsigned int hash_uint(void *n) {
  return (unsigned int)n;
}
int uint_equal(void *a, void *b) {
  return a == b;
}

unsigned int hash_ptr(void *n) {
  return (unsigned int)n;
}
int ptr_equal(void *a, void *b) {
  return a == b;
}

#pragma GCC diagnostic pop

#define ROTL32(x,n) ((x) << n | (x) >> (32-n))

#define MIX(h,d) \
  d *= 0xcc9e2d51; \
  d = ROTL32(d, 15); \
  d *= 0x1b873593; \
  h ^= d; \
  h = ROTL32(h, 13); \
  h = h * 5 + 0xe6546b64;

#define FINAL_MIX(h) \
  h ^= h >> 16; \
  h *= 0x85ebca6b; \
  h ^= h >> 13; \
  h *= 0xc2b2ae35; \
  h ^= h >> 16;

#define  Byte_u(x, i) (((unsigned char *) (x)) [i])

unsigned int string_length(char *s) {
  unsigned int len = 0;
  for (; *s != '\0'; s++)
    len++;
  return len;
}

unsigned int caml_hash_mix_string(unsigned int h, char *s) {
  unsigned int len = string_length(s);
  unsigned int i;
  unsigned int w;

  /* Mix by 32-bit blocks (little-endian) */
  for (i = 0; i + 4 <= len; i += 4) {
    w = *((unsigned int *) &Byte_u(s, i));
    MIX(h, w);
  }
  /* Finish with up to 3 bytes */
  w = 0;
  switch (len & 3) {
  case 3: w  = Byte_u(s, i+2) << 16;   /* fallthrough */
  case 2: w |= Byte_u(s, i+1) << 8;    /* fallthrough */
  case 1: w |= Byte_u(s, i);
          MIX(h, w);
  default: /*skip*/;     /* len & 3 == 0, no extra bytes, do nothing */
  }
  /* Finally, mix in the length.  Ignore the upper 32 bits, generally 0. */
  h ^= len;
  return h;
}

unsigned int hash_string(void *str) {
  unsigned int h;
  h = 0xc4675a42; // ...
  h = caml_hash_mix_string(h, str);
  FINAL_MIX(h);
  return h;
}

int string_equal(void *s, void *d) {
  return !strcmp(s, d);
}
