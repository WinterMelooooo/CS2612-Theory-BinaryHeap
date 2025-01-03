int rev(int (*cmp)(int, int), int x, int y) {
  return cmp(y, x);
}

int less(int x, int y) {
  return x < y;
}

int f(int a[10]);
int g(int *p);

int m() {
  int x = rev(less, 2, 1),
      y = rev(&less, 3, 4);
  int (*h)(int *) = f;
  int (*i)(int [5]) = g;
  ********f;
  int t = f == f && f == *h && *h == *h;
}

struct blist {
  void *key;
  void *val;
  struct blist *next;
  /* for traversal */
  struct blist *down;
  struct blist *up;
};

struct hashtbl {
  unsigned int (*hash)(void *);
  int (*equal)(void *, void *);
  struct blist **bucks;
  struct blist *top;
};

void init_hashtbl(struct hashtbl *h, unsigned int hash(void *), int (*equal)(void *, void *)) {
  h->hash = hash;
  h->equal = equal;
  h->bucks = (void *)0;
  h->top = (void *)0;
}

void *hashtbl_find(struct hashtbl *h, void *key, int *valid) {
  unsigned int ind;
  struct blist *i;

  if (h->bucks == (void *)0) {
    *valid = 0;
    return (void *)0;
  }

  ind = h->hash(key) % (unsigned int)211;
  for (i = h->bucks[ind]; i != (void *)0; i = i->next)
    if (h->equal(key, i->key)) {
      *valid = 1;
      return i->val;
    }
  *valid = 0;
  return (void *)0;
}

typedef int T;
typedef int F(int (T));
F fff, ggg;
