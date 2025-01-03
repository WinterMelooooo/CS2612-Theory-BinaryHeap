// Predicates are classified to sep, which should be fixed

struct list {
  void *x;
  struct list *next;
};

/*@ Extern Coq (nil : {A} -> list A)
               (cons : {A} -> A -> list A -> list A)
               (append : {A} -> list A -> list A -> list A)
 */

/*@ Extern Coq (ordered : {A} -> (A -> A -> Prop) -> list A -> Prop) */

/*@ Let repr({A}; storeA : Z -> A -> Assertion, l, as) =
      l == 0 && as == nil ||
      exists a as_, repr(storeA, l->next, as_) &&
                    storeA(l->x, a) &&
                    as == cons(a, as_)
 */

struct list *merge(struct list *l1, struct list *l2, int (*cmp)(void *x, void *y))
/*@ With {A} storeA (le : A -> A -> Prop)
    Require exists as1 as2,
            repr(storeA, l1, as1) && repr(storeA, l2, as2) &&
            ordered(le, as1) && ordered(le, as2) &&
            cmp |= int (void *x, void *y)
                   With a b
                   Require emp && storeA(x, a) && storeA(y, b)
                   Ensure __return <= 0 && le(a, b) || __return > 0 && le(b, a)
    Ensure exists as, repr(storeA, __return, as) && ordered(le, as)
 */
{
  if (l1 == (void *)0)
    return l2;
  else if (l2 == (void *)0)
    return l1;
  else if (cmp(l1->x, l2->x) <= 0) {
    l1->next = merge(l1->next, l2, cmp);
    return l1;
  } else {
    l2->next = merge(l1, l2->next, cmp);
    return l2;
  }
}

struct list *sort(struct list *l, int (*cmp)(void *x, void *y))
/*@ With {A} storeA (le : A -> A -> Prop)
    Require exists as,
            repr(storeA, l, as) &&
            cmp |= int (void *x, void *y)
                   With a b
                   Require emp && storeA(x, a) && storeA(y, b)
                   Ensure __return <= 0 && le(a, b) || __return > 0 && le(b, a)
    Ensure exists as, repr(storeA, __return, as) && ordered(le, as)
 */
{
  if (l == (void *)0 || l->next == (void *)0)
    return l;
  struct list *i, *j;
  i = l;
  j = l->next;
  while (j != (void *)0 &&j != (void *)0) {
    i = i->next;
    j = j->next->next;
  }
  struct list *b;
  b = i->next;
  i->next = (void *)0;
  struct list *l1, *l2;
  l1 = sort(l, cmp);
  l2 = sort(b, cmp);
  return merge(l1, l2, cmp);
}
