typedef struct T {
  int data;
  struct T *next;
} T;

int f() {
  T t;
  t.next = &t;
}
