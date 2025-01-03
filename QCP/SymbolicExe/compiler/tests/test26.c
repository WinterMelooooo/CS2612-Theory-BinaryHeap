typedef int *ptr;
typedef int arr[10];

int f(arr x) {
  typedef int **ptr, ***pptr;
  { ptr ptr;
    int *p = x;
    ptr = &p;
    /*@ *ptr == p */ }
}

typedef struct { int ptr; } X;

typedef struct { X ptr; } Y, *W, **Z;

int g() {
  Y y;
  y.ptr.ptr = 1;
  //@ y.ptr.ptr == 1
  W w = &y;
  Z z = &w;
  return y.ptr.ptr;
}
