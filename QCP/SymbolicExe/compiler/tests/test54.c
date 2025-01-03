void g(long long);

long long f() {
  unsigned int x;
  // assignment
  x = 0;
  // binary arith
  x = x + 1;
  // function call
  g(2);
  // condition
  unsigned long long y = 3;
  4 ? 4294967295 : y;
  // return value
  return 5;
}
