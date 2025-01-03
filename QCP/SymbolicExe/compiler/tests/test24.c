int f() {
  int n;
  //@ (~ n & n | n << n >> n) == 0
  //@ Inv __time_cost < 100 * (10 - n)
  for (n = 10; n > 0; n--)
    ;
  return 0;
}
