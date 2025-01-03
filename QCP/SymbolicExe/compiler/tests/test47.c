int f() {
  int x;
  /*@ undef_data_at(&x) */
  x = 0;
  /*@ data_at(&x, 0) */
  return 0;
}
