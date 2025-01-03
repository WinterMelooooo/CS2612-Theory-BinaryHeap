int f()
/*@ Require emp
    Ensure emp */
{
  int a0;
  int a1;
  int a2;
  int a3;
  int a4;
  int a5;
  int a6;
  int a7;
  int a8;
  int a9;
  int a10;
  int a11;
  int a12;
  int a13;
  int a14;
  int a15;
  int a16;
  int a17;
  int a18;
  int a19;
  a0 += 1;
  a1 += a0;
  a2 += a1;
  a3 += a2;
  a4 += a3;
  a5 += a4;
  a6 += a5;
  a7 += a6;
  a8 += a7;
  a9 += a8;
  a10 += a9;
  a12 += a11;
  a11 += a10;
  a13 += a12;
  a14 += a13;
  a15 += a14;
  a16 += a15;
  a17 += a16;
  a18 += a17;
  a19 += a18;
  //@ a1 == a0 + 1 && a2 == a0 + a1 && a3 == a2
  //@ &a1 == a2
  return a0 + a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 +
         a13 + a14 + a15 + a16 + a17 + a18 + a19;
}
