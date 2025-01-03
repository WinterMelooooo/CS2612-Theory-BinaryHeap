int test(int a)
/*@ Require emp
    Ensure emp
*/
{ 
   int res;
   switch (a) {
      // initiator should not be executed, but the variable should be declared 
      int y = 10;
      // All Statement except the var declaration before the first case should not be executed
      case 1: 
         res = 1;
         break;
      case 2:
         // should be rejected
         res = y;
         break;
   }
   return res;
}