// frontend now rejects the following case

int test(int a)
/*@ Require emp
    Ensure emp
*/
{ 
   int res;
   switch (a) {
      // declare variable before the first case is allowed
      int y;
      case 1: 
         res = 1;
         break;
      case 2:
         y = 2;
         res = y;
         break;
      default:
         res = 3;
         break;   
   }
   return res;
}