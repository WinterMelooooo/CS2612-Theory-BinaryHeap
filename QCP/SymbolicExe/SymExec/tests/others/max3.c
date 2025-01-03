//@ Export Coq Goal "max3_goal.v"
//@ Export Coq Proof "max3_proof.v"

//@ Extern Coq (_max3 : Z -> Z -> Z -> Z)

int max3(int x, int y, int z)
/*@ Require emp
   Ensure  __return == _max3(x, y, z) && emp
*/
{
  if (x < y) {
    if (y < z) {
      return z;
    }
    else {
      return y;
    }
  }
  else {
    if (x < z) {
      return z;
    }
    else {
      return x;
    }
  }
}