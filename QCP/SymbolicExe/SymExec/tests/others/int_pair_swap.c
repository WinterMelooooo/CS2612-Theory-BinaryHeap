//@ Export Coq Goal "int_pair_swap_goal.v"
//@ Export Coq Proof "int_pair_swap_proof.v"

struct int_pair {
  int a;
  int b;
};

void int_pair_swap (struct int_pair * p)
/*@ With    x y
   Require p->a == x && p->b == y
   Ensure  p->a == y && p->b == x
*/
{
  int t;
  t = p -> a;
  p -> a = p -> b;
  p -> b = t;
}