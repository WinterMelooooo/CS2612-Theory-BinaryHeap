int x;

int f()
/*@ With x
  Require x == 0
  Ensure x == 0
*/
{
  {
    int x;
    {
      int x;
      {
        //@ exists x, x == #x && #x == ##x
      }
    }
  }
}
