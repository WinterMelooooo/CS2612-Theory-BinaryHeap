int main()
{
  int i;
  unsigned int a[100];
  unsigned int s;
  unsigned long long n;
  for (i = 0;(unsigned long long)i < n;++i){
    //@ s >= 0
    s += a[i];
  }

  for (i = 0;(unsigned long long)i < n;++i)
    s += a[i];
  //@ s >= 0

  for (i = 0;(unsigned long long)i < n;++i){
    //@ s >= 0
    s += (unsigned int)1;
    //@ s >= 1
    s += (unsigned int)2;
    //@ s >= 2
  }

  for (i = 0;(unsigned long long)i < n;++i){
     //@ s >= 0
     //@ s >= 1
  }
  return (int)s;
}

