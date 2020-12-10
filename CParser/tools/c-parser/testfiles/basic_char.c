/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int a;
int f1 (int i)
{ id i; 
  lock (i);
  return i;
}

/* int * f (int *i){  
  int x;
  int *j;
  x = *i;
  *j = 0;
  if (x) { 
    x=*j+1;
    *j = 1;
  }
  else {
    x = x +1;
  };
  await (x>0) { x++; a = a+x; x = x + 1;}
  for (x=0; x<10; x++){ 
    x = x + 1;
  }
  return j; 
} 
 int f1 (int i)
{
  return i + 1;
}

int g(char c)
{ int x;
  f1(5);
  return 0;
} */
