#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>

pthread_t t0, t1;
int x;

int id[]   = { 0, 1 };
int flag[] = { 0, 0 };
int victim = 0;

void lock (int * p) {
  int me = *p;
  int other = !me;
  flag[me] = 1;
  victim = me;
  // __sync_synchronize ();
  while (flag[other] && victim == me)
    ;
}

void unlock (int * p) {
  int me = *p;
  flag[me] = 0;
}

void *
incx (void * p)
{
  lock (p);
  x++;
  unlock (p);
  return 0;
}

int
main (void)
{
  pthread_create (&t0, 0, incx, &id[0]);
  pthread_create (&t1, 0, incx, &id[1]);
  pthread_join (t0, 0);
  pthread_join (t1, 0);
  printf ("%d\n", x);
  return 0;
}
