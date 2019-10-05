/* C-SB+o-mb-o+o-mb-o.litmus
 *
 * Is Parallel Programming Hard, And, If So, What Can You Do About It?
 *
 * Page 270, Listing 15.1: buggy
 * Page 272, Listing 15.2: barrier'd
 *
 * Note: a simple compiler barrier is not enough!
 */
#include <pthread.h>
#include <assert.h>

#define ACCESS(x) (*(volatile typeof(x) *) &(x))
#define READ(x) ({typeof(x) TMP = ACCESS(x); TMP;})
#define WRITE(x,v) ({ACCESS(x) = (v);})

#define BARRIER() ; /* no barrier */
//#define BARRIER() asm volatile ("":::"memory") /* compiler barrier */
//#define BARRIER() asm volatile ("mfence":::"memory") /* full barrier */

static int w0 = 0;
static int w1 = 0;

static int r0 = 0;
static int r1 = 0;

static void * P0 (void * p)
{
  WRITE(w0, 1);
  BARRIER();
  r0 = READ(w1);

  return p;
}

static void * P1 (void * p)
{
  WRITE(w1, 1);
  BARRIER();
  r1 = READ(w0);

  return p;
}

int main ()
{
  pthread_t t[2];
  pthread_create (t + 0, 0, P0, 0);
  pthread_create (t + 1, 0, P1, 0);
  pthread_join (t[0], 0);
  pthread_join (t[1], 0);
  assert(r0 + r1);
  return 0;
}
