#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include "140-atomic-array-counter.c"
static _Atomic int streit;
_Noreturn void regel_streit(void) { printf("REGEL_STREIT\n"); fflush(stdout); abort(); }
#define NT 4
#define N 200000
static void *w(void *a) { (void)a; for (int i = 0; i < N; i++) zaehle_regel(0); return 0; }
int main(void) {
    pthread_t t[NT];
    for (int i = 0; i < NT; i++) pthread_create(&t[i], 0, w, 0);
    for (int i = 0; i < NT; i++) pthread_join(t[i], 0);
    printf("%u %d\n", lies_regel(0), NT * N);
    return 0;
}
