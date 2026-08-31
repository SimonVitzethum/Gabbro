#include <stdio.h>
#include "m1.c"

/* Das Freigabe-Primitiv bleibt fremd -- genau das, was der Erzeuger zusagt. */
void TOR_gib(void) { }

int main(void) {
    printf("spur vor  = %u\n", spur);
    arbeite();
    printf("spur nach = %u\n", spur);
    printf("nutz      = %u\n", nutz);
    return 0;
}
