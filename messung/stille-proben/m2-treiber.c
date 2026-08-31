#include <stdio.h>
#include "m2.c"
extern unsigned rufe;
int main(void) {
    printf("arbeite() -- die SPERRE wird genommen:\n");
    arbeite();
    printf("ruft_selbst() -- der Nutzer ruft SEINE Funktion:\n");
    ruft_selbst();
    printf("ein Rumpf, zwei Wege: %u Rufe\n", rufe);
    return 0;
}
