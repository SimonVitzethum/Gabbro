/* Die EIGENE fremde Funktion des Schreibers -- handgeschriebenes C, genau das,
 * was `extern fn` zusagt. */
#include <stdio.h>
unsigned rufe = 0;
void TOR_nimm(void) { rufe++; printf("  [fremd] TOR_nimm gerufen, jetzt %u mal\n", rufe); }
void TOR_gib(void)  { printf("  [fremd] TOR_gib gerufen\n"); }
