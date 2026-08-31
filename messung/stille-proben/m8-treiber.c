#include <stdio.h>
#include "m8.c"
int main(void) {
    uint8_t w[4] = { 0x2A, 0x00, 0x00, 0x00 };   /* Bits 15:0 == 42 */
    Eintrag e = { w, 4 };
    printf("frag() = %u   (fremd sagt 999, der erzeugte Leser sagt 42)\n", frag(&e));
    return 0;
}
