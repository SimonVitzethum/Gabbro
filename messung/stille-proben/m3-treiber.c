#include <stdio.h>
#include "m3.c"
int main(void) {
    stand = 0;   /* Der ERZEUGTE Probenrumpf sagt `stand != 7` -- also `true`.
                  * Der eigene fremde Rumpf des Schreibers sagt immer `false`. */
    printf("frage() = %s   (fremd sagt false, die Probe sagt true)\n",
           frage() ? "true" : "false");
    return 0;
}
