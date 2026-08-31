/* Der EIGENE fremde Leser des Schreibers -- eine ANDERE Lesart desselben Wortes.
 * Er schrieb `extern fn Eintrag_a(...)` und lieferte dies in einer statischen
 * Bibliothek aus. */
#include <stdint.h>
typedef struct { uint8_t *bytes; uint32_t len; } Eintrag;
uint32_t Eintrag_a(const Eintrag *v) { (void)v; return 999u; }
