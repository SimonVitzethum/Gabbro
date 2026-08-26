/* **Die SCHALE -- was der Erzeuger nicht schreibt, und genau darum geht es.**
 *
 * `gabbro emit` schreibt fuer jede Sperre ZWEI ZEILEN:
 *
 *     void A_nimm(void);
 *     void A_gib(void);
 *
 * Deklarationen. Keine Definitionen. **Der Rumpf einer Sperre kommt von aussen** -- es gibt
 * keine Gabbro-Laufzeit, und das ist Absicht (`abi.rs`: *„eine Bibliothek, die man nur mit
 * ihrem eigenen Uebersetzer benutzen kann, ist keine Bibliothek"*).
 *
 * Damit ist jede Aussage der Rangordnung eine Aussage ueber die `locks`-Bloecke, die IN
 * DER `.gab` STEHEN. Wer dieselben Symbole sonst noch ruft, steht nicht im Bild.
 */
#include "grenze.c"

#include <pthread.h>
#include <stdatomic.h>
#include <stddef.h>
#include <stdio.h>

/* ---------------------------------------------------------------- Frage 4: die Sperren */

static pthread_mutex_t mA = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t mB = PTHREAD_MUTEX_INITIALIZER;

/* Das Rendezvous fuer den GESTEUERTEN Lauf. Aus: die Faeden laufen frei.
 * An: nach der ersten Nahme wartet jeder Faden auf den anderen -- damit ist die
 * Verschraenkung nicht mehr dem Zufall ueberlassen, sondern erzwungen. */
static atomic_int rz_an = 0;
static atomic_int am_tor = 0;

void schale_rendezvous_an(void);
void schale_rendezvous_an(void) { atomic_store(&rz_an, 1); }

static _Thread_local int schon_rendezvousiert = 0;

/* Von Hand statt `pthread_barrier_t`: die Barriere haengt an `_POSIX_C_SOURCE`, und ein
 * Merkmalsschalter, der die Probe von der Uebersetzungsfahne abhaengig macht, ist genau
 * die Sorte stiller Unterschied, die dieser Ordner sonst „zwei Register" nennt. */
static void vielleicht_rendezvous(void) {
    if (atomic_load(&rz_an) && !schon_rendezvousiert) {
        schon_rendezvousiert = 1;
        atomic_fetch_add(&am_tor, 1);
        while (atomic_load(&am_tor) < 2) { /* warten, bis der andere auch haelt */ }
    }
}

void A_nimm(void) { pthread_mutex_lock(&mA);   vielleicht_rendezvous(); }
void A_gib(void)  { pthread_mutex_unlock(&mA); }
void B_nimm(void) { pthread_mutex_lock(&mB);   vielleicht_rendezvous(); }
void B_gib(void)  { pthread_mutex_unlock(&mB); }

/* ------------------------------------------------------- Frage 1: Groesse und Ausrichtung */

uint64_t schale_masse(int was);
uint64_t schale_masse(int was) {
    switch (was) {
    case 0:  return (uint64_t) sizeof(Fach_slot);
    case 1:  return (uint64_t) _Alignof(Fach_slot);
    case 2:  return (uint64_t) sizeof(Fach);
    case 3:  return (uint64_t) _Alignof(Fach);
    case 4:  return (uint64_t) offsetof(Fach_slot, marke);
    case 5:  return (uint64_t) offsetof(Fach_slot, gueltig);
    case 6:  return (uint64_t) offsetof(Fach_slot, breit);
    case 7:  return (uint64_t) offsetof(Fach_slot, schmal);
    case 8:  return (uint64_t) NFAECHER;
    default: return 0xFFFFFFFFu;
    }
}

/* ------------------------------------------------- Frage 2: der Zeiger, den C sich MERKT */

/* **Die Form, die ein gemischter Kern von selbst erzeugt.** Die C-Seite bekommt einmal
 * einen Zeiger und legt ihn ab; spaeter schreibt sie durch ihn. Die Rust-Seite haelt
 * inzwischen ein `&mut` auf dasselbe Objekt -- und `&mut` traegt in LLVM `noalias`. */
static Fach *gemerkt = NULL;

void schale_merke(Fach *f);
void schale_merke(Fach *f) { gemerkt = f; }

void schale_schreibe_gemerkt(uint32_t i, uint32_t w);
void schale_schreibe_gemerkt(uint32_t i, uint32_t w) { fremd_schreiben(gemerkt, i, w); }

/* ------------------------------------------------- Frage 3: ein C-Rahmen dazwischen */

/* C legt eine Marke auf seinen Stapelrahmen, ruft zurueck, und liest sie danach wieder.
 * Wird der Rahmen ordentlich verlassen, sieht man `nach`; wird er abgerissen, nie. */
int schale_durch_c_rahmen(void (*zurueck)(void));
int schale_durch_c_rahmen(void (*zurueck)(void)) {
    volatile int marke = 0x5A;
    fputs("  [C] Rahmen betreten\n", stdout); fflush(stdout);
    zurueck();
    fputs("  [C] Rahmen verlassen\n", stdout); fflush(stdout);
    return marke;
}
