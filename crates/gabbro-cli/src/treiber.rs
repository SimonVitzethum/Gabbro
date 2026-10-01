//! Per-unit hosted driver generator: `gabbro build` writes one driver C file
//! per concurrent unit (lane 246).
//!
//! The emitter translates each `concurrent` member to a plain function and
//! emits no caller and no `main`; this generator writes the missing half: one
//! thread per declared start, join all, and the lock primitives the emitter
//! only declares. The generated file is a build artefact, pinned per unit: the
//! probe compares the `concurrent { ... }` occurrences of the sources against
//! the `gabbro_faden_start` sites of the driver, BY COUNT (a multiset since
//! fix lane F4): a root added, dropped or started a different number of times
//! without regenerating fails loudly.
//!
//! **Since TODO section 0e K8 the driver names no operating-system function.**
//! Threads, locks and the words of a failure go through `laufzeit/bindung.h`,
//! which the PROGRAM defines -- see [`erzeuge`] for what left the template with
//! them. The bare-metal twin [`erzeuge_metall`] never named one: underneath it
//! there is no operating system, and the machine is allowed.

use std::collections::BTreeMap;

/// One declared start, resolved to the C name the emitter writes.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Wurzel {
    /// Short name: the C function (`hauptA`), i.e. the last path segment.
    pub c_name: String,
    /// Full Gabbro path as declared (`hauptA` or `modul::hauptA`).
    pub gab_path: String,
}

/// One lock the driver must define (the emitter only declares it).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Sperre {
    /// Short lock name (`L`); the primitives are `<name>_nimm` / `<name>_gib`.
    pub name: String,
    /// A shared (`geteilt`) lock additionally needs `_nimm_geteilt` / `_gib_geteilt`.
    pub geteilt: bool,
    /// `masks irqs` (Opus agent J): the bare-metal driver takes it with IF = 0
    /// (`METALL_SPERRE_MASKIERT`), so no thrown entry can land on a core with a
    /// claim on it. The hosted driver has no interrupts and ignores the word.
    pub maskiert: bool,
}

/// One `entry` of the unit, as the BARE-METAL driver installs it (Opus agent J,
/// OFFEN O32 residue). The emitter declares `gabbro_eintritt_<name>` and says
/// "the emitter names the primitive and does not define it"; the metal driver
/// defines it (`METALL_EINTRITT`, `laufzeit/metall/metall.h`) and installs it
/// in the IDT at `gabbro_eintritt_<name>_VEKTOR`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Eintritt {
    /// The entry name (`zeitgeber`).
    pub name: String,
    /// The constant vector. An entry without one cannot be installed and is
    /// refused by the build before generation.
    pub vektor: u128,
    /// A LAPIC-delivered interrupt (`via idt` at a vector >= 32): the stub
    /// writes the EOI. An entered entry (no `via`), an NMI or a CPU exception
    /// (vector < 32) is acknowledged by `iretq` alone.
    pub geworfen: bool,
    /// How the stub runs the dispatch.
    pub ruf: EintrittRuf,
}

/// The call the stub makes, decided by the build from the declaration.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum EintrittRuf {
    /// `regs in` feed the dispatch's parameters in order; `regs out` (zero or
    /// one register) receives its result.
    Bindung { ein: Vec<String>, aus: Option<String> },
    /// The dispatch target is not declared in this unit: the stub ends the
    /// machine loudly if entered (`metall_eintritt_ohne_ziel`).
    OhneZiel,
    /// The declared registers do not match the dispatch's signature: no stub
    /// can bind them honestly, and it ends the machine loudly if entered
    /// (`metall_eintritt_bindung_falsch`). OFFEN O32.
    BindungFalsch,
}

/// **The exceptions that push a CPU error code** (8, 10..14, 17, 21, 29, 30): their
/// entries take the twin stub `METALL_EINTRITT_FC` and `metall_idt_setze_fc`
/// (`laufzeit/metall/metall.h`, OFFEN O32 (9)).
pub fn hat_fehlercode(v: u128) -> bool {
    matches!(v, 8 | 10..=14 | 17 | 21 | 29 | 30)
}

/// What the bare-metal driver carries beyond roots and locks (Opus agent J).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MetallZusatz {
    /// The unit's entries, installed in the metal IDT.
    pub eintritte: Vec<Eintritt>,
    /// `rcu R` domains: the read side `R_lese_start`/`R_lese_ende`.
    pub rcus: Vec<String>,
    /// `accumulates A ... per cpu N`: the cell arrays `A_zellen`. The image
    /// brings up at most as many cores as the SMALLEST of them holds, so
    /// `gabbro_kern()` stays below every `N` (certificate section E).
    pub zellen: Vec<String>,
}

/// **The generator's version, carried in the unit fingerprint.** The driver
/// is rendered deterministically out of the sources, so a template change
/// with unchanged sources would otherwise leave a stale driver behind a
/// valid record. Bump this on every template change; `bau.rs` mixes it into
/// the fingerprint of every unit that owns a driver.
pub const GENERATOR_KENNUNG: &str = "treiber-gen-10";

/// **The unit's dynamic arenas, reserved before the first root runs** (server lane,
/// 2026-09-28, TODO section 0e K8).
///
/// THE DEFECT THIS CLOSES, found by K8's probe and not by a reader. The emitted C ends with
/// `#define GABBRO_ARENEN &A_desc, &B_desc` and says in its own comment that it is *"the ONE
/// list a driver needs to reserve (`gabbro_arena_reserve`) before any of the unit's code
/// runs"*. **Neither generated driver read it.** Only `laufzeit/kmodul/kmodul.c` did, and the
/// harness drivers -- `instrumente/pruefe-metall.sh`, `miss-arena-decke.sh`,
/// `pruefe-emission.sh` -- each wrote the call by hand. So a hosted or bare-metal unit with a
/// dynamic arena, built by `gabbro build` and run from its own driver, started with `base ==
/// NULL`: every `grow` and every `alloc` took its `else`, the heap was DEAD, and nothing said
/// so. *Fail-closed and therefore silent -- which is why three hand-written registers over one
/// call could all be right while the generated one was missing* (`W7`).
///
/// The block is `#ifdef`-guarded because the emitter defines `GABBRO_ARENEN` exactly when it
/// emitted descriptors, which is the same reading `kmodul.c` already stood on: the unit's own
/// list decides whether the unit has arenas at all, and no `-D` on a command line can drift
/// from it.
///
/// No error check, and that differs from the module flavour on purpose: the hosted
/// (`laufzeit/arena_dyn.c`) and bare-metal (`laufzeit/metall/arena.c`) reservations FAIL-STOP
/// inside themselves -- there is no program running yet that could take an `else`. A kernel
/// module cannot stop the machine, so `kmodul.c` reads the outcome and refuses the load.
fn arenen_reservieren(aus: &mut String) {
    aus.push_str(
        "\n    /* -- The unit's dynamic arenas, reserved before the first root runs.\n     *\n\
         \x20    * The list is the emitted unit's own (`GABBRO_ARENEN`, written by the\n\
         \x20    * emitter, which is the only place that knows which descriptors it\n\
         \x20    * emitted), so it cannot drift from the program. A unit without an\n\
         \x20    * arena has no such define and this block disappears. The reservation\n\
         \x20    * fail-stops on refusal inside the runtime: at load there is no\n\
         \x20    * program running that could take an `else`. */\n\
         #ifdef GABBRO_ARENEN\n\
         \x20   {\n\
         \x20       gabbro_arena_desc *const arenen[] = { GABBRO_ARENEN };\n\
         \x20       unsigned a;\n\
         \x20       for (a = 0; a < (unsigned)(sizeof arenen / sizeof arenen[0]); a++) {\n\
         \x20           gabbro_arena_reserve(arenen[a]);\n\
         \x20       }\n\
         \x20   }\n\
         #endif\n",
    );
}

/// **The hosted runtime of a dynamic arena, written by the generator** (C-free lane,
/// 2026-09-30; the template `arena.dyn`).
///
/// Until this text, `laufzeit/arena_dyn.c` was handwritten C that reserved the address range
/// of every arena's ceiling at load and made the committed prefix writable at every `grow`,
/// handing the binding its addresses as NUMBERS. Now the generator writes it, and the binding
/// answers and takes REGIONS: `gabbro_os_reserve` is a Gabbro function over a region gate
/// (`tor.region`) that never answers 0 -- a refused reservation ends the process inside it,
/// since at load no program runs that could take an `else` -- and `gabbro_os_commit` takes the
/// region's page and its length under `requires bytes <= lenof(stelle)`.
///
/// **Every line of arithmetic here is the template's, and it is proved**
/// (`grammatik/Grammatik/SchablonenArena.lean`): the span covers every slot and is whole pages
/// with no 64-bit wrap (`arena_spanne_passt`, for a page of at most `2^32` -- any other page
/// answer fail-stops below), and the range a `grow` commits covers the new slots, lies on
/// pages and inside the span (`arena_commit_bereich`), so the binding's `requires` holds at
/// the one call the template makes. The descriptor is the emitted unit's
/// (`ARENA_DYN_PRELUDE` in `emit.rs`), which is why this text stands AFTER the unit's
/// `#include`. No operating system is named: the three names it calls are the program's.
pub const ARENA_LAUFZEIT: &str = "\
/* -- The runtime of the unit's dynamic arenas (template `arena.dyn`, proved in\n\
 *    grammatik/Grammatik/SchablonenArena.lean). Generated; the binding is the program's. */\n\
#ifndef GABBRO_OS_M_DESKRIPTOR\n\
#define GABBRO_OS_M_DESKRIPTOR 1u\n\
#define GABBRO_OS_M_BODEN      4u\n\
#define GABBRO_OS_M_UEBER_MAX  5u\n\
#define GABBRO_OS_M_SEITE      6u\n\
#define GABBRO_OS_ENDE_ABBRUCH 134u\n\
#endif\n\
#define GABBRO_ARENA_EXIT_RESERVE 3u\n\
void gabbro_os_melden(uint32_t code, uint64_t a, uint64_t b);\n\
void gabbro_os_ende(uint32_t code);\n\
uint8_t *gabbro_os_reserve(uint64_t bytes);\n\
uint32_t gabbro_os_commit(uint8_t *stelle, uint64_t bytes);\n\
uint64_t gabbro_os_seitengroesse(void);\n\
\n\
static uint64_t gabbro_arena_seite(void)\n\
{\n\
    uint64_t s = gabbro_os_seitengroesse();\n\
    if (s == 0u || s > 4294967296u) {\n\
        gabbro_os_melden(GABBRO_OS_M_SEITE, s, 0u);\n\
        gabbro_os_ende(GABBRO_OS_ENDE_ABBRUCH);\n\
    }\n\
    return s;\n\
}\n\
\n\
void gabbro_arena_reserve(gabbro_arena_desc *d)\n\
{\n\
    uint64_t seite, spanne;\n\
    if (d == 0 || d->base != 0 || d->max == 0u || d->elem == 0u || d->floor_hi > d->max) {\n\
        gabbro_os_melden(GABBRO_OS_M_DESKRIPTOR, d ? d->max : 0u, d ? d->floor_hi : 0u);\n\
        gabbro_os_ende(GABBRO_ARENA_EXIT_RESERVE);\n\
        return;\n\
    }\n\
    seite = gabbro_arena_seite();\n\
    /* `arena_spanne_passt`: every slot, whole pages, no wrap. */\n\
    spanne = ((uint64_t)d->max * (uint64_t)d->elem + seite - 1u) / seite * seite;\n\
    d->base = gabbro_os_reserve(spanne);\n\
    d->used = 0u;\n\
    d->committed = 0u;\n\
    if (d->floor_hi > 0u && !gabbro_arena_grow(d, d->floor_hi)) {\n\
        gabbro_os_melden(GABBRO_OS_M_BODEN, d->floor_hi, 0u);\n\
        gabbro_os_ende(GABBRO_ARENA_EXIT_RESERVE);\n\
        return;\n\
    }\n\
}\n\
\n\
bool gabbro_arena_grow(gabbro_arena_desc *d, uint32_t n)\n\
{\n\
    uint64_t neu, seite, start, ende;\n\
    if (d == 0 || d->base == 0) {\n\
        return false;\n\
    }\n\
    if (n == 0u) {\n\
        return true;\n\
    }\n\
    neu = (uint64_t)d->committed + (uint64_t)n;\n\
    if (neu > d->max) {\n\
        /* Past the ceiling there is no commit, only the stop (`N426` holds it statically). */\n\
        gabbro_os_melden(GABBRO_OS_M_UEBER_MAX, neu, d->max);\n\
        gabbro_os_ende(GABBRO_OS_ENDE_ABBRUCH);\n\
        return false;\n\
    }\n\
    seite = gabbro_arena_seite();\n\
    /* `arena_commit_bereich`: whole pages, covering the new slots, inside the span. */\n\
    start = (uint64_t)d->committed * (uint64_t)d->elem / seite * seite;\n\
    ende = (neu * (uint64_t)d->elem + seite - 1u) / seite * seite;\n\
    if (gabbro_os_commit((uint8_t *)d->base + start, ende - start) != 0u) {\n\
        /* The platform refused below the ceiling: `committed` unchanged, `else` runs. */\n\
        return false;\n\
    }\n\
    d->committed = (uint32_t)neu;\n\
    return true;\n\
}\n";

/// **The program's binding as the generated driver calls it** (C-free lane, 2026-09-30): the
/// report codes and the prototypes that were `laufzeit/bindung.h`, which is gone -- every name
/// here is a GABBRO function of the binding (`bibliothek/linux/linux.gab`), and the C compiler
/// holds each prototype against the emitted definition in the same translation unit.
pub const BINDUNG_KOPF: &str = "\
#include <stdint.h>\n\
#include <stdbool.h>\n\
#define GABBRO_OS_M_DESKRIPTOR 1u\n\
#define GABBRO_OS_M_SPANNE     2u\n\
#define GABBRO_OS_M_RESERVE    3u\n\
#define GABBRO_OS_M_BODEN      4u\n\
#define GABBRO_OS_M_UEBER_MAX  5u\n\
#define GABBRO_OS_M_SEITE      6u\n\
#define GABBRO_OS_M_START      7u\n\
#define GABBRO_OS_M_WARTE      8u\n\
#define GABBRO_OS_ENDE_ABBRUCH 134u\n\
void gabbro_os_melden(uint32_t code, uint64_t a, uint64_t b);\n\
void gabbro_os_ende(uint32_t code);\n\
uint8_t *gabbro_os_reserve(uint64_t bytes);\n\
uint32_t gabbro_os_commit(uint8_t *stelle, uint64_t bytes);\n\
uint64_t gabbro_os_seitengroesse(void);\n\
void gabbro_os_nachgeben(void);\n";

/// **The hosted thread runtime, written by the generator** (C-free lane, 2026-09-30; template
/// `faden.laufzeit`).
///
/// `laufzeit/faden.c` and the binding's pthread and raw-`clone` C are gone. A thread is started
/// through the TRAMPOLINE the emitter writes for the program's stack gate
/// (`gabbro_os_klon_tor`, template `tor.trampolin`): the `clone` in the parent, and in the
/// child the root on the handed stack, then the program's `-> never` thread end. The root and
/// the end are C function DESIGNATORS at every call site of `gabbro_faden_start` (the driver
/// and the emitted `start` statement name them), so no code address is ever read from data.
/// The join word is written by the kernel at both ends (the gate's contract); the wait loop
/// trusts the word and nothing else (`faden_warte_korrekt`, `SchablonenArena.lean` §3). The
/// interface (`gabbro_faden_start`/`_warte`) is the one the bare-metal runtime implements too.
pub const FADEN_LAUFZEIT: &str = "\
/* -- The thread runtime (template `faden.laufzeit`). Generated; every OS call is the\n\
 *    program's (the stack gate's trampoline, the thread end, the word wait). */\n\
uint64_t gabbro_os_klon_flaggen(void);\n\
int64_t gabbro_os_klon_tor_trampolin(uint64_t flaggen, uint64_t spitze, uint8_t *eltern, uint8_t *kind, void (*_kind)(void), void (*_ende)(void));\n\
_Noreturn void gabbro_os_faden_ende(void);\n\
void gabbro_os_warte_wort(uint8_t *wort, uint32_t erwartet);\n\
int gabbro_faden_start(void (*fn)(void), void *spitze, uint32_t *wort);\n\
void gabbro_faden_warte(uint32_t *wort);\n\
int gabbro_faden_start(void (*fn)(void), void *spitze, uint32_t *wort)\n\
{\n\
    int64_t r;\n\
    if (fn == 0 || spitze == 0 || wort == 0 || ((uintptr_t)spitze & 15u) != 0u) {\n\
        return 22;\n\
    }\n\
    r = gabbro_os_klon_tor_trampolin(gabbro_os_klon_flaggen(), (uint64_t)(uintptr_t)spitze,\n\
                                     (uint8_t *)wort, (uint8_t *)wort, fn, gabbro_os_faden_ende);\n\
    if (r < 0) {\n\
        return r < -4095 ? 12 : (int)-r;\n\
    }\n\
    return 0;\n\
}\n\
void gabbro_faden_warte(uint32_t *wort)\n\
{\n\
    for (;;) {\n\
        uint32_t v = __atomic_load_n(wort, __ATOMIC_ACQUIRE);\n\
        if (v == 0u) {\n\
            return;\n\
        }\n\
        gabbro_os_warte_wort((uint8_t *)wort, v);\n\
    }\n\
}\n\n";

/// **The hosted lock, written by the generator** (C-free lane, 2026-09-30; template
/// `sperre.ticket`).
///
/// Until this text a hosted lock was a `pthread_mutex_t` in a blob of words, initialised in
/// `main` and taken through the binding's C. Now it is the ticket lock `CTicket.lean` proves --
/// the four instructions of its model, word for word (the relaxed `fetch_add` that draws a
/// ticket, the acquire spin, the release store) -- which the bare-metal image
/// has run since Opus agent I (`laufzeit/metall/metall.h`). Mutual exclusion is
/// `ticket_ausschluss`; every step refines `sperrAbstrakt` (`ticketLP_sperrAbstrakt`). The one
/// thing added to the spin is a hand-over: every 64 passes the waiter calls the program's
/// `gabbro_os_nachgeben` (a Gabbro function over the kernel's yield gate), because with more
/// threads than cores the ticket served next may belong to a thread that is not running. A
/// yield changes no word of the lock and no program memory -- a stutter of `dreht`
/// (`schrittT_proj`: a spin is a stutter). A zero-initialised `static` is a free lock, so there
/// is no initialiser and nothing to call before the first root. No operating system and no
/// instruction set is named here.
pub const SPERRE_TICKET: &str = "\
/* -- Lock primitives: the ticket lock of CTicket.lean (template `sperre.ticket`). The emitter\n\
 *    declares `L_nimm`/`L_gib`; this file defines them; the only call out is the program's\n\
 *    yield (`gabbro_os_nachgeben`). A zero `static` is a free lock. */\n\
#include <stdatomic.h>\n\
typedef struct {\n\
    _Atomic uint32_t naechste;\n\
    _Atomic uint32_t jetzt;\n\
} gabbro_ticket;\n\
void gabbro_os_nachgeben(void);\n\
static void gabbro_ticket_nimm(gabbro_ticket *t)\n\
{\n\
    uint32_t my = atomic_fetch_add_explicit(&t->naechste, 1u, memory_order_relaxed);\n\
    uint32_t n = 0u;\n\
    while (atomic_load_explicit(&t->jetzt, memory_order_acquire) != my) {\n\
        if (++n == 64u) {\n\
            n = 0u;\n\
            gabbro_os_nachgeben();\n\
        }\n\
    }\n\
}\n\
static void gabbro_ticket_gib(gabbro_ticket *t)\n\
{\n\
    uint32_t n = atomic_load_explicit(&t->jetzt, memory_order_relaxed);\n\
    atomic_store_explicit(&t->jetzt, (uint32_t)(n + 1u), memory_order_release);\n\
}\n\n";

/// True for `[A-Za-z_][A-Za-z0-9_]*` (ASCII only: a Gabbro name that reaches
/// C is ASCII; anything else cannot name a C function and is refused before
/// generation, never truncated into one).
pub fn gueltiger_c_name(s: &str) -> bool {
    let mut zeichen = s.chars();
    let Some(erstes) = zeichen.next() else {
        return false;
    };
    if !(erstes.is_ascii_alphabetic() || erstes == '_') {
        return false;
    }
    zeichen.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Render the hosted driver for one unit.
///
/// **EVERY OPERATING-SYSTEM CALL IN THE ARTEFACT IS THE PROGRAM'S** (server lane,
/// 2026-09-28, TODO section 0e K8, second slice). Until this template changed, the driver
/// was the last place in the hosted runtime that named the operating system by itself:
/// `pthread_create`, `pthread_join`, `pthread_mutex_lock`, `pthread_mutex_unlock`, `pause`,
/// `fprintf` and `abort` -- seven names, measured over a built binary
/// (`instrumente/pruefe-os-bindung.sh`, `MARKE_OSSYM`), and every one of them written here.
/// They are calls through `laufzeit/bindung.h` now, which declares them and defines none;
/// `bibliothek/linux/linux.{gab,c}` is the binding a program takes off the shelf, and
/// `bau.rs::bindungsregel_gehostet` refuses a unit that binds none of them.
///
/// **A generated file is the runtime, not user code**, which is why the seven were the
/// runtime's to give up: nobody types this file, a stale one is refused by [`pin_pruefe`],
/// and the measurement counts its object among the runtime's.
///
/// Three things left the template with them, and each one is a simplification the binding
/// paid for rather than a loss:
///
/// * **the adapters.** `pthread_create` wants `void *(*)(void *)` and an emitted root is
///   `void (*)(void)`, so every root used to get a `faden_<root>` wrapper. The POSIX
///   signature is in `bibliothek/linux/linux.c` now, so the root's own name stands at the
///   call site -- exactly the shape the BARE-METAL driver already had
///   (`gabbro_faden_start({root}, …)`), and one shape for both drivers is one pin to read;
/// * **the idle root.** `ruhe()` spun on `pause()`, was `__attribute__((unused))` and was
///   never spawned on hosted -- the template said so itself. Keeping it would have demanded
///   a binding row of every concurrent unit for a call nothing makes; bare metal parks its
///   spare cores inside its own runtime and never read this function
///   (`erzeuge_metall_voll` emits none);
/// * **the words.** The error paths printed and aborted. Printing is an OS call, so the
///   runtime has no words of its own: a failure travels as a code and two numbers
///   (`GABBRO_OS_M_START`, `GABBRO_OS_M_WARTE`) and the program's binding says the
///   sentence. A lock that cannot be taken fail-stops inside the binding, because the
///   driver has no `else` to take at a lock it must hold.
///
/// `wurzeln` are the resolved roots in declaration order, ONE ENTRY PER
/// OCCURRENCE (fix lane F4: `concurrent { f, f }` is two starts, and the
/// accepted pool-safe duplicate must get two threads); the generator writes
/// one `gabbro_faden_start` per entry.
/// `sperren` the locks to define. `nachlauf` is optional
/// unit-specific observation C after the join loop (the 124 invariant
/// checks); the plain build passes `None`, so the artefact carries the
/// runtime half only and a test harness supplies the check half. The file
/// always ends in `return 0;`, which is unreachable but valid C when
/// `nachlauf` returns itself.
///
/// The output is deterministic: same inputs, same bytes (no hashes, no
/// timestamps), so a stale driver is detectable by comparison, not by age.
pub fn erzeuge(
    einheit: &str,
    wurzeln: &[Wurzel],
    sperren: &[Sperre],
    nachlauf: Option<&str>,
) -> String {
    let mut aus = String::new();
    aus.push_str(&format!(
        "/* {einheit}.treiber.c -- GENERATED by `gabbro build` (lane 246). Do not edit.\n"
    ));
    aus.push_str(
        " *\n \
         * WHAT THIS IS. The hosted runtime driver for one concurrent unit: the\n \
         * emitter translated each `concurrent` member to a plain function and\n \
         * emitted no caller and no `main`; this file starts exactly the declared\n \
         * roots, one thread per occurrence, and joins them. Regenerate after every\n \
         * change to the unit's `concurrent` sets or locks: the pin probe compares\n \
         * the source sets against the `gabbro_faden_start` sites below and fails\n \
         * a stale file.\n \
         *\n \
         * EVERY OPERATING-SYSTEM CALL IN HERE IS THE PROGRAM'S (TODO section 0e K8).\n \
         * This file names no POSIX function and no system call: threads, locks and\n \
         * the words of a failure go through the names of the binding head below,\n \
         * which the program defines in Gabbro -- `bibliothek/linux/linux.gab` is the\n \
         * binding it may take off the shelf. A unit that binds none is refused\n \
         * before this file is written.\n \
         *\n \
         * BUILD (from the tree root; `<ausgabe>` is the manifest's `out` dir):\n \
         *\n \
         *   cc -std=c11 -O0 -Wall -Wextra -Werror -I laufzeit -I <ausgabe> \\\n \
         *      -DEINHEIT_INCLUDE='\"<einheit>.c\"' -c \\\n \
         *      -o <ausgabe>/<einheit>.treiber.o <ausgabe>/<einheit>.treiber.c\n \
         *\n \
         * and link it against the program's own C bodies, if it has any. The binding\n \
         * (`bibliothek/linux/linux.gab`) is Gabbro and part of the unit; the arena,\n \
         * lock and thread runtimes are written into this file (templates `arena.dyn`,\n \
         * `sperre.ticket`, `faden.laufzeit`).\n \
         */\n",
    );
    aus.push_str("\n/* -- The names this driver calls and does not define ------------------- */\n\n");
    aus.push_str(BINDUNG_KOPF);
    aus.push_str("\n/* -- The emitted unit -------------------------------------------------- */\n\n");
    aus.push_str("#include EINHEIT_INCLUDE\n");
    // The arena runtime is the generator's since the C-free lane's second slice (template
    // `arena.dyn`); a unit without a dynamic arena defines no `GABBRO_ARENEN` and gets none.
    aus.push_str("\n#ifdef GABBRO_ARENEN\n");
    aus.push_str(ARENA_LAUFZEIT);
    aus.push_str("#endif\n");
    let mut sortiert: Vec<&Sperre> = sperren.iter().collect();
    sortiert.sort_by(|a, b| a.name.cmp(&b.name));
    if !sortiert.is_empty() {
        aus.push_str(SPERRE_TICKET);
    }
    for s in &sortiert {
        let n = &s.name;
        aus.push_str(&format!(
            "static gabbro_ticket sperre_{n};\n\n\
             void {n}_nimm(void)\n{{\n    gabbro_ticket_nimm(&sperre_{n});\n}}\n\n\
             void {n}_gib(void)\n{{\n    gabbro_ticket_gib(&sperre_{n});\n}}\n\n"
        ));
        if s.geteilt {
            // **The shared pair is the same object taken the same way**, which is what
            // the emitter asks for today: `L_nimm_geteilt` is a second NAME and not a
            // second primitive.
            aus.push_str(&format!(
                "void {n}_nimm_geteilt(void)\n{{\n    gabbro_ticket_nimm(&sperre_{n});\n}}\n\n\
                 void {n}_gib_geteilt(void)\n{{\n    gabbro_ticket_gib(&sperre_{n});\n}}\n\n"
            ));
        }
    }
    aus.push_str(FADEN_LAUFZEIT);
    aus.push_str("/* -- ROOTS: the declared starts of this unit.\n");
    aus.push_str(" *\n * ONE STACK AND ONE JOIN WORD PER OCCURRENCE, and the ROOT'S OWN NAME at the\n");
    aus.push_str(" * call site -- the shape of the bare-metal driver, so one scanner reads both.\n");
    aus.push_str(" * Each stack is a region of the program's binding with its lowest page left\n");
    aus.push_str(" * unwritable (a guard: an overflow faults instead of writing a neighbour).\n */\n");
    aus.push_str("/* N_WURZELN counts the declared starts, one per occurrence -- the probe checks it\n * against the number of members the source's `concurrent` sets name. */\n");
    aus.push_str(&format!("#define N_WURZELN {}\n", wurzeln.len()));
    aus.push_str("#define GABBRO_STAPEL 8388608u\n");
    aus.push_str("static uint32_t wort[N_WURZELN > 0 ? N_WURZELN : 1];\n");
    aus.push_str("\n/* -- main: start exactly the roots, join them. ---------------------------- */\n\nint main(void)\n{\n");
    if !wurzeln.is_empty() {
        aus.push_str("    uint64_t seite = gabbro_os_seitengroesse();\n    uint8_t *st;\n    int rc;\n");
    }
    arenen_reservieren(&mut aus);
    aus.push('\n');
    // **A failed start joins what already runs** (fix lane F4, the finding review
    // G06 F6 made at `laufzeit/start_pool.c`, which this template shared): the
    // threads started before the failing one are joined before `main` returns,
    // so "join covers exactly the spawned set" holds on the error path too.
    for (i, w) in wurzeln.iter().enumerate() {
        let c = &w.c_name;
        let einsammeln: String = (0..i)
            .map(|j| format!("        gabbro_faden_warte(&wort[{j}]);\n"))
            .collect();
        aus.push_str(&format!(
            "    st = gabbro_os_reserve(seite + GABBRO_STAPEL);\n\
             \x20   rc = (int)gabbro_os_commit(st + seite, GABBRO_STAPEL);\n\
             \x20   if (rc == 0) {{\n\
             \x20       rc = gabbro_faden_start({c}, st + seite + GABBRO_STAPEL, &wort[{i}]);\n\
             \x20   }}\n\
             \x20   if (rc != 0) {{\n\
             \x20       gabbro_os_melden(GABBRO_OS_M_START, {i}, (uint64_t)rc);\n{einsammeln}\
             \x20       return 2;\n    }}\n"
        ));
    }
    for i in 0..wurzeln.len() {
        aus.push_str(&format!("    gabbro_faden_warte(&wort[{i}]);\n"));
    }
    if let Some(code) = nachlauf {
        aus.push_str("\n    /* -- Unit-specific observation (test half, not runtime). -- */\n");
        aus.push_str(code);
        if !code.ends_with('\n') {
            aus.push('\n');
        }
    }
    // **The marker stands in every driver, with or without observation.** A
    // test that appends a unit's checks does it HERE, so the build artefact
    // and the test artefact differ by exactly the appended block -- the
    // spawn, join and mutex bytes are identical, verifiable by diff.
    aus.push_str("    /* NACHLAUF: unit-specific observation goes here in test runs. */\n");
    aus.push_str("    return 0;\n}\n");
    aus
}

/// Render the BARE-METAL driver for one unit (Opus agent I, 2026-09-26):
/// `<unit>.metall.c`, the freestanding twin of the hosted driver.
///
/// Same roots, same occurrence count, same locks -- linked against
/// `laufzeit/metall/` (`start.S`, `kern.c`) instead of pthreads: every
/// declared start becomes one `gabbro_faden_start` on a driver-owned 64 KiB
/// stack (the runtime places them round robin over the cores, from core 1),
/// the driver thread joins them all, and every lock is the ticket lock
/// (`METALL_SPERRE`, `CTicket.lean`). The emitted unit is `#include`d
/// unchanged. `nachlauf` and the `NACHLAUF` marker work exactly as in
/// [`erzeuge`]: the build artefact carries the runtime half only.
///
/// Deterministic like [`erzeuge`]: same inputs, same bytes.
pub fn erzeuge_metall(
    einheit: &str,
    wurzeln: &[Wurzel],
    sperren: &[Sperre],
    nachlauf: Option<&str>,
) -> String {
    erzeuge_metall_voll(einheit, wurzeln, sperren, &MetallZusatz::default(), nachlauf)
}

/// [`erzeuge_metall`] with the unit's entries, rcu domains and per-cpu cells
/// (Opus agent J): `masks irqs` locks as `METALL_SPERRE_MASKIERT`, every
/// `entry` as a stub installed in the IDT before the roots start, every `rcu`
/// as `METALL_RCU`, and the core limit `METALL_KERNE_GRENZE` over the cell
/// arrays. Deterministic like the rest.
pub fn erzeuge_metall_voll(
    einheit: &str,
    wurzeln: &[Wurzel],
    sperren: &[Sperre],
    zusatz: &MetallZusatz,
    nachlauf: Option<&str>,
) -> String {
    let mut aus = String::new();
    aus.push_str(&format!(
        "/* {einheit}.metall.c -- GENERATED by `gabbro build` (Opus agent I). Do not edit.\n"
    ));
    aus.push_str(
        " *\n \
         * WHAT THIS IS. The BARE-METAL runtime driver for one concurrent unit: the\n \
         * twin of `<unit>.treiber.c` without an OS. It starts exactly the declared\n \
         * roots, one thread per occurrence, through the thread interface of\n \
         * `laufzeit/faden.h` as `laufzeit/metall/kern.c` implements it (no libc, no\n \
         * Linux), joins them, and defines every lock as the ticket lock of\n \
         * `CTicket.lean`. Cores without a thread run the idle root inside the\n \
         * runtime's scheduler loop. The pin probe compares the source's\n \
         * `concurrent` sets against the `gabbro_faden_start` sites below.\n \
         *\n \
         * BUILD: `instrumente/pruefe-metall.sh` is the recipe (flags, link script,\n \
         * QEMU line); in short, with `<ausgabe>` the manifest's `out` dir:\n \
         *\n \
         *   cc -std=c11 -O2 -ffreestanding -fno-builtin -nostdlib -fno-pie -mno-red-zone \\\n \
         *      -I laufzeit/metall -I <ausgabe> -DEINHEIT_INCLUDE='\"<einheit>.c\"' \\\n \
         *      -c <ausgabe>/<einheit>.metall.c\n \
         *   ld -T laufzeit/metall/metall.ld start.o kern.o <einheit>.metall.o\n \
         */\n",
    );
    aus.push_str("\n#include \"metall.h\"\n");
    aus.push_str("\n/* -- The emitted unit -------------------------------------------------- */\n\n");
    aus.push_str("#include EINHEIT_INCLUDE\n");
    aus.push_str("\n/* -- Lock primitives: the ticket lock (CTicket.lean, SATZKARTE section 32). */\n");
    let mut sortiert: Vec<&Sperre> = sperren.iter().collect();
    sortiert.sort_by(|a, b| a.name.cmp(&b.name));
    for s in sortiert {
        let makro = match (s.maskiert, s.geteilt) {
            (true, true) => "METALL_SPERRE_MASKIERT_GETEILT",
            (true, false) => "METALL_SPERRE_MASKIERT",
            (false, true) => "METALL_SPERRE_GETEILT",
            (false, false) => "METALL_SPERRE",
        };
        aus.push_str(&format!("{makro}({})\n", s.name));
    }
    if !zusatz.rcus.is_empty() {
        aus.push_str("\n/* -- rcu read sides (the body the emitter leaves to the environment). */\n");
        let mut r: Vec<&String> = zusatz.rcus.iter().collect();
        r.sort();
        r.dedup();
        for n in r {
            aus.push_str(&format!("METALL_RCU({n})\n"));
        }
    }
    if !zusatz.zellen.is_empty() {
        // The smallest cell array bounds the cores the image brings up, so
        // `gabbro_kern()` answers below every `per cpu` count of the unit.
        let mut z: Vec<&String> = zusatz.zellen.iter().collect();
        z.sort();
        z.dedup();
        let mut grenze = String::from("METALL_KERNE_MAX");
        for n in z {
            grenze = format!("METALL_MIN({grenze}, METALL_ZELLEN({n}_zellen))");
        }
        aus.push_str("\n/* -- per-cpu cells: at most as many cores as the smallest array has cells. */\n");
        aus.push_str(&format!("METALL_KERNE_GRENZE({grenze})\n"));
    }
    if !zusatz.eintritte.is_empty() {
        aus.push_str("\n/* -- ENTRIES: the stubs the emitter declares and does not define. */\n");
        for e in &zusatz.eintritte {
            let n = &e.name;
            let ruf = match &e.ruf {
                EintrittRuf::Bindung { ein, aus: ziel } => {
                    let args: Vec<String> = ein.iter().map(|r| format!("r->{r}")).collect();
                    let ruf = format!("gabbro_eintritt_{n}_verteiler({})", args.join(", "));
                    match ziel {
                        Some(r) => format!("r->{r} = (uint64_t){ruf}"),
                        None => ruf,
                    }
                }
                EintrittRuf::OhneZiel => "metall_eintritt_ohne_ziel()".to_string(),
                EintrittRuf::BindungFalsch => {
                    aus.push_str(&format!(
                        "/* entry {n}: its `regs in`/`regs out` are not the dispatch's parameters\n \
                         * and result -- no honest binding exists; the stub ends the machine. */\n"
                    ));
                    "metall_eintritt_bindung_falsch()".to_string()
                }
            };
            // **OFFEN O32 (9), Opus agent L:** an exception that pushes a CPU error
            // code gets the twin stub that drops it (`METALL_EINTRITT_FC`); such a
            // vector is never LAPIC-thrown, so it writes no EOI.
            if hat_fehlercode(e.vektor) {
                aus.push_str(&format!("METALL_EINTRITT_FC({n}, {ruf})\n"));
            } else {
                aus.push_str(&format!(
                    "METALL_EINTRITT({n}, {}, {ruf})\n",
                    if e.geworfen { 1 } else { 0 }
                ));
            }
        }
    }
    aus.push_str("\n/* -- ROOTS: one driver-owned stack and one join word per declared start. */\n");
    for i in 0..wurzeln.len() {
        aus.push_str(&format!(
            "static unsigned char stapel_{i}[65536] __attribute__((aligned(16)));\nstatic uint32_t wort_{i};\n"
        ));
    }
    aus.push_str("\n/* N_WURZELN counts the declared starts, one per occurrence -- the probe checks it\n * against the number of members the source's `concurrent` sets name. */\n");
    aus.push_str(&format!("#define N_WURZELN {}\n", wurzeln.len()));
    aus.push_str("\n/* -- The driver thread: start exactly the roots, join them. -------------- */\n\nint gabbro_metall_haupt(void)\n{\n");
    arenen_reservieren(&mut aus);
    // The entries are in the IDT before any root runs: a handler that arrives
    // for a root finds its stub.
    for e in &zusatz.eintritte {
        let n = &e.name;
        let setze = if hat_fehlercode(e.vektor) { "metall_idt_setze_fc" } else { "metall_idt_setze" };
        aus.push_str(&format!(
            "    {setze}(gabbro_eintritt_{n}_VEKTOR, gabbro_eintritt_{n});\n"
        ));
    }
    for (i, w) in wurzeln.iter().enumerate() {
        let c = &w.c_name;
        // A refused start joins what already runs, as in the hosted driver:
        // "the join covers exactly the spawned set" holds on the error path.
        let einsammeln: String = (0..i)
            .map(|j| format!("        gabbro_faden_warte(&wort_{j});\n"))
            .collect();
        aus.push_str(&format!(
            "    if (gabbro_faden_start({c}, stapel_{i} + sizeof(stapel_{i}), &wort_{i}) != 0) {{\n"
        ));
        aus.push_str(&format!("        metall_schreibe(\"start: {c} refused\\n\");\n"));
        aus.push_str(&einsammeln);
        aus.push_str("        return 2;\n    }\n");
    }
    for i in 0..wurzeln.len() {
        aus.push_str(&format!("    gabbro_faden_warte(&wort_{i});\n"));
    }
    if let Some(code) = nachlauf {
        aus.push_str("\n    /* -- Unit-specific observation (test half, not runtime). -- */\n");
        aus.push_str(code);
        if !code.ends_with('\n') {
            aus.push('\n');
        }
    }
    aus.push_str("    /* NACHLAUF: unit-specific observation goes here in test runs. */\n");
    aus.push_str("    return 0;\n}\n");
    aus
}

/// The `gabbro_faden_start` roots of a bare-metal driver, COUNTED: the first
/// argument of every call site, once per site.
pub fn metall_start_zaehlung(treiber_c: &str) -> BTreeMap<String, usize> {
    let mut zaehlung = BTreeMap::new();
    let mut rest = treiber_c;
    while let Some(i) = rest.find("gabbro_faden_start(") {
        let nach = &rest[i + "gabbro_faden_start(".len()..];
        let name: String = nach
            .trim_start()
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        if !name.is_empty() {
            *zaehlung.entry(name).or_insert(0) += 1;
        }
        rest = nach;
    }
    zaehlung
}

/// The pin of the bare-metal driver: the same multiset rule as
/// [`pin_pruefe`], read off the `gabbro_faden_start` sites.
pub fn metall_pin_pruefe(quelle: &BTreeMap<String, usize>, treiber_c: &str) -> Result<usize, String> {
    let treiber = metall_start_zaehlung(treiber_c);
    if treiber != *quelle {
        let zeige = |m: &BTreeMap<String, usize>| -> String {
            m.iter()
                .map(|(n, k)| if *k == 1 { n.clone() } else { format!("{n} x{k}") })
                .collect::<Vec<_>>()
                .join(", ")
        };
        return Err(format!(
            "the bare-metal driver starts other threads than the sources declare -- source: [{}], \
             driver: [{}]. Regenerate the driver",
            zeige(quelle),
            zeige(&treiber)
        ));
    }
    let gesamt: usize = quelle.values().sum();
    match n_wurzeln(treiber_c) {
        Some(n) if n == gesamt => Ok(n),
        Some(n) => Err(format!(
            "N_WURZELN is {n} but the sources declare {gesamt} start(s) in the bare-metal driver"
        )),
        None => Err("the bare-metal driver carries no `#define N_WURZELN <n>` line".to_string()),
    }
}

/// The roots of a hosted driver C file, COUNTED: the root named at every
/// `gabbro_faden_start` call site below the ROOTS marker, with the number of sites that
/// name it (a pool routine started twice has two sites). Read with a plain scanner and
/// not a C parser: [`erzeuge`] is the only writer of the files this reads.
pub fn faden_start_zaehlung(treiber_c: &str) -> BTreeMap<String, usize> {
    // **Since 2026-09-30 (C-free lane) the hosted driver has the bare-metal shape**:
    // `gabbro_faden_start(<root>, …)`, the root FIRST. The thread runtime written above the
    // roots declares and defines the same name, so the count starts at the ROOTS marker.
    let ab = treiber_c.find("/* -- ROOTS:").unwrap_or(treiber_c.len());
    metall_start_zaehlung(&treiber_c[ab..])
}

/// The declared starts of the sources as a multiset: short C name to the
/// number of `concurrent` occurrences naming it.
pub fn vorkommen<'a>(namen: impl IntoIterator<Item = &'a str>) -> BTreeMap<String, usize> {
    let mut m = BTreeMap::new();
    for n in namen {
        *m.entry(n.to_string()).or_insert(0) += 1;
    }
    m
}

/// The `#define N_WURZELN <n>` count of a driver C file, if present.
pub fn n_wurzeln(treiber_c: &str) -> Option<usize> {
    for zeile in treiber_c.lines() {
        let gekuerzt = zeile.trim();
        if let Some(rest) = gekuerzt.strip_prefix("#define N_WURZELN") {
            return rest.trim().parse::<usize>().ok();
        }
    }
    None
}

/// The pin: the source starts and the driver starts must be the same
/// MULTISET, and `N_WURZELN` must count them.
///
/// `quelle` maps the short C names of the declared roots to the number of
/// `concurrent` occurrences naming them (fix lane F4: a set pin could not see
/// a pool routine declared twice and started once). Returns the start count
/// on success; the error names both sides with their counts, so a stale
/// driver fails loudly instead of starting the wrong threads.
pub fn pin_pruefe(quelle: &BTreeMap<String, usize>, treiber_c: &str) -> Result<usize, String> {
    let treiber = faden_start_zaehlung(treiber_c);
    let zeige = |m: &BTreeMap<String, usize>| -> String {
        m.iter()
            .map(|(n, k)| if *k == 1 { n.clone() } else { format!("{n} x{k}") })
            .collect::<Vec<_>>()
            .join(", ")
    };
    if treiber != *quelle {
        return Err(format!(
            "the driver starts other threads than the sources declare -- source: [{}], driver: [{}]. \
             Regenerate the driver: a root added, dropped or started a different number of times \
             without regenerating starts the wrong threads",
            zeige(quelle),
            zeige(&treiber)
        ));
    }
    let gesamt: usize = quelle.values().sum();
    match n_wurzeln(treiber_c) {
        Some(n) if n == gesamt => Ok(n),
        Some(n) => Err(format!(
            "N_WURZELN is {n} but the sources declare {gesamt} start(s) -- \
             the join loop would miss a thread or read past the array"
        )),
        None => Err("the driver carries no `#define N_WURZELN <n>` line".to_string()),
    }
}

/// **What the generated MODULE driver needs to know** (C-free lane, C2, 2026-09-30).
///
/// Until this driver, a `module` unit was built around `laufzeit/kmodul/kmodul.c`, `arena.c`,
/// `sperre.h`, `bindung.h` and five type shims -- handwritten C, 850 lines, compiled into every
/// `.ko`. Now `gabbro build` writes that text from this plan, the way it writes the hosted and
/// the bare-metal drivers, and every piece of logic in it is a proved template
/// (`grammatik/Grammatik/SchablonenModul.lean`: `modul.lebenslauf`, `arena.modul`).
///
/// **NO NAME OF THE KERNEL IS IN HERE.** The two symbols the module loader calls and the notes
/// it reads (the licence) come from the MANIFEST, which is the program's text; every call below
/// the unit goes to the program's binding (`gabbro_kern_*`). So the build knows how to lay out
/// a loadable unit and nothing about which kernel loads it.
pub struct KmodPlan<'a> {
    /// The loader's load symbol (`kmod <kbuild> <load> <unload>`), defined by the driver.
    pub laden: &'a str,
    /// The loader's unload symbol.
    pub entladen: &'a str,
    /// The unit's own init function (C name), answering `uint32_t`: 0 loads.
    pub init: &'a str,
    /// The unit's own exit function (C name).
    pub exit: &'a str,
    /// `provision <bytes>`: the static storage of EACH dynamic arena. `None` when the manifest
    /// names none; the build refuses a `module` unit with an arena and no provision before
    /// generation, so the driver never guesses a size.
    pub vorrat: Option<u64>,
    /// `note <section> <text>`: one read-only string per line, placed in its section and kept.
    pub notizen: &'a [(String, String)],
    pub sperren: &'a [Sperre],
    pub wurzeln: &'a [Wurzel],
}

/// The report codes the module driver hands the program's binding. **Closed and numbered
/// here**, and the binding carries one sentence per code (`bibliothek/linux-kmod`). The gaps
/// (2, 4, 5, 7) are the codes of the old runtime's `vzalloc` reservation, which a static pool
/// no longer has; they stay unused rather than renumbered, so a binding written against the
/// old list reads no sentence under a wrong number.
pub const KMOD_MELDECODES: &str = "\
#define GABBRO_KERN_M_DESKRIPTOR    1u\n\
#define GABBRO_KERN_M_BODEN         3u\n\
#define GABBRO_KERN_M_UEBER_MAX     6u\n\
#define GABBRO_KERN_M_LADEN_ANTWORT 8u\n\
#define GABBRO_KERN_M_LADEN_STOPP   9u\n\
#define GABBRO_KERN_M_LADEN_FADEN  10u\n";

/// **The module arena runtime** (template `arena.modul`, `SchablonenModul.lean` §1).
///
/// A kernel module has no lazy commit and no process to end, so the storage of every dynamic
/// arena is a STATIC pool of the manifest's provision, zeroed by the loader like every `.bss`,
/// and the arithmetic is: span = min(ceiling, provision); the committed floor must fit the
/// span (else the LOAD is refused -- never a unit started with a smaller range); a `grow`
/// past the ceiling is a fail-stop the load function reads back; a `grow` past the span
/// answers `false` and the program's `else` runs (refuse-on-full below the ceiling). The
/// proved invariant is `committed * elem <= span <= provision`: every slot the unit can reach
/// lies inside its pool.
pub const KMOD_ARENA: &str = "\
/* -- The module arena runtime (template `arena.modul`). Each arena's storage is a static\n\
 *    pool of the provision; the loader zeroes it. No allocation, no kernel call. */\n\
#ifdef GABBRO_ARENEN\n\
static gabbro_arena_desc *const gabbro_modul_arenen[] = { GABBRO_ARENEN };\n\
#define GABBRO_MODUL_N_ARENEN (sizeof gabbro_modul_arenen / sizeof gabbro_modul_arenen[0])\n\
static uint8_t gabbro_modul_lager[GABBRO_MODUL_N_ARENEN][GABBRO_MODUL_VORRAT]\n\
    __attribute__((aligned(4096)));\n\
static uint32_t gabbro_modul_stopp;\n\
static uint64_t gabbro_modul_spanne(const gabbro_arena_desc *d)\n\
{\n\
    uint64_t decke = (uint64_t)d->max * (uint64_t)d->elem;\n\
    return decke < (uint64_t)GABBRO_MODUL_VORRAT ? decke : (uint64_t)GABBRO_MODUL_VORRAT;\n\
}\n\
static uint32_t gabbro_modul_reserve(gabbro_arena_desc *d, uint8_t *lager)\n\
{\n\
    if (d == 0 || d->base != 0 || d->max == 0u || d->elem == 0u || d->floor_hi > d->max) {\n\
        gabbro_kern_melden(GABBRO_KERN_M_DESKRIPTOR, d ? d->max : 0u, d ? d->floor_hi : 0u);\n\
        return GABBRO_KERN_M_DESKRIPTOR;\n\
    }\n\
    if ((uint64_t)d->floor_hi * (uint64_t)d->elem > gabbro_modul_spanne(d)) {\n\
        gabbro_kern_melden(GABBRO_KERN_M_BODEN, d->floor_hi, (uint64_t)GABBRO_MODUL_VORRAT);\n\
        return GABBRO_KERN_M_BODEN;\n\
    }\n\
    d->base = lager;\n\
    d->used = 0u;\n\
    d->committed = d->floor_hi;\n\
    return 0u;\n\
}\n\
bool gabbro_arena_grow(gabbro_arena_desc *d, uint32_t n)\n\
{\n\
    uint64_t neu;\n\
    if (d == 0 || d->base == 0) {\n\
        return false;\n\
    }\n\
    if (n == 0u) {\n\
        return true;\n\
    }\n\
    neu = (uint64_t)d->committed + (uint64_t)n;\n\
    if (neu > d->max) {\n\
        /* Past the ceiling: a fail-stop (`N426` holds it statically); the load reads it. */\n\
        gabbro_kern_melden(GABBRO_KERN_M_UEBER_MAX, neu, d->max);\n\
        gabbro_modul_stopp = GABBRO_KERN_M_UEBER_MAX;\n\
        return false;\n\
    }\n\
    if (neu * (uint64_t)d->elem > gabbro_modul_spanne(d)) {\n\
        /* Past the provision, below the ceiling: `committed` unchanged, the `else` runs. */\n\
        return false;\n\
    }\n\
    d->committed = (uint32_t)neu;\n\
    return true;\n\
}\n\
#endif\n";

/// **`<stdatomic.h>` for a build without a C library: the COMPILER's C11 atomics** (C-free lane,
/// C2). The emitter writes nine call forms (`atomic_load_explicit`, `atomic_store_explicit`,
/// five `atomic_fetch_*_explicit`, the weak and the strong compare-exchange) with the C11
/// orderings; each is mapped onto the GCC builtin that implements exactly that operation with
/// exactly that ordering -- the same builtins a hosted build's own `<stdatomic.h>` expands to.
/// So a module unit's atomics mean what they mean hosted: C11 as the compiler implements it,
/// the trust the hosted target already names ("the C and the hardware"). The ORDERING is passed
/// through untouched -- no row chooses a primitive -- and `instrumente/pruefe-kernelmodul.sh`
/// expands every (form, ordering) pair and holds it against that (its gift 8 drops one).
/// Until the C-free lane's C2 this was `bibliothek/linux-kmod/stdatomic.h`, 273 handwritten
/// lines mapping the forms onto the Linux kernel's own memory-model macros (named assumption
/// (M11) of `Zielsatz/Spec.lean`, revised with this change); a `_Atomic` object is a real
/// C11 atomic again, so a plain access to one is sequentially consistent rather than
/// unordered. A floating-point `atomic` stays refused for a module (`bau.rs::modulregel`).
pub const KMOD_STDATOMIC: &str = "\
typedef enum {
    memory_order_relaxed = __ATOMIC_RELAXED,
    memory_order_consume = __ATOMIC_CONSUME,
    memory_order_acquire = __ATOMIC_ACQUIRE,
    memory_order_release = __ATOMIC_RELEASE,
    memory_order_acq_rel = __ATOMIC_ACQ_REL,
    memory_order_seq_cst = __ATOMIC_SEQ_CST
} memory_order;
#define atomic_load_explicit(P, O) __extension__ ({ __auto_type __gabbro_p = (P); \\
    __typeof__((void)0, *__gabbro_p) __gabbro_w; __atomic_load(__gabbro_p, &__gabbro_w, (O)); \\
    __gabbro_w; })
#define atomic_store_explicit(P, V, O) __extension__ ({ __auto_type __gabbro_p = (P); \\
    __typeof__((void)0, *__gabbro_p) __gabbro_w = (V); __atomic_store(__gabbro_p, &__gabbro_w, (O)); })
#define atomic_fetch_add_explicit(P, V, O) __atomic_fetch_add((P), (V), (O))
#define atomic_fetch_sub_explicit(P, V, O) __atomic_fetch_sub((P), (V), (O))
#define atomic_fetch_or_explicit(P, V, O) __atomic_fetch_or((P), (V), (O))
#define atomic_fetch_and_explicit(P, V, O) __atomic_fetch_and((P), (V), (O))
#define atomic_fetch_xor_explicit(P, V, O) __atomic_fetch_xor((P), (V), (O))
#define atomic_compare_exchange_weak_explicit(P, E, D, S, F) __extension__ ({ \\
    __auto_type __gabbro_p = (P); __typeof__((void)0, *__gabbro_p) __gabbro_d = (D); \\
    __atomic_compare_exchange(__gabbro_p, (E), &__gabbro_d, 1, (S), (F)); })
#define atomic_compare_exchange_strong_explicit(P, E, D, S, F) __extension__ ({ \\
    __auto_type __gabbro_p = (P); __typeof__((void)0, *__gabbro_p) __gabbro_d = (D); \\
    __atomic_compare_exchange(__gabbro_p, (E), &__gabbro_d, 0, (S), (F)); })
";

/// **The three header names the emitted unit asks for, written for a build without a C
/// library** (`-nostdinc`, the kernel's own build). Every line maps a name C defines onto a
/// type or a builtin the COMPILER predefines (`__UINT64_TYPE__`, `__SIZE_TYPE__`,
/// `__builtin_isfinite`, the `__atomic` builtins); none names a kernel type, so these files
/// hold for any freestanding build of the same compiler.
pub fn kmod_koepfe() -> Vec<(&'static str, String)> {
    let kopf = |name: &str, rumpf: &str| {
        let waechter = format!("GABBRO_FREI_{}_H", name.trim_end_matches(".h").to_uppercase());
        format!(
            "/* GENERATED by `gabbro build` -- <{name}> for a build without a C library: the\n\
             \x20* compiler's own predefined types and builtins, no kernel type. Do not edit. */\n\
             #ifndef {waechter}\n#define {waechter}\n{rumpf}#endif\n"
        )
    };
    let mut ints = String::new();
    for b in [8, 16, 32, 64] {
        ints.push_str(&format!(
            "typedef __INT{b}_TYPE__ int{b}_t;\ntypedef __UINT{b}_TYPE__ uint{b}_t;\n\
             #define INT{b}_MAX __INT{b}_MAX__\n#define INT{b}_MIN (-INT{b}_MAX - 1)\n\
             #define UINT{b}_MAX __UINT{b}_MAX__\n"
        ));
    }
    ints.push_str(
        "typedef __INTPTR_TYPE__ intptr_t;\ntypedef __UINTPTR_TYPE__ uintptr_t;\n\
         #define UINTPTR_MAX __UINTPTR_MAX__\n#define SIZE_MAX __SIZE_MAX__\n",
    );
    vec![
        ("stdint.h", kopf("stdint.h", &ints)),
        (
            "stddef.h",
            kopf(
                "stddef.h",
                "typedef __SIZE_TYPE__ size_t;\ntypedef __PTRDIFF_TYPE__ ptrdiff_t;\n\
                 #define NULL ((void *)0)\n#define offsetof(t, m) __builtin_offsetof(t, m)\n",
            ),
        ),
        (
            "stdbool.h",
            kopf("stdbool.h", "#define bool _Bool\n#define true 1\n#define false 0\n"),
        ),
        ("math.h", kopf("math.h", "#define isfinite(x) __builtin_isfinite(x)\n")),
        ("stdatomic.h", kopf("stdatomic.h", KMOD_STDATOMIC)),
    ]
}

/// A section name or a note text as the build writes it into C: printable ASCII only, no
/// quote and no backslash (`emit.rs::abschnitt_attribut` gives the reason for the section
/// half: the name travels on into an unquoted assembler directive). `None` when it passes.
pub fn notiz_fehler(abschnitt: &str, text: &str) -> Option<String> {
    let name_gut = !abschnitt.is_empty()
        && abschnitt.chars().all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-' | '$'));
    if !name_gut {
        return Some(format!(
            "`{abschnitt}` is no section name -- letters, digits and `. _ - $` only"
        ));
    }
    if let Some(c) = text.chars().find(|c| !(c.is_ascii_graphic() || *c == ' ') || *c == '"' || *c == '\\') {
        return Some(format!(
            "the note `{text}` holds `{}` -- printable ASCII without `\"` and `\\` only, because \
             it is written into a C string as it stands",
            c.escape_debug()
        ));
    }
    None
}

/// **Render the driver of a `module` unit** (C-free lane, C2; templates `modul.lebenslauf`,
/// `arena.modul`). The emitted unit is INCLUDED (so its `static` init/exit and roots are
/// nameable), and everything it leaves undefined is defined here: the arena runtime, the lock
/// primitives, one kernel thread per declared root through the binding, and the loader's two
/// entry points in the order the lifecycle template proves:
///
/// * load: every arena's pool bound (a refusal refuses the LOAD), every lock initialised,
///   the unit's init; a non-zero answer or a fail-stop during it refuses the load and the
///   unit's exit is NOT called; then one thread per root -- a root that did not start makes
///   the load wait for the ones that did, and refuse;
/// * unload: every root has RETURNED, then the unit's exit.
///
/// Deterministic: same plan, same bytes.
pub fn erzeuge_kmod(einheit: &str, plan: &KmodPlan) -> String {
    let mut aus = String::new();
    aus.push_str(&format!(
        "/* GENERATED by `gabbro build` ({GENERATOR_KENNUNG}) -- the driver of the `module` unit\n\
         \x20* `{einheit}`. Do not edit. Templates `modul.lebenslauf` and `arena.modul`\n\
         \x20* (grammatik/Grammatik/SchablonenModul.lean). No kernel header and no kernel name:\n\
         \x20* the loader's two entry points and the notes are the manifest's, every call below\n\
         \x20* the unit is the program's binding (`gabbro_kern_*`). */\n\
         #include \"einheit.c\"\n\n"
    ));
    aus.push_str(KMOD_MELDECODES);
    aus.push_str(
        "void gabbro_kern_melden(uint32_t code, uint64_t a, uint64_t b);\n\
         int32_t gabbro_kern_verweigert(uint32_t code);\n\n",
    );
    for (i, (abschnitt, text)) in plan.notizen.iter().enumerate() {
        aus.push_str(&format!(
            "static const char gabbro_notiz_{i}[] __attribute__((section(\"{abschnitt}\"), used, \
             aligned(1))) = \"{text}\";\n"
        ));
    }
    if !plan.notizen.is_empty() {
        aus.push('\n');
    }
    aus.push_str("#ifdef GABBRO_ARENEN\n");
    match plan.vorrat {
        Some(v) => aus.push_str(&format!("#define GABBRO_MODUL_VORRAT {v}ull\n")),
        None => aus.push_str(
            "#error \"this unit declares an arena and its manifest names no `provision`\"\n",
        ),
    }
    aus.push_str("#endif\n");
    aus.push_str(KMOD_ARENA);
    aus.push('\n');

    // -- the locks (the emitter declares `L_nimm`/`L_gib`; the primitive is the binding's) --
    let mut sperren: Vec<&Sperre> = plan.sperren.iter().collect();
    sperren.sort_by(|a, b| a.name.cmp(&b.name));
    if !sperren.is_empty() {
        aus.push_str(
            "/* -- The lock primitives. The storage is this file's (a zeroed blob per lock), the\n\
             \x20*    operations are the program's binding. */\n\
             void gabbro_kern_sperre_init(uint8_t *s);\n",
        );
        if sperren.iter().any(|s| !s.maskiert) {
            aus.push_str(
                "void gabbro_kern_sperre_nimm(uint8_t *s);\nvoid gabbro_kern_sperre_gib(uint8_t *s);\n",
            );
        }
        if sperren.iter().any(|s| s.maskiert) {
            aus.push_str(
                "uint64_t gabbro_kern_sperre_nimm_maskiert(uint8_t *s);\n\
                 void gabbro_kern_sperre_gib_maskiert(uint8_t *s, uint64_t flaggen);\n",
            );
        }
        for s in &sperren {
            let l = &s.name;
            aus.push_str(&format!(
                "static uint8_t gabbro_sperre_{l}[256] __attribute__((aligned(64)));\n"
            ));
            if s.maskiert {
                aus.push_str(&format!(
                    "static uint64_t gabbro_sperre_flaggen_{l};\n\
                     void {l}_nimm(void)\n{{\n\
                     \x20   uint64_t f = gabbro_kern_sperre_nimm_maskiert(gabbro_sperre_{l});\n\
                     \x20   gabbro_sperre_flaggen_{l} = f;\n\
                     }}\n\
                     void {l}_gib(void)\n{{\n\
                     \x20   uint64_t f = gabbro_sperre_flaggen_{l};\n\
                     \x20   gabbro_kern_sperre_gib_maskiert(gabbro_sperre_{l}, f);\n\
                     }}\n"
                ));
            } else {
                aus.push_str(&format!(
                    "void {l}_nimm(void)\n{{\n\
                     \x20   gabbro_kern_sperre_nimm(gabbro_sperre_{l});\n\
                     }}\n\
                     void {l}_gib(void)\n{{\n\
                     \x20   gabbro_kern_sperre_gib(gabbro_sperre_{l});\n\
                     }}\n"
                ));
            }
            if s.geteilt {
                // Readers exclude each other too: the shared pair takes the same lock.
                aus.push_str(&format!(
                    "void {l}_nimm_geteilt(void) {{ {l}_nimm(); }}\n\
                     void {l}_gib_geteilt(void) {{ {l}_gib(); }}\n"
                ));
            }
        }
        aus.push('\n');
    }

    // -- the roots, one kernel thread each, through the binding (template `faden.modul`) --
    let mut wurzeln: Vec<&str> = plan.wurzeln.iter().map(|w| w.c_name.as_str()).collect();
    wurzeln.sort_unstable();
    if !wurzeln.is_empty() {
        aus.push_str(
            "/* -- The roots (template `faden.modul`): one thread each, started by the program's\n\
             \x20*    binding with the designator of a wrapper written here (an `entry fn`). The\n\
             \x20*    wrapper stores 0 into the root's join word once the root has returned; the\n\
             \x20*    word is 1 from just before the start, and a start that fails stores the 0\n\
             \x20*    itself. The wait re-reads the word and sleeps through the binding between. */\n\
             uint32_t gabbro_kern_faden_start(int32_t (*lauf)(uint8_t *), uint32_t nummer);\n\
             void gabbro_kern_schlafe(void);\n\
             static void gabbro_faden_warte(uint32_t *wort)\n\
             {\n\
             \x20   while (__atomic_load_n(wort, __ATOMIC_ACQUIRE) != 0u) {\n\
             \x20       gabbro_kern_schlafe();\n\
             \x20   }\n\
             }\n",
        );
        for w in &wurzeln {
            aus.push_str(&format!(
                "static uint32_t gabbro_faden_wort_{w};\n\
                 static int32_t gabbro_faden_{w}(uint8_t *unbenutzt)\n{{\n\
                 \x20   (void)unbenutzt;\n\
                 \x20   {w}();\n\
                 \x20   __atomic_store_n(&gabbro_faden_wort_{w}, 0u, __ATOMIC_RELEASE);\n\
                 \x20   return 0;\n\
                 }}\n"
            ));
        }
        aus.push('\n');
    }

    // -- the lifecycle (template `modul.lebenslauf`) --
    aus.push_str(&format!("int {}(void);\nvoid {}(void);\n", plan.laden, plan.entladen));
    aus.push_str(&format!("int {}(void)\n{{\n    uint32_t antwort;\n", plan.laden));
    aus.push_str(
        "#ifdef GABBRO_ARENEN\n\
         \x20   {\n\
         \x20       unsigned a;\n\
         \x20       for (a = 0; a < (unsigned)GABBRO_MODUL_N_ARENEN; a++) {\n\
         \x20           uint32_t c = gabbro_modul_reserve(gabbro_modul_arenen[a], gabbro_modul_lager[a]);\n\
         \x20           if (c != 0u) {\n\
         \x20               return gabbro_kern_verweigert(c);\n\
         \x20           }\n\
         \x20       }\n\
         \x20   }\n\
         #endif\n",
    );
    for s in &sperren {
        aus.push_str(&format!("    gabbro_kern_sperre_init(gabbro_sperre_{});\n", s.name));
    }
    aus.push_str(&format!(
        "    antwort = {}();\n\
         \x20   if (antwort != 0u) {{\n\
         \x20       gabbro_kern_melden(GABBRO_KERN_M_LADEN_ANTWORT, antwort, 0u);\n\
         \x20       return gabbro_kern_verweigert(GABBRO_KERN_M_LADEN_ANTWORT);\n\
         \x20   }}\n",
        plan.init
    ));
    aus.push_str(
        "#ifdef GABBRO_ARENEN\n\
         \x20   if (gabbro_modul_stopp != 0u) {\n\
         \x20       gabbro_kern_melden(GABBRO_KERN_M_LADEN_STOPP, gabbro_modul_stopp, 0u);\n\
         \x20       return gabbro_kern_verweigert(GABBRO_KERN_M_LADEN_STOPP);\n\
         \x20   }\n\
         #endif\n",
    );
    if !wurzeln.is_empty() {
        aus.push_str("    {\n        uint32_t fehler = 0u, f;\n");
        for (i, w) in wurzeln.iter().enumerate() {
            aus.push_str(&format!(
                "        __atomic_store_n(&gabbro_faden_wort_{w}, 1u, __ATOMIC_RELAXED);\n\
                 \x20       f = gabbro_kern_faden_start(gabbro_faden_{w}, {i}u);\n\
                 \x20       if (f != 0u) {{\n\
                 \x20           __atomic_store_n(&gabbro_faden_wort_{w}, 0u, __ATOMIC_RELEASE);\n\
                 \x20           gabbro_kern_melden(GABBRO_KERN_M_LADEN_FADEN, f, 0u);\n\
                 \x20           fehler = f;\n\
                 \x20       }}\n"
            ));
        }
        aus.push_str("        if (fehler != 0u) {\n");
        for w in &wurzeln {
            aus.push_str(&format!("            gabbro_faden_warte(&gabbro_faden_wort_{w});\n"));
        }
        aus.push_str(
            "            return gabbro_kern_verweigert(GABBRO_KERN_M_LADEN_FADEN);\n        }\n    }\n",
        );
    }
    aus.push_str("    return 0;\n}\n\n");
    aus.push_str(&format!("void {}(void)\n{{\n", plan.entladen));
    for w in &wurzeln {
        aus.push_str(&format!("    gabbro_faden_warte(&gabbro_faden_wort_{w});\n"));
    }
    aus.push_str(&format!("    (void){}();\n}}\n", plan.exit));
    aus
}

#[cfg(test)]
mod treiber_tests {
    use super::{
        erzeuge, erzeuge_kmod, erzeuge_metall, gueltiger_c_name, kmod_koepfe, metall_pin_pruefe,
        notiz_fehler, pin_pruefe, vorkommen, KmodPlan, Sperre, Wurzel,
    };
    use std::collections::BTreeMap;

    fn beispiel() -> (Vec<Wurzel>, Vec<Sperre>) {
        (
            vec![
                Wurzel {
                    c_name: "hauptA".to_string(),
                    gab_path: "hauptA".to_string(),
                },
                Wurzel {
                    c_name: "hauptB".to_string(),
                    gab_path: "hauptB".to_string(),
                },
            ],
            vec![Sperre {
                name: "L".to_string(),
                geteilt: false,
                maskiert: false,
            }],
        )
    }

    fn menge(v: &[&str]) -> BTreeMap<String, usize> {
        vorkommen(v.iter().copied())
    }

    /// **The generator's own output holds its own pin.** If this ever fails,
    /// the writer and the probe disagree about the shape -- and the probe is
    /// what every other test trusts.
    #[test]
    fn erzeugter_treiber_haelt_pin() {
        let (wurzeln, sperren) = beispiel();
        let c = erzeuge("beispiel124", &wurzeln, &sperren, None);
        assert_eq!(pin_pruefe(&menge(&["hauptA", "hauptB"]), &c), Ok(2));
        assert!(c.contains("void L_nimm(void)"));
        assert!(c.contains("void L_gib(void)"));
        assert!(!c.contains("_nimm_geteilt"), "no shared pair without a shared lock");
        assert!(c.contains("#define N_WURZELN 2"));
        assert!(c.contains("/* NACHLAUF:"));
    }

    /// **The hosted driver names no operating-system function** (server lane, 2026-09-28,
    /// TODO section 0e K8, second slice).
    ///
    /// The generated driver was the last place in the hosted runtime that called the OS by
    /// itself -- seven names, measured over a built binary by
    /// `instrumente/pruefe-os-bindung.sh`. That instrument is the wall; this test is the
    /// door before it, because it fails in a second and without a compiler, and because it
    /// reads the TEMPLATE rather than one probe's output: a name reintroduced for a shape no
    /// probe happens to have would pass the wall and fail here.
    ///
    /// Header names count as much as call sites: `#include <pthread.h>` is how the previous
    /// six arrived, and a driver that includes it has the whole library in reach again.
    #[test]
    fn der_treiber_nennt_keine_os_funktion() {
        let (wurzeln, sperren) = beispiel();
        let geteilt = vec![Sperre { name: "M".to_string(), geteilt: true, maskiert: true }];
        for (welcher, c) in [
            ("plain", erzeuge("beispiel124", &wurzeln, &sperren, None)),
            ("shared", erzeuge("beispiel124", &wurzeln, &geteilt, None)),
            ("with a NACHLAUF", erzeuge("beispiel124", &wurzeln, &sperren, Some("    (void)0;"))),
        ] {
            // The COMMENT half of the file is allowed to name what moved away -- it says
            // where the calls went, which is the point. Only code is read.
            let code: String = c
                .lines()
                .filter(|z| {
                    let t = z.trim_start();
                    !(t.starts_with('*') || t.starts_with("/*") || t.starts_with("//"))
                })
                .collect::<Vec<_>>()
                .join("\n");
            for name in [
                "pthread_", "fprintf", "printf", "abort", "exit(", "pause(", "malloc",
                "<pthread.h>", "<stdio.h>", "<stdlib.h>", "<unistd.h>",
            ] {
                assert!(
                    !code.contains(name),
                    "the {welcher} driver must not name `{name}`:\n{code}"
                );
            }
            // And the positive half: a green over a file that called nothing would say
            // nothing. The bound names ARE there.
            for name in [
                "gabbro_os_nachgeben", "gabbro_ticket_nimm", "gabbro_ticket_gib",
                "gabbro_faden_start", "gabbro_faden_warte", "gabbro_os_melden",
                "gabbro_os_klon_tor_trampolin", "gabbro_os_faden_ende",
            ] {
                assert!(code.contains(name), "the {welcher} driver calls `{name}`");
            }
        }
    }

    /// **Every lock is FREE before the first root starts, and needs no call for it** (C-free
    /// lane, 2026-09-30): the ticket lock is a zero `static` (`naechste == jetzt == 0`, the
    /// free state of `CTicket.lean`), so a root can never meet an uninitialised one -- the
    /// race the old `pthread_mutex_init` in `main` existed to prevent cannot be written.
    #[test]
    fn jede_sperre_ist_vor_dem_ersten_start_gesetzt() {
        let (wurzeln, _) = beispiel();
        let sperren = vec![
            Sperre { name: "A".to_string(), geteilt: false, maskiert: false },
            Sperre { name: "B".to_string(), geteilt: true, maskiert: false },
        ];
        let c = erzeuge("zwei", &wurzeln, &sperren, None);
        let erster_start = c.find("/* -- ROOTS:").and_then(|ab| c[ab..].find("gabbro_faden_start(").map(|i| ab + i)).expect("the driver starts a root");
        for n in ["A", "B"] {
            let decl = c
                .find(&format!("static gabbro_ticket sperre_{n};"))
                .unwrap_or_else(|| panic!("lock {n} is a zero static:\n{c}"));
            assert!(decl < erster_start, "lock {n} stands before the first start");
        }
        assert!(!c.contains("sperre_init"), "and nothing initialises it:\n{c}");
    }

    /// **A shared lock earns its shared pair, beside the exclusive one.**
    #[test]
    fn geteilte_sperre_bekommt_geteiltes_paar() {
        let (wurzeln, _) = beispiel();
        let sperren = vec![Sperre {
            name: "M".to_string(),
            geteilt: true,
            maskiert: false,
        }];
        let c = erzeuge("einheit", &wurzeln, &sperren, None);
        assert!(c.contains("void M_nimm(void)"));
        assert!(c.contains("void M_nimm_geteilt(void)"));
        assert!(c.contains("void M_gib_geteilt(void)"));
    }

    /// **A stale driver fails loudly, in both directions.** A dropped root
    /// and an added root both name the two sets -- the refusal says what
    /// changed, not just that something did.
    #[test]
    fn abgestandener_treiber_faellt_laut() {
        let (wurzeln, sperren) = beispiel();
        let c = erzeuge("beispiel124", &wurzeln, &sperren, None);
        let gefallen = pin_pruefe(&menge(&["hauptA"]), &c).expect_err("a dropped root must fail");
        assert!(
            gefallen.contains("hauptB") && gefallen.contains("hauptA"),
            "both sets are named:\n{gefallen}"
        );
        let gefallen = pin_pruefe(&menge(&["hauptA", "hauptB", "hauptC"]), &c)
            .expect_err("an added root must fail");
        assert!(gefallen.contains("hauptC"), "the added root is named:\n{gefallen}");
    }

    /// **The count is checked too, not just the set.** A hand edit that adds
    /// a thread but forgets `N_WURZELN` would join the wrong array.
    #[test]
    fn vergessener_zaehler_faellt() {
        let (wurzeln, sperren) = beispiel();
        let c = erzeuge("beispiel124", &wurzeln, &sperren, None).replace(
            "#define N_WURZELN 2",
            "#define N_WURZELN 3",
        );
        let gefallen =
            pin_pruefe(&menge(&["hauptA", "hauptB"]), &c).expect_err("a wrong count must fail");
        assert!(gefallen.contains("N_WURZELN"), "the count is named:\n{gefallen}");
    }

    /// **A pool routine named twice gets two threads** (fix lane F4, review G06
    /// F5). Two `gabbro_faden_start` sites, two blobs, `N_WURZELN 2` -- and a
    /// driver that starts it once fails the multiset pin, which the set pin
    /// before this lane let pass.
    #[test]
    fn pool_doppelt_zwei_faeden() {
        let w = Wurzel {
            c_name: "arbeiter".to_string(),
            gab_path: "arbeiter".to_string(),
        };
        let (_, sperren) = beispiel();
        let c = erzeuge("pool", &[w.clone(), w.clone()], &sperren, None);
        assert_eq!(
            c.matches("gabbro_faden_start(arbeiter,").count(),
            2,
            "two thread starts name the root itself:\n{c}"
        );
        assert!(c.contains("#define N_WURZELN 2"));
        assert_eq!(pin_pruefe(&menge(&["arbeiter", "arbeiter"]), &c), Ok(2));
        let einmal = erzeuge("pool", &[w], &sperren, None);
        let gefallen = pin_pruefe(&menge(&["arbeiter", "arbeiter"]), &einmal)
            .expect_err("one thread for two declared starts must fail");
        assert!(gefallen.contains("arbeiter x2"), "the count is named:\n{gefallen}");
    }

    /// **C names are ASCII words.** Anything else never reaches the file --
    /// it is refused before generation, never truncated into a name.
    #[test]
    fn c_namen_sind_ascii_woerter() {
        assert!(gueltiger_c_name("hauptA"));
        assert!(gueltiger_c_name("_ruhe"));
        assert!(!gueltiger_c_name(""));
        assert!(!gueltiger_c_name("9lebt"));
        assert!(!gueltiger_c_name("grüße"));
        assert!(!gueltiger_c_name("a-b"));
    }

    /// **Deterministic: same inputs, same bytes.** A driver that differed
    /// between two runs would make every comparison worthless (the same
    /// reason the emitter is held byte-identical in `pruefe-emission.sh`).
    #[test]
    fn zweimal_erzeugt_ist_bytegleich() {
        let (wurzeln, sperren) = beispiel();
        let a = erzeuge("beispiel124", &wurzeln, &sperren, None);
        let b = erzeuge("beispiel124", &wurzeln, &sperren, None);
        assert_eq!(a, b, "two runs are two identical artefacts");
    }

    /// **BOTH generated drivers reserve the unit's arenas, and the hosted one did not**
    /// (server lane, 2026-09-28, TODO section 0e K8).
    ///
    /// The emitted C writes `#define GABBRO_ARENEN &A_desc` and calls it *"the ONE list a
    /// driver needs to reserve before any of the unit's code runs"*. Until this test only
    /// `laufzeit/kmodul/kmodul.c` read it; the two generated drivers did not, so a unit with a
    /// dynamic arena ran with a NULL base and every `grow` took its `else` -- a dead heap and
    /// no word about it. What is checked here is the shape that closes it:
    ///
    /// * the reservation stands in BOTH drivers, and BEFORE the first start (a root that
    ///   allocated before the reservation would be the same defect one line later);
    /// * it is `#ifdef`-guarded, so a unit without an arena is untouched and no driver
    ///   references `gabbro_arena_reserve` for nothing;
    /// * the list comes from the emitted unit and is spelt nowhere else in the driver's CODE,
    ///   which is the whole reason it cannot drift (`W7`). Comment lines are dropped before
    ///   that count: the block's own header names the macro to say where the list comes from,
    ///   and prose naming a token is not a use of it -- the lesson `pruefe-osfrei.py` wrote
    ///   down, met here as a red on the first run.
    #[test]
    fn beide_treiber_reservieren_die_arenen_vor_dem_ersten_start() {
        let (wurzeln, sperren) = beispiel();
        for (welcher, c) in [
            ("hosted", erzeuge("beispiel124", &wurzeln, &sperren, None)),
            ("bare metal", erzeuge_metall("beispiel124", &wurzeln, &sperren, None)),
        ] {
            assert!(
                c.contains("#ifdef GABBRO_ARENEN"),
                "the {welcher} driver guards the block on the unit's own list:\n{c}"
            );
            assert!(
                c.contains("gabbro_arena_reserve(arenen[a]);"),
                "the {welcher} driver reserves every arena of the list:\n{c}"
            );
            let reserve = c.find("gabbro_arena_reserve(arenen[a]);").expect("the call stands");
            let erster_start = c
                .rfind("int main(void)")
                .or_else(|| c.rfind("int gabbro_metall_haupt(void)"))
                .map(|i| {
                    let nach = &c[i..];
                    i + nach
                        .find("gabbro_faden_start(")
                        .or_else(|| nach.find("gabbro_faden_start("))
                        .expect("the driver starts something")
                })
                .expect("the driver has an entry function");
            assert!(
                reserve < erster_start,
                "the {welcher} driver reserves BEFORE it starts a root"
            );
            let im_code = c
                .lines()
                .filter(|z| {
                    let t = z.trim_start();
                    !(t.starts_with('*') || t.starts_with("/*") || t.starts_with("//"))
                })
                .filter(|z| z.contains("GABBRO_ARENEN"))
                .count();
            // The hosted driver guards a third time: the arena runtime it writes (template
            // `arena.dyn`, C-free lane 2026-09-30) stands only in a driver whose unit has arenas.
            let soll = if welcher == "hosted" { 3 } else { 2 };
            assert_eq!(
                im_code, soll,
                "the {welcher} driver names the list in code only as guards and the \
                 initialiser, and carries no copy of it:\n{c}"
            );
        }
    }

    /// **The bare-metal driver holds its own pin, for a pool too** (Opus
    /// agent I). Same multiset rule as the hosted driver, read off the
    /// `gabbro_faden_start` sites; no hosted symbol in the file.
    #[test]
    fn metall_treiber_haelt_pin() {
        let (wurzeln, sperren) = beispiel();
        let c = erzeuge_metall("beispiel124", &wurzeln, &sperren, None);
        assert_eq!(metall_pin_pruefe(&menge(&["hauptA", "hauptB"]), &c), Ok(2));
        assert!(c.contains("METALL_SPERRE(L)"));
        assert!(c.contains("int gabbro_metall_haupt(void)"));
        assert!(c.contains("/* NACHLAUF:"));
        for gehostet in ["pthread", "stdio.h", "stdlib.h", "unistd.h", "printf", "main(void)\n"] {
            assert!(!c.contains(gehostet), "no hosted `{gehostet}` in the bare-metal driver");
        }
        let gefallen =
            metall_pin_pruefe(&menge(&["hauptA"]), &c).expect_err("a dropped root fails");
        assert!(gefallen.contains("hauptB"), "the sets are named:\n{gefallen}");

        let w = Wurzel {
            c_name: "arbeiter".to_string(),
            gab_path: "arbeiter".to_string(),
        };
        let pool = erzeuge_metall("pool", &[w.clone(), w.clone()], &sperren, None);
        assert_eq!(metall_pin_pruefe(&menge(&["arbeiter", "arbeiter"]), &pool), Ok(2));
        let einmal = erzeuge_metall("pool", &[w], &sperren, None);
        let gefallen = metall_pin_pruefe(&menge(&["arbeiter", "arbeiter"]), &einmal)
            .expect_err("one start for two declared fails");
        assert!(gefallen.contains("arbeiter x2"), "the count is named:\n{gefallen}");

        let geteilt = erzeuge_metall(
            "e",
            &wurzeln,
            &[Sperre {
                name: "M".to_string(),
                geteilt: true,
                maskiert: false,
            }],
            None,
        );
        assert!(geteilt.contains("METALL_SPERRE_GETEILT(M)"));
        assert_eq!(c, erzeuge_metall("beispiel124", &wurzeln, &sperren, None), "deterministic");
    }

    /// **Entries, masked locks, rcu and per-cpu cells reach the bare-metal
    /// driver** (Opus agent J). A `masks irqs` lock is the masked ticket, every
    /// entry gets its stub with its register binding and is installed BEFORE the
    /// first root starts, a thrown entry at a vector >= 32 writes the EOI and an
    /// entered one does not, a mismatched binding becomes the loud stub, and the
    /// smallest cell array bounds the cores.
    #[test]
    fn metall_treiber_mit_eintritten() {
        use super::{erzeuge_metall_voll, Eintritt, EintrittRuf, MetallZusatz};
        let (wurzeln, _) = beispiel();
        let sperren = vec![
            Sperre { name: "TAKT".to_string(), geteilt: false, maskiert: true },
            Sperre { name: "RING".to_string(), geteilt: false, maskiert: false },
        ];
        let zusatz = MetallZusatz {
            eintritte: vec![
                Eintritt {
                    name: "zeitgeber".to_string(),
                    vektor: 32,
                    geworfen: true,
                    ruf: EintrittRuf::Bindung { ein: vec![], aus: None },
                },
                Eintritt {
                    name: "syscall".to_string(),
                    vektor: 128,
                    geworfen: false,
                    ruf: EintrittRuf::Bindung {
                        ein: vec!["rax".to_string(), "rdi".to_string()],
                        aus: Some("rax".to_string()),
                    },
                },
                Eintritt {
                    name: "leise".to_string(),
                    vektor: 33,
                    geworfen: false,
                    ruf: EintrittRuf::BindungFalsch,
                },
                // OFFEN O32 (9): a #GP entry takes the error-code twin.
                Eintritt {
                    name: "gp".to_string(),
                    vektor: 13,
                    geworfen: false,
                    ruf: EintrittRuf::Bindung { ein: vec![], aus: None },
                },
            ],
            rcus: vec!["BACCT".to_string()],
            zellen: vec!["hoch".to_string(), "tief".to_string()],
        };
        let c = erzeuge_metall_voll("e", &wurzeln, &sperren, &zusatz, None);
        assert!(c.contains("METALL_SPERRE_MASKIERT(TAKT)"), "{c}");
        assert!(c.contains("METALL_SPERRE(RING)"));
        assert!(c.contains("METALL_EINTRITT(zeitgeber, 1, gabbro_eintritt_zeitgeber_verteiler())"));
        assert!(c.contains(
            "METALL_EINTRITT(syscall, 0, r->rax = (uint64_t)gabbro_eintritt_syscall_verteiler(r->rax, r->rdi))"
        ));
        assert!(c.contains("METALL_EINTRITT(leise, 0, metall_eintritt_bindung_falsch())"));
        assert!(c.contains("METALL_EINTRITT_FC(gp, gabbro_eintritt_gp_verteiler())"), "{c}");
        assert!(c.contains("metall_idt_setze_fc(gabbro_eintritt_gp_VEKTOR, gabbro_eintritt_gp)"));
        assert!(c.contains("    metall_idt_setze(gabbro_eintritt_leise_VEKTOR"));
        assert!(c.contains("METALL_RCU(BACCT)"));
        assert!(c.contains(
            "METALL_KERNE_GRENZE(METALL_MIN(METALL_MIN(METALL_KERNE_MAX, METALL_ZELLEN(hoch_zellen)), METALL_ZELLEN(tief_zellen)))"
        ));
        let setze = c.find("metall_idt_setze(gabbro_eintritt_zeitgeber_VEKTOR").expect("installed");
        let start = c.find("gabbro_faden_start(").expect("a root starts");
        assert!(setze < start, "entries are in the IDT before the first root runs");
        assert_eq!(metall_pin_pruefe(&menge(&["hauptA", "hauptB"]), &c), Ok(2));
        assert_eq!(c, erzeuge_metall_voll("e", &wurzeln, &sperren, &zusatz, None), "deterministic");
    }

    /// **The module driver names no kernel function and carries every piece its plan asks
    /// for** (C-free lane, C2): the loader's two symbols and the notes come from the plan, the
    /// arena pool from the provision, the masked pair only for a `masks irqs` lock, and one
    /// thread per root -- and the text is the same twice.
    #[test]
    fn der_modultreiber_nennt_keinen_kern_und_traegt_seinen_plan() {
        let sperren = vec![
            Sperre { name: "TAKT".to_string(), geteilt: false, maskiert: true },
            Sperre { name: "RING".to_string(), geteilt: true, maskiert: false },
        ];
        let wurzeln = vec![Wurzel { c_name: "eins".to_string(), gab_path: "m::eins".to_string() }];
        let notizen = vec![(".modinfo".to_string(), "license=MIT".to_string())];
        let plan = KmodPlan {
            laden: "lade_mich",
            entladen: "entlade_mich",
            init: "laden",
            exit: "entladen",
            vorrat: Some(8192),
            notizen: &notizen,
            sperren: &sperren,
            wurzeln: &wurzeln,
        };
        let c = erzeuge_kmod("probe", &plan);
        assert_eq!(c, erzeuge_kmod("probe", &plan), "deterministic");
        for muss in [
            "int lade_mich(void)",
            "void entlade_mich(void)",
            "antwort = laden();",
            "(void)entladen();",
            "#define GABBRO_MODUL_VORRAT 8192ull",
            "section(\".modinfo\"), used",
            "= \"license=MIT\";",
            "gabbro_kern_sperre_nimm_maskiert(gabbro_sperre_TAKT)",
            "gabbro_kern_sperre_nimm(gabbro_sperre_RING)",
            "void RING_nimm_geteilt(void)",
            "gabbro_faden_eins",
            "bool gabbro_arena_grow(",
        ] {
            assert!(c.contains(muss), "missing `{muss}`:\n{c}");
        }
        assert!(!c.contains("TAKT_nimm_geteilt"), "no shared pair for an unshared lock");
        for kern in ["linux", "module_init", "vzalloc", "printk", "kthread", "#include <"] {
            assert!(!c.contains(kern), "the driver names `{kern}`:\n{c}");
        }
        // Without a provision an arena unit does not compile, and says why.
        let ohne = erzeuge_kmod("probe", &KmodPlan { vorrat: None, ..plan });
        assert!(ohne.contains("#error \"this unit declares an arena and its manifest names no `provision`\""));
    }

    #[test]
    fn die_koepfe_nennen_nur_den_uebersetzer() {
        let koepfe = kmod_koepfe();
        let namen: Vec<&str> = koepfe.iter().map(|(n, _)| *n).collect();
        assert_eq!(namen, ["stdint.h", "stddef.h", "stdbool.h", "math.h", "stdatomic.h"]);
        for (n, text) in &koepfe {
            assert!(!text.contains("#include"), "{n} includes something:\n{text}");
            assert!(!text.contains("linux"), "{n} names linux:\n{text}");
        }
        assert!(koepfe[4].1.contains("memory_order_acquire = __ATOMIC_ACQUIRE"));
    }

    #[test]
    fn eine_notiz_ist_druckbar_und_ihr_abschnitt_ein_name() {
        assert_eq!(notiz_fehler(".modinfo", "license=Dual MIT/GPL"), None);
        assert!(notiz_fehler(".mod info", "x").is_some());
        assert!(notiz_fehler("", "x").is_some());
        assert!(notiz_fehler(".modinfo", "a\"b").is_some());
        assert!(notiz_fehler(".modinfo", "a\\b").is_some());
        assert!(notiz_fehler(".modinfo", "a\tb").is_some());
    }
}
