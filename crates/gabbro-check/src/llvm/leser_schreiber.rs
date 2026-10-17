//! **Shared (reader) acquisition of a `lock` — `locks shared L { … }`.**
//!
//! A lock that declares `shared held <= n ops` is a reader/writer lock (the checker refuses
//! `locks shared` on any other one, gift 39). Its generated runtime is three words, all
//! `i32`, all zero at start, no C and no libc:
//!
//! * `<L>.naechst` / `<L>.bereit` -- the FIFO ticket gate (the exclusive lock of `ticket_nehmen`),
//! * `<L>.leser` -- the number of readers inside.
//!
//! **Writer** (`locks L`): take a ticket and wait for it (`ticket_nehmen`), then wait until
//! `leser == 0` (`acquire` load). It keeps the ticket for the whole section; release is
//! `bereit += 1` as before.
//!
//! **Reader** (`locks shared L`): take a ticket and wait for it, `leser += 1` (`acq_rel`),
//! give the ticket back at once (`bereit += 1`), then run the section. Release is
//! `leser -= 1` (`release`).
//!
//! **Invariants (why it is correct).**
//! 1. *Writers exclude writers and readers entering.* A reader enters only while it owns the
//!    ticket, so while a writer owns the ticket no new reader can increment `leser`.
//! 2. *Writers exclude readers inside.* A reader that incremented before the writer got the
//!    ticket did so before it released the ticket (its `bereit += 1`, seq_cst RMW); the writer's
//!    seq_cst load of `bereit` that admits it therefore sees that increment, and the writer
//!    waits until the matching `release` decrement is visible (`acquire` load of `leser`), so the
//!    reader's section happens-before the writer's.
//! 3. *Readers see the writer's writes.* The writer's release is `bereit += 1` (seq_cst RMW);
//!    a later reader's admitting load of `bereit` synchronises with it.
//! 4. *Readers do not exclude readers.* After the ticket hand-over they run concurrently.
//! 5. *No lost wakeup, no starvation of a writer.* All waiting is a spin on a load of a word
//!    the other side changes (the generated runtime has no sleep primitive to lose); tickets are
//!    FIFO, so a queued writer is overtaken by no later reader.
//!
//! All ticket accesses are `seq_cst` (as for the exclusive lock), which is `xchg`/`ldar`/`stlr`
//! level on x86_64 and aarch64; the reader count uses `acq_rel` / `release` / `acquire`,
//! enough by 2 and 3 above. Same IR on both targets, no target switch.
//!
//! A held shared acquisition travels in `Koerper::sperren` under the marked name `L#leser`
//! (`als_leser` unpacks it), so every exit (`return`, `leave`, `next`) releases it right.

use super::*;

const MARKE: &str = "#leser";

/// `L#leser` -> `Some("L")`.
pub(super) fn als_leser(gehalten: &str) -> Option<&str> {
    gehalten.strip_suffix(MARKE)
}

/// Reader entry: ticket gate, `leser += 1`, gate open again. Returns the name under which the
/// acquisition is held.
pub(super) fn leser_nehmen(k: &mut Koerper, name: &str) -> String {
    ticket_nehmen_roh(k, name);
    let leser = gteil(name, "leser");
    k.zeile(&format!("atomicrmw add ptr {leser}, i32 1 acq_rel, align 4"));
    ticket_freigabe_roh(k, name);
    format!("{name}{MARKE}")
}

/// Reader exit: `leser -= 1` with release (the section happens-before a waiting writer).
pub(super) fn leser_freigabe(k: &mut Koerper, name: &str) {
    let leser = gteil(name, "leser");
    k.zeile(&format!("atomicrmw sub ptr {leser}, i32 1 release, align 4"));
}

/// Writer side, after the ticket: wait until no reader is inside. A lock without a `shared held`
/// declaration has no readers and no `leser` word, and gets no wait.
pub(super) fn schreiber_wartet_auf_leser(k: &mut Koerper, name: &str) {
    if !k.s.schloesser.get(name).copied().unwrap_or(false) {
        return;
    }
    let leser = gteil(name, "leser");
    let warte = k.block("lock_leser_warte");
    let frei = k.block("lock_leser_frei");
    k.zeile(&format!("br label %{warte}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{warte}:");
    k.beendet = false;
    let n = k.tmp();
    k.zeile(&format!("{n} = load atomic i32, ptr {leser} acquire, align 4"));
    let leer = k.tmp();
    k.zeile(&format!("{leer} = icmp eq i32 {n}, 0"));
    k.zeile(&format!("br i1 {leer}, label %{frei}, label %{warte}"));
    k.beendet = true;
    let _ = writeln!(k.text, "{frei}:");
    k.beendet = false;
}
