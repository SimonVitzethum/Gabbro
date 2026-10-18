# Offen — was dem Projekt noch fehlt

*Updated 2026-10-17 for memory, stack, `own`/alias separation and model-based LLVM coverage. Enthält NUR Offenes aus fünf Gebieten:
LLVM-Backend, Lean-Modell, Prüfer, Übersetzungsvalidierung, Heap. IDs (`Oxx`) sind
stabil — Kommentare im Baum, die `OFFEN Oxx` nennen, meinen diese Abschnitte
(Historie in Git). Geschlossenes und
Entferntes steht im Anhang, je mit einer Zeile Grund.*

## 0. Order of work (Simon, 2026-10-17)

Strictly in this order; each step is Lean-first (model, then exporter/checker/compiler), no legacy, no German words in syntax.

**Phase A: dynamic data structures and their invariants** (plan: `dokumente/PLAN-DYNAMISCH.md` section 8a; covers O4-O6, O11, O14, O20, O29).
 1. `free`/`grow` as G blocks over the arena sugar; free-list invariant (`ArenaFrei.lean` is built, phase 1 part one).
 2. Invariants over live slots: links in range, acyclic along a walk, tree shape (capability tree), freelist disjoint from live slots; preservation theorems with witnesses and counter-models. DONE in Lean (2026-10-18, third pass, `PLAN-DYNAMISCH.md` 8a.1, SATZKARTE 79): list, tree and BOTH on one arena as ONE recognizer `Erk K` (guarded tree forms, disjointness of the two structures, loops `forever`/`traverse`/`retry`, function bodies `ErkE`), executed forms for the parent store, `revoke` of a subtree and bucket heads in a table field (`BaumOk`/`SibOk`/`HashOk` kept on executed blocks), witnesses run on real worlds and planted defects. Open: wiring the recognizer into `Akzeptiert` (8a.3, revised proposal: an arena as an invariant name, the `ErkE` derivation a certificate in the unit), the exporter for these forms, calls inside writers, the release of a whole revoked subtree, recognizers for hash chains and the sibling demand.
 3. Concurrency of arenas (O20): `grow` as a locked commit. DONE in Lean (2026-10-18, `PLAN-DYNAMISCH.md` 8a.2, SATZKARTE 79 step 3): a shared arena IS the lock invariant (`Dekl.sperr`), the section theorem (`abschnitt_erk` inline, `abschnitt_rufe` call form, `rufAt_erk`), `grow_atomar`/`grow_gesperrt`/`komm_nur_halter`, the machine bridge `erkE_maschine`/`erkE_maschine_erk` (loop-free writers, coverage derived from the certificate by `erkE_endR`), `invGutSD2_arena` (D3 against the proposed meaning D2), `ok_gleich_wort` (`dekl_ok_traeger`), `erkE_execEndH`; witnesses, planted defects. Open: the ABA ownership predicate, the commit bound (no `dynFrisch` form, frames do not name `zaehl`/`komm`; `Erk.wachs` now demands `0 ≤ n`), the footprint of a pure `pop` (`schuldet` counts tables only: a DECISION for step 4), the arena at writer entry, loops in the machine bridge, the migration D1 (needs `Syntax.lean` split and a full rebuild).
 4. `Spec.lean` diff (dynamic structures and table/group invariants leave NOT CLAIMED; `invRuhe`/`invSicht` non-vacuous), `gabbro_ziel` re-proved, two independent verdicts.
 5. Exporter/elaboration, then checker (O11), then the three examples (list, tree, hash chain) with certificates and poison probes.
 Open decisions: first structures (recommended list and tree), links as indices in one arena (recommended), `free` across function boundaries (follows the `own` boundary rule).

**Phase B: weak memory, items 1-5** (state: GX/W model carries atomics with the rely; release/acquire enforced).
 1. Message passing with a plain payload under release/acquire without a lock (O25, `N291`): model first (happens-before over the payload), then the checker rule; 11 corpus examples wait for it. **State 2026-10-18:** the memory-model half is PROVED (`Speichermodell/Payload/`, SATZKARTE §80: message passing, no race after the await, the value, counter-models, litmus tests); the `Spec.lean` diff D1-D6 and the checker rule R0-R4 are proposed in `PLAN-DYNAMISCH.md` §11 (not applied; four decisions for Simon in §11.5); no concrete W/GX fixture yet.
 2. Weak memory beyond DRF-SC: name and prove what is claimed (standard patterns), shrink the NOT CLAIMED line.
 3. Hardware bridge: x86-TSO, ARMv8 and RISC-V (RVWMO) refine W/GX, access by access, through the ISA-neutral `Need` list of Track L (needs the CPU models, built by Simon).
 4. Orderings and primitives: `consume`, `seq_cst` total order, stand-alone fences, mixed-size access, atomics over floats; litmus tests as the yardstick (MP, SB, LB, IRIW: allowed or forbidden as the model says).
 5. Shared atomics across link boundaries and the merge discipline of per-core cells (O17); lock-free structures (SPSC/MPSC ring, Treiber stack, seqlock, RCU) with happens-before over the payload; device and DMA ordering.

**Phase C: the rest** (in this order).
 1. Track P (complete Lean parser: coverage matrix, then elaboration replaces `lean_g.rs`) and Track L (refinement down to the binary: ISA-neutral `Code`, no CPU model; `PLAN-UEBERSETZUNGSVALIDIERUNG.md` 9a/9b). Both run now, in parallel with phase A.
 2. `boot` and `entrust` semantics in the model; aarch64 `vector`/`via` meaning; port space and `asm` in the model (the LLVM lowerings exist without a model).
 3. Interrupts and cores (O19 rest), arenas under concurrency (O20), `child` without a model (O21), gate preconditions (O23), strings (O24), source forms without a complete G export (O27), linking (O28), regions in G (O37).
 4. Termination, waiting bounds and fairness, stack depth, floats beyond the IEEE kernel.
 5. Benchmark against GCC `-O3`: only after the compiler lowers much more and strong optimisation is in (Simon).
 6. Housekeeping: C remnants (C templates in `schablonen.rs`, Lean folder `CBackend`, 13 compiler warnings), file split to an average under 500 lines (`instrumente/teile/lean-teilen.py`), the old Isabelle `.thy` set.

---

## 1. Heap and stack (updated 2026-10-17)

- **Built:** pressure-sampled unbounded arenas, slot release, external free-list
  links supporting small elements, per-chunk live counts and physical return of
  empty anonymous payload pages. Whole-arena reset clears counts and returns
  used payload pages. Virtual reservations/access rights and the committed
  prefix stay intact; best-effort page discard requires no decommit bitmap.
- **Built:** all direct/compatible indirect recursive cycles use a loop
  dispatcher and explicit growable continuation storage. Pure tail cycles keep
  their jump-only path. Continuation chunks are released on unwind; allocation
  failure is an explicit trap. This avoids recursion-dependent native stack
  growth, not the need for RAM to store non-tail continuations.
- **Built:** checked static range zeroing and optional whole-page return through
  declared program bindings; guarded per-invocation thread stacks, group spawn
  before join, kernel-exit completion and stack unmapping after join.
- **Still open:** `free` across function boundaries, aliases outside the tracked
  ownership discipline, complete `ArenaForm`/`DynForm` export and the G form of
  the newer memory statements. No checker refusal or source obligation was
  relaxed. CPU/final-byte refinement remains section 5 work.
- **Evidence:** `dokumente/LLVM-BACKEND.md`. Coverage is the actual Lean
  constructor/field register, checked by
  `python3 instrumente/pruefe-llvm-modelldeckung.py`; examples never define it.

## 2. Lean-Modell

- **O1-Rest (Pflichten jenseits der Maschine).** L50/L52 trägt das Bein `folge`,
  L24 die Invarianten-Beine, L34 steht als Existenz mit Zeuge. Offen: der Name
  von `breaking` im G-Rest (Markenschicht + Re-Beweis aller satzweisen Sätze),
  die Block-Wiederherstellungspflicht in (b), Axiom-/Register-Ereignisse im
  Ruf-Log, pfadsensitives `ende` (je Rückgabestelle), ein Ordnungsfeld in
  `Einheit` vom Exporteur gefüllt.
- **O4 (`cdt_wohlgeformt` bei freiem Slot).** Wartet auf O5 (Geschwister-Konsistenz);
  `delete_leaf` gilt nur bedingt, `revoke` erbt die Bedingung.
- **O5 (Geschwister-Konsistenz als Tabellen-Invarianten-Demand).** Indexieren
  DURCH die Option (`slots[s.next_sibling]`) blockiert; `requires` je Rufstelle
  ist Ersatz, kein Supply-once.
- **O6 (DEMAND 3 als schrankenloser Rangzeuge).** Geht für die Widerlegung;
  die Beweis-Richtung (`unsat`) über der Rangform plus vier ungezogene
  Erreichbarkeits-Zeilen bleiben bei der Demand.
- **Dynamische Datenstrukturen + Tabellen-/Gruppeninvarianten im Ziel (Plan 2026-10-17).** Lean zuerst, dann Exporteur,
  Prüfer, Compiler: `dokumente/PLAN-DYNAMISCH.md` §8a (sieben Stufen, drei Entscheidungen offen). Umfasst O4–O6, O11, O14, O20, O29.
- **O14 (Arena-Ketten: zwei Statement-Formen ohne Form).** Spezifikation und
  Exporteur haben die Form; zwei Statement-Gestalten schließen keine Kette.
- **O19-Rest (handlers and cores).** Since 2026-10-18 (Lean): G has a per-core mask state over the layer `KernZ` (`KernMaske.lean`), the core
  schedule is DERIVED from the machine (`kernPlan_aus_lauf`, `kernHaltM_aus`, `kernHaltE_iff_M`: the same statement), and `Code` has `Instr.imsk` with the
  named hardware assumption `MaskHw` and the refinement (`MaskRel.lean`, `irq_guard`); `PLAN-DYNAMISCH.md` 8a.4, SATZKARTE 81. Open: the `Spec.lean`
  proposal (8a.4, not applied) and its GA twin; the composition of the `Code` steps with the interleaving of all threads of a core (H3); re-entry and
  handler-on-handler preemption; `Einheit` names no handler; `H102` fires only on `via idt`; no Rust/LLVM emitter for `imsk`.
- **Reader/writer lock (decision 2026-10-18).** In Lean as the layer `RwSchritt` over machine G (`RwSchritt/RwRang/RwOrdnung/RwInv.lean`): exclusion
  (many readers XOR one writer), rank order and no wait cycle, no write-write/write-read race (premise `LeserLos`), the lock invariant visible to readers and
  owed by writers only; witnesses (two readers + a writer, kernel-checked) and planted defects (`RwZeuge`, `RwZeugeLeser`); `Code` lowering on one state word with
  `cas`/`aload`/`armw` and the refinement `RwRel` (`RwLock*.lean`); `PLAN-DYNAMISCH.md` 8a.5, SATZKARTE 82. Open: the `Spec.lean` diff (mode in G recommended) and the
  syntax (`lock L rank N rw`, `reads L { }`, signature `reads L`: proposals), the legs of `Ziel` with no layer twin, the checker rule deriving `LeserLos`, fairness; no Rust/LLVM.
- **O20 (Arenen unter Nebenläufigkeit).** Generationen und Commit-Decke nehmen
  einen Kontrollfaden und einmal betretene Wurzeln an. Seit 2026-10-18 (Lean, Phase A Schritt 3) ist eine
  geteilte Arena die Sperrinvariante (`Dekl.sperr`), der Abschnittssatz steht (`abschnitt_erk`/`abschnitt_rufe`),
  `grow` ist ein gesperrter, unsichtbarer Commit (`grow_atomar`); offen: ABA-Besitzprädikat, Commit-Schranke,
  Fußabdruck von `pop` (`schuldet`), Eintrittsfakt eines Schreibers.
- **O21 (`child` ohne Modell).** Der Kind-Faden existiert im Prüfer; sein Code
  zwischen Torruf und Region ist für das Kind ungeprüft.
- **O23 (Tor-Vorbedingungen nicht im Ziel).** NUL-Pfad und Rahmenlänge sind
  benannt, nicht modelliert.
- **O24 (Strings geprüft, nicht dargestellt).** NUL, `max`-Decke, Aggregate.
- **O27 (source forms without complete G export).** The source-to-G exporter
  remains partial, notably float, byte-pointer/string and dynamic-arena forms.
  A working LLVM lowering is not a Lean judgment. Track the constructor/field
  boundaries in `dokumente/llvm-modelldeckung.tsv`, not counts of examples.
- **O28-Rest (Verbund).** Spec-Diff ohne unabhängige Review-Runde; keine
  semantische Äquivalenz/Verfeinerung bei Verträgen (Normalform-Bäume);
  kein Zertifikat für verlinkte Programme; C-Linkschritt ist Sache der
  Validierung (§5).
- **O37 (Regionen in G).** Keine Byte-Zeiger im Modell (`Ty.ptr` ist
  Träger-Fähigkeit); nichts gibt eine Region frei (kein Eigentums-Schluss
  am Tor-Parameter); Gabbro-Rümpfe reichen keine Ausdehnung weiter
  (nur fremde `ensures … <= lenof(result)` trägt).

## 3. Prüfer

- **Legacy-Bereinigung, Stand 2026-10-17 abends:** `cnamen.rs`, `N041`/`N046`/`N052` mit Sätzen und 17 Gift-Proben und 42 tote
  Funktionen/Konstanten in Quelltext und Tests sind entfernt. Offen: 13 Compiler-Warnungen in `llvm.rs`/`nulpfad.rs`/
  `certstmt.rs` (zwei unerreichbare Muster, darunter der Verbund-Init für Konstanten, nie gelesene Felder), die
  C-Schablonen in `schablonen.rs`, der Lean-Ordner `CBackend` (17 Lean-Module außerhalb hängen daran),
  Kommentare mit `emit.rs`/C11. (Ursprüngliche Liste:
- **Legacy-Bereinigung (feste Regel 2026-10-17: kein Legacy in Compiler, Prüfer, Parser).** Gemessen in `crates/`:
  C11 in 79 Zeilen (23 Dateien), `emit.rs`/`gabbro emit` in 172 Zeilen (38 Dateien, meist Kommentare),
  C-Namensregeln (`cnamen.rs`, `erzeugernamen.rs`, `N041`-Familie), C-Schablonen in `schablonen.rs`,
  `certstmt.rs`, `E247`-Hinweis auf C-Gründe, `retired`-Codes (16 Zeilen). Alles entfernen, nicht
  umbenennen. Offene Entscheidung: gilt `grammatik/Grammatik/CBackend` (22 233 Zeilen, archivierte C-Kette) als Legacy
  des Modells?

- **Wächter-Reste (vier Wächter seit 2026-10-17).** `bruecke/` wird nicht gemessen (sein `lake build`
  scheitert am fehlenden `mathlib`-Eintrag); der baumweite `gabbro prove`-Lauf und der E1-Vergleich
  (Pflichten-Manifest) hängen in keinem Wächter; der Mutationslauf über den Prüfer ist ersatzlos
  gestrichen; 8 600 deutsche Kommentarzeilen im Prüfer sind nicht bewacht. Details:
  `dokumente/WERKZEUGKASTEN.md`.

- **O11 (hüterlose Invariante).** Eine `table`/`group`-Invariante, die keine
  Funktion `maintains`, wird von NICHTS gebucht (`N275`–`N277` prüfen nur
  verankerte).
- **Alias / `own` (gebaut 2026-10-17, Reste offen).** `R014` (Fehler) und `R015`
  (Hinweis) trennen Zeigerwurzeln an Rufgrenzen; Lean hat `ParamGetrennt` und
  `ObjGetrennt` (Objekte unterhalb einer Tabelle) samt Brücke zu `R014`; LLVM setzt
  `noalias` an interne schreibbare Zeigerparameter. Papier: `dokumente/A1-OWN-PAPER.md`.
  Offen: Records über Byte-Puffern (Bereichsobjekte im Modell, `LG005`/`LG001`);
  die vier Brücken-Hypothesen (`ParamVerschieden`, `RechteOk`, `HerkunftTreu`,
  `FrischNeu` nur für den Modell-Allokator) und der `let`-Lauf des Prüfers in Lean;
  `R004`/`R007` als Sonderfälle von `R014`; Mutationslauf (gestrichen mit den 80 Wächtern, kein Ersatz);
  `noalias` ist kein Lean-Urteil (O27).
- **O26-Rest (fremde Sperrprimitive).** Eigene Primitive geprüft (`N481`–`N483`);
  fremde bleiben angenommen (schwaches Gedächtnis nimmt acquire/release an).

## 4. LLVM-Backend

- **LLVM-Absenkungen ohne Lean-Modell (2026-10-17, Regel: Sprache folgt dem Lean-Modell).** Gebaut und nur als
  Text/qemu belegt: aarch64-`entry` (die Bedeutung von `vector`/`via` auf aarch64 ist eine Lesart des
  Absenkers, `SPRACHE.md` und das Modell sagen dazu nichts), `masks irqs`, x86_64-Port-Raum, Assembler-Körper.
  Verweigert, weil jede Absenkung Semantik erfände: `boot` und `entrust` (Quellform ohne Anweisung, Lean zuerst).
  Zu tun: die aarch64-Bedeutung von `vector`/`via` ins Modell, dann `boot`/`entrust` im Modell festlegen.

Volltabelle in `dokumente/LLVM-BACKEND.md` §5. Kurzform:

- **O22 — group execution and stack lifecycle built 2026-10-17.** Every
  invocation owns a guarded mapping and completion word. All roots start before
  any join; kernel `clear_child_tid` ends the join after actual exit, then the
  mapping is released. Trampoline assembly is confined to the stack switch.
  Runtime syscall numbers still belong to the Linux profile; OS-neutral
  bindings/profiles and the target-to-GX proof remain open.
- **`entries` (12 Stellen).** Hardware-Dispatch ohne Modell — benannt verweigert.
- **Stapel-Tore + `child` (12).** `clone`-Trampolin fehlt.
- **`publish` mit Nutzlast (11).** OFFEN O25 — vom Zielsatz nicht gedeckt.
- **Geteilte Sperren (3), Bibliotheksrufe (3).** Eigenes Primitiv / Nutzlast-Modell fehlt.
- **O40-Rest (Emitter-Namen).** Prüfer-Hälfte gebaut (`N042`); modulqualifizierte
  Namen fehlen beiden Emittern (LLVM mangelt `m_` nur bei Kollision).

## 5. Übersetzungsvalidierung — kommt VIEL später

Voraussetzungskette, in dieser Reihenfolge; nichts davon ist O27-Arbeit:

- **Vollständiges Lean-Modell einer CPU.** Ohne es keine Verfeinerung —
  das ist der lange Pol (ARM-PLAN: Sail-Arm plus Mehrkern-Modell), nicht O27.
- **Und mehr:** Brücke je Zugriff (Ziel → W/GX-Simulation pro Zugriff),
  Tor- + Eintritts-Lemmata je Ziel (rohe Anweisung, `_start` mit Stapel,
  Zustand, Austritt/`never`), O28-Linkschluss, O26-fremde Ordnungen.
- **Automatisch für alle Programme.** Kein Schritt je Programm von Hand —
  deshalb ist die Kette teurer als O27, nicht billiger: O27 erweitert die
  Urteil-Menge Programm für Programm, die Validierung muss danach für ALLE
  ohne Zutun laufen.

## Anhang — geschlossen oder entfernt (ID → Grund)

O2 zurückgezogen (Falsifikatoren ohne Schwelle); O3 gebaut; O7 gebaut;
O8 gebaut (Lane 167); O9 gebaut; O12 Einzelprogramm, kein Modellfall;
O13 gebaut; O15/O16 bepreist und ABGELEHNT (null Korpusnutzen);
O18 gebaut (F10); O25 geschlossen (Rely IST das Ziel, `gabbro_ziel`);
O10 Messschicht, kein Gebietsgegenstand; O29 außerhalb des Umfangs (Simon);
O30 überholt (Rust-Backend + Lean-Validator statt Selbsthosting);
O31 gebaut (Reste: Build/Hardware, nicht Gebietsgegenstand);
O32 Hardware/Laufzeit, kein Gebietsgegenstand; O33 Prozessbuchhaltung;
O34/O35/O36/O38 gebaut; O39 Kernelmodul-Welt (Zählung: `N574`–`N577` gebaut,
Unload-Fenster Hardware).
