/-
  File:      Grammatik/Zielsatz/Akzeptiert.lean
  Subject:   PLAN-ZIELSATZ.md step 3 -- what the CHECKER decides, as ONE Bool
             (`Akzeptiert`), proved to be a `Pruefer` of `Spec.lean`
             (`akzeptiert_pruefer`): the Bool decides EXACTLY
             `AkzeptiertSpec` (`akzeptiert_iff`), given complete member
             lists. The start the PROOF works with is Spec's
             `StartZulaessig` (derived from the runtime's start `Laufzeit`
             and the user's `StartPflicht`, `startZulaessig_aus`), with a
             Bool for finite start tables (`startB`).

  `Akzeptiert P S fs ls cs ws` is the conjunction of every premise of the
  flagship theorems that is a decidable fact about the PROGRAM:

  | component      | Bool                   | field of `AkzeptiertSpec` (Spec.lean)                  | used by |
  |----------------|------------------------|--------------------------------------------------------|---------|
  | `frag`         | `programmImFragmentG`  | the same Bool                                          | `hFrag` of `ziel_ort_mehrfaden_ende` |
  | `abg`          | `abgAlleB`             | `∀ w, AbgK P fs (reachB P fs w)`                       | `hAbg` (with `K t := reachB P fs (init t).1`) |
  | `fuss`         | `fussWB`               | `∀ f, FussS P S (lokW P fs ws) f`                      | `hFuss` (with `StartZulaessig`) |
  | `stufen`       | `stufenB`              | `StufenM P`                                            | `hSt` of `keine_verklemmungG` |
  | `sperrOrte`    | `sperrOrteB`           | `∀ L c, c ∈ S.orte L → Bewacht c L`                    | first half of `hS : SperrInvOk S` |
  | `wurzeln`      | `wurzelnB`             | `∀ w ∈ ws, D.haelt w = [] ∧ D.gruende w = 0`           | `hLeer` / `hex`; no reasons at a start (`StartOhneGrund`) |
  | `einzeln`      | `einzelnPoolB`         | `EinzelnPool P fs ws` (a start declared twice is pool-safe; since F10, before `ws.Nodup`) | same-routine thread pairs in `schreibGetrenntK_of` |
  | `renn`         | `rennB`                | every unguarded, non-atomic carrier (payloads included) is `SchreibGetrennt` | `rennfrei_ungeschuetzt` (the checker's `H013`) |
  | `antworten`    | `antwortenB`           | every answer site of every body is an axiom `-> never` or has a non-empty type (`StelleOk`) | `fortschrittG_aus` (the stop `nieZurueck` is an axiom `-> never` only) |
  | `masken`       | `maskenB`              | `MaskenDisziplin P fs`: every function a handler's (`P.unterbricht`) call graph reaches takes only `masks irqs` locks | `kernHaltE_aus` (the leg `keinKernHalt`; Opus agent H, 2026-09-26, the Rust `H102`) |
  | `reset`        | `resetB`               | every declared static array admits zero (C18)          | the checked range-store expansion (`lowResetRangeL`) |
  | `bibliothek`   | `libraryB`             | `LibraryAdmission P`: generated programs are ordinary (C02 source certificates in `Uebersetzung.lean` carry the content) | by construction (`libraryB_immer`) |

  **Member lists.** `fs` (functions), `ls` (locks), `cs` (carriers:
  tables and globals). `D.Fn`, `D.Lock`, `D.Tab`, `D.Glob` carry no
  enumeration; `SperrInvOk`'s first half and the deadlock theorem quantify
  over every lock, and the race component over every carrier (a write-write
  race on a carrier that no footprint reads is visible to no footprint list,
  only to a list of ALL carriers). In `GabbroZiel` all three are
  `Aufzaehlung`s -- complete by their type.

  `ws : List D.Fn` -- the program's DECLARED THREAD STARTS (the checker's
  `concurrent { … }` members and `entry`/`boot` dispatch roots,
  `crates/gabbro-check/src/startexklusiv.rs`). Since 2026-09-15 they are a
  field of the program (`Einheit.starts`, Spec.lean) and the checker of
  `GabbroZiel` runs on `E.ws` (`akzeptiert_pruefer`); `Akzeptiert` keeps the
  list as an argument. The call graphs are COMPUTED from it (`reachB`),
  never supplied.

  **Changes of 2026-09-26 (Opus agent H, OFFEN O19):**
  * `masken` is NEW (`maskenB`): every function the program declares entered by
    hardware (`Programm.unterbricht`, the exported `entry … via idt`) has a call
    graph that takes only locks declared `masks irqs` -- the Rust `H102`. It is
    the premise the leg `keinKernHalt` reads (`kernHaltE_aus`,
    Zielsatz/Masken.lean). On a program with no handler it is `true`
    (`maskenB_ohne`), so every unit of before keeps its verdict.

  **Changes of 2026-09-22 (fix lane F10, OFFEN O18):**
  * `einzeln` is now `einzelnPoolB` (`EinzelnPool`): a routine declared at
    least twice is admitted when pool-safe (no signature lock, no reasons,
    every carrier its graph may write guarded or atomic) -- the Rust `N304`
    of lane 245. `getrenntW` pairs start OCCURRENCES (`mehrfachB`), so a
    pool routine's footprint carrier its own graph may write is thread-local
    no longer. On a repetition-free `ws` the Bool is unchanged
    (`akzeptiert_nodup_gleich`, PoolSym.lean).

  **Changes of 2026-09-15 (round-6 verdicts, finding W1):**
  * `antworten` is NEW: no body calls an axiom or reads a register at a declared answer
    type without a value, except an axiom `-> never` (`antwortenB`, decided exactly by
    `antwortenB_iff`; emptiness by `antwortB_iff`, EinpassenVoll.lean, over the function
    list for `fnptr n`). Before, such a site made every run of its body stop at
    `nieZurueck`, whose reason ("unreachable in the C as in G") holds only for `never`: the C
    call returns into a continuation nothing covered. Probe: `w1_abgelehnt`
    (Zielsatz/ProbenW1.lean) -- refused now, accepted by the old conjunction.

  **Changes of 2026-09-15 (third Opus verdict):**
  * `renn` no longer exempts publish payloads (P3): two starts writing one
    unguarded payload is a C11 race on a non-atomic object; `H013` has no
    payload exemption either. A payload read by one start and written by
    another was already refused by `fuss` (thread-locality over footprints),
    so only the write-write case changes.
  * `einzeln` is NEW: the declared starts are pairwise distinct. The runtime
    runs each on its own thread; two threads running one busy start would
    escape `renn` (which separates DIFFERENT starts) and would not be
    covered by Spec's `Laufzeit`.

  **Changes of 2026-09-14 (review findings):**
  * `renn` is NEW: a write-write race on an unguarded carrier that no
    footprint reads passed the old Bool (thread-locality was judged on
    footprints, which list reads, not writes). `rennfreiBis_of`
    proves Spec's `RennfreiBis` for EVERY carrier from the Bool's Prop and an
    admissible start (`rennfrei_alle`, RennfreiOrte.lean). Probe:
    `ak3_zwei_schreiber_ohne_lesen` (AkzeptiertZeuge.lean) -- refused now,
    accepted by the old conjunction.
  * `wurzeln` includes "no reasons" (`D.gruende w = 0`).
  * `zeit` (`rufTief` for every function) is DROPPED: it refused every
    recursive or indirect program, and Spec does not need it -- the time
    leg `ZeitAb` is conditional on `rufTief` per frame.
  * `StartZulaessig`/`Ruhig`/`SperrInvLokal` are Spec's (one definition).
    `Ruhig` now demands that an idle start writes NOTHING (before: no
    footprint carrier) -- two idle threads writing one unguarded carrier
    would race.

  **What could NOT be made decidable, and why:**
  * member-list completeness (`hvoll`, `hls`, `hcs`): the exporter's
    `inductive`s are finite, and the proof is `cases` per declaration.
  * `SperrInvLokal S` and `AxEnsLokal Q`: `S.inv L` and `Q a` are
    Bool-valued FUNCTIONS on memory, not syntax. User well-formedness.
  * `StartGut`, `∀ L, S.inv L sp`: since 2026-09-15 the USER's start
    obligation (`StartPflicht`, over the declared initial memory and
    arguments); decidable for a finite start table (`startB`).
  * NOT in `Akzeptiert`, although decidable per instance:
    `kostenPasst P passes decl fs` (the DECLARED costs; `decl` is not part
    of `Programm D`, and the check depends on `passes`).
-/
module

public import Grammatik.Zielsatz.Kern.Akzeptiert.Teil1
public import Grammatik.Zielsatz.Kern.Akzeptiert.Teil2
public import Grammatik.Zielsatz.Kern.Akzeptiert.Teil3
