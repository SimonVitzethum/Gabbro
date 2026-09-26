# Opus agent D — invariants complete (2026-09-26)

*Branch of the worktree `agent-a2927f48bcf280903`, on master `38777111` (Merge Opus C). Everything
ran locally, through the queued wrappers (`./lean-bau`, `./lean-probe`, `./cargo-pruef`).
`free -g` at the start: 31 GB total, 18 GB available; at the end: 14 GB available.*

## 1. The task and the answer in one paragraph

`Spec.lean`'s NOT CLAIMED list read *"invariants at entry or while locks are held (claimed at
returns only)"*, and OFFEN O11 said a `table`/`group` invariant no function `maintains` was booked
by nothing. Both are closed: `Ziel` gains four legs (`invRuhe`, `invSicht`, `sperrWechsel`,
`sperrSicht`), `ZielF` one (`spawnSicht`), all proved, **no premise of `GabbroZiel` moved**; the
Rust checker gains `N496` (every writer of an invariant carrier names it in `maintains`). Two
words of the task could not be taken literally, and the statement says exactly what they can
mean: **"at every entry"** is false in general (a function called from inside a writer may see
the invariant broken), and **"while held"** can only mean observation points (the holder's
writes are shared memory at once).

## 2. What is claimed now (definitions in `Spec.lean`, proofs in `Zielsatz/Invarianten.lean`)

| leg | statement | premises it uses |
|---|---|---|
| `invRuhe : InvRuheG P M0 M` | every table/group invariant that reads only its carriers (`InvTraeger`) and held in the start memory holds in shared memory whenever no UNFINISHED thread has a frame of a function that owes it (`InvZu`) -- in particular at every entry reached outside every writer, at every thread start and spawn, and everywhere once the writers are finished | (b) through `invRueck`, `invGrund`, `StartEndeG`; `KeinStartGrundG` |
| `invSicht : InvSichtG P M0 M` | a thread outside every writer of `i` that holds a guard lock of one of `i`'s carriers sees `i` intact, whatever the other threads do | the above, lock exclusivity, the declaration's `U003` (`invarianten_gehalten`) |
| `sperrWechsel : SperrWechselG P O passes S M` | every step from `M` that ACQUIRES `L` goes from a memory where `S.inv L` holds to one where it holds; every RELEASE leaves one where it holds | `sperrInv` at `M` and at the successor ((a), (b)), exclusivity, `SperrInvOk` |
| `sperrSicht : SperrSichtG P O passes S M` | every step from `M` that accesses a carrier `L` protects holds `L`; while a thread holds `L`, no other thread's step moves such a carrier | (a) `sperrOrte`, exclusivity (`zugriff_haelt`, `relyG`) |
| `ZielF.spawnSicht` | a thread-machine step that makes a dormant slot live leaves the G state alone; the spawned thread holds no lock, every free lock has its invariant and every closed table invariant holds there | the thread-machine invariant, `sperrInv`, `invRuhe` |

**While held, precisely.** A lock invariant is a predicate over shared memory. Inside its section
the holder may break it, and then memory does not satisfy it -- the witness below shows such a
machine. What is claimed is that nobody else can observe that: no step of a thread not holding
`L` touches a protected carrier (`sperrSicht`, first half), the holder's view of the carriers
changes only by its own steps (second half), the section began at an acquire whose memory had
the invariant and the release restores it (`sperrWechsel`), and whenever no thread holds `L` it
holds (`sperrInv`, before). That is the lock invariant at every point where it can be observed.

**At entry, precisely.** A table invariant is owed by every function whose effects write one of
its carriers (`schuldet`), and inside such a body it may be broken. A callee of a writer can be
entered while it is broken, so no leg says "at every entry". The claim is `invRuhe`: at every
machine where no unfinished thread is inside a writer -- the entry of every function reached
there included. A writer's callee sees what the writer's `requires` to it says; that is the
user's logic, as before.

## 3. The Spec diff, reviewed (AGENTS §2)

* **Premises before/after:** identical. `Einheit`, `AkzeptiertSpec`, `Pruefer`, `LogikPflicht`,
  `StartPflicht`, `NutzerPflicht`, `HardwareAnnahmen`, `Laufzeit`, `GabbroZiel` are textually
  unchanged (the diff of `Spec.lean` touches the header, adds six definitions above `Ziel`,
  four fields of `Ziel` and one of `ZielF`).
* **Conclusion:** `Ziel` gains `invRuhe`, `invSicht`, `sperrWechsel`, `sperrSicht`; `ZielF`
  gains `spawnSicht`; no field is removed or changed.
* **Embedding:** every earlier leg is proved by the same term in `ziel_aus`/`zielF_aus`; the
  old `Ziel` is a projection of the new one. `gabbro_ziel_g` (machine G), `gabbro_ziel_vor`
  (the statement before Opus A, verbatim, FaedenVor.lean) and all 23 certificates build
  unchanged against the new statement (`lake build`: 318 jobs green).
* **Nothing weakened, and not decorative:** unlike `keinKernHalt` and `zeit`, the new legs are
  not premise-free (table above), and each has a witness at a reached machine where the thing
  it forbids to be SEEN is really there (section 5).
* **Why table invariants at `E.sp0` are the legs' hypothesis and not a (b) duty:** (b) did not
  demand them, and a (b) duty would drop from the statement every program whose declared table
  invariant is false at its initializer -- programs the old legs covered. As a hypothesis of
  the leg nothing is dropped; for a concrete unit it is decidable.
* **NOT CLAIMED line:** replaced by what is claimed; what stays named: a table invariant false
  at the start, one reading carriers outside its `traeger`, any invariant while an unfinished
  thread is inside one of its writers, a lock invariant inside its holder's section.
* **Axioms:** `#print axioms gabbro_ziel` = `[propext, Classical.choice, Quot.sound]`, and the
  same for `gabbro_ziel_g` and every new theorem. No `sorry`, `admit`, `axiom`,
  `native_decide`.

## 4. How it is proved

* `schritt_logArt` -- every step of G appends at most ONE call-log event, and a `rueck`/`grund`
  event's world carries the memory the step leaves (one tactic over the 70 rules).
* `rufLogPasstG_eind` -- a call log determines its key stack. With `rufErreichbarG_passt`:
  `schritt_schluessel` -- a step leaves a thread's key stack unchanged, pushes one key, or pops
  the head with its return event logged.
* `invRuhe_erreichbar` (induction over runs): outside every writer, a step moves no carrier of
  the invariant (`schritt_traeger`: a step changes only what its head function may write, and a
  frame that writes a carrier owes the invariant); the step that ends the last writer frame of
  an unfinished thread is either a logged POP (then `invRueck`/`invGrund` at that event) or the
  thread FINISHING at the writer's return (then `StartEndeG`, via `fertig_retKopf`).
* `invSicht_aus`: a writer holds every guard of the invariant by signature (`U003`), so a thread
  holding one excludes every other writer (`exklusivG`); then `invRuhe`.
* `sperrWechsel_aus`, `sperrSicht_aus`: exclusivity at the machine after an acquire and before a
  release, `sperrInv` there, `SperrInvOk` for the carriers the acquire does not move;
  `zugriff_haelt` and `relyG`.
* `faden_spawn_m`: a step that makes a dormant slot live is `start` or `kind`, which keep `K.m`.
* `inv_ohne_schreiber`: an invariant no function writes is never open, so it holds at every
  reachable machine given the start -- the model's frame half of O11.

## 5. Witnesses (`Zielsatz/InvariantenZeuge.lean`, program `mP` of MehrfadenZeuge.lean)

The legs are applied through their generic lemmas with exactly the premises `ziel_aus` feeds
them, supplied by `mP_zertifiziert`.

| witness | what it shows |
|---|---|
| `lock_gebrochen_unsichtbar` | six steps from the start: thread 0 holds the lock inside `setze(30)` and has written `konto[0] := 30`; memory has `konto = [30, 0]` (computed), so the lock invariant is FALSE there; BY `sperrSicht` no step of thread 1 from that machine accesses `konto` |
| `inv_erwerb_und_eintritt` | thread 0 runs its section, calls `pruefeA`, finishes; thread 1 then ACQUIRES the lock: `konto[0] == konto[1]` before and after the acquire, BY `sperrWechsel`; thread 1 then ENTERS `setze(70)`: the table invariant `privA[0] == privA[1]` is closed (`InvZu`, its only writer's thread is finished) and holds, BY `invRuhe`, in memory and at the entry world of `setze`'s frame |
| `tabelle_gebrochen` | one step from the start: `privA = [7, 0]`, the table invariant is FALSE, and it is OPEN (`hauptA`, which owes it, is running) -- the leg claims nothing there |

Refusal side of O11: `beispiele/gift/1231`-`1234` (below); model side: `ivPschlecht_nicht_invGutS`
(InvZeuge.lean) -- a writer that breaks an invariant it owes fails (b).

## 6. OFFEN O11 in Rust: `N496`

`m1.rs`, `invarianten_buchen`: a function with a body whose declared `effects`, or derived hull,
write, publish or consume a carrier of a `table`/`group` invariant must name it in `maintains`
(error `N496`). A `table` with `ops` stays exempt (carried by `table.ops.erhaltung`; the `ops`
condition of O11 stays open). Sentence `m1.invariante_gebucht` in `saetze.rs`.

**Corpus diff, measured over every `.gab` under `beispiele/` and `messung/`** (`.tmp/mess496.py`,
a local script): four files.

| file | before | after |
|---|---|---|
| `beispiele/09-ohne-zeiger.gab` | clean | **the invariant was FALSE**: `forall s : Kappenraum.slots[s].benutzt` -- the zeroed table breaks it at the start, and `blatt_loeschen` breaks it on purpose (its own `ensures` is `!benutzt`). Nobody owed it, so nothing noticed. Replaced by `frei_ohne_elter` (a free slot has no parent), which both writers keep, and both `maintain` it; clean |
| `beispiele/17-gruppe-ueber-zwei-sperren.gab` | clean | `einreihen` keeps its group invariant and now says so (`maintains`); clean |
| `beispiele/gift/66`, `108` | fall at `U007`, `M112` | `N496` joins; the expected codes still fall |

Poison probes (each falls at `N496` and nothing else): `1231` a table writer without
`maintains`, `1232` a group carrier, `1233` a `consumes`, `1234` a caller writing through its
callee. Positive probe: `crates/gabbro-check/tests/invarianten_buchung.rs` (snippets both ways,
09 and 17 clean). `./cargo-pruef`: 1336 passed, 0 failed (after piece 1).

## 7. Certificates

The exporter (`lean_g.rs`) and `obligations --g` are untouched, so every certificate is
byte-identical and `tests/zertifikate.rs` stays green without regeneration. 09 and 17 stay
UNCERTIFIED with the same first refusal (`LG001`: a `Region` mark, a `group`). The certificates'
theorems (`gP_gabbro_f`) now carry the new legs, through `gabbro_ziel`.

## 8. Findings

1. **`beispiele/09`'s table invariant was false** (section 6). It is the O11 gap made concrete:
   an invariant booked by nobody was also true of nothing.
2. **Every certified program has NO table invariant**: the exporter writes `Inv := Empty` and
   refuses `maintains` (`LG001`). So for certified programs `invRuhe`/`invSicht` are vacuous;
   the lock legs `sperrWechsel`/`sperrSicht` are not. The residue is a TODO bullet.
3. **Argued, NOT proved:** in the model, `U003` (a writer holds every guard of every carrier by
   SIGNATURE) together with lock-free roots (`AkzeptiertSpec.wurzeln`) and write propagation to
   the caller (`RufPasst.hw`) suggests that an invariant with a GUARDED carrier is written by no
   function reachable from an accepted start -- guarded table invariants would then be frozen,
   and the contentful case of `invRuhe` would be the unguarded one (a thread-local table, as
   `privA` in the witness). If so, the Rust `U003` (which admits writes under `locks`) and the
   model's differ; this was not measured and is reported as a question, not a result.
4. **"At every entry" is not a true sentence** about a language whose bodies may break the
   invariants they owe; the header now says what replaced it.

## 9. What remains

* Table invariants in the exporter (so the table legs bite for certified programs), with the
  start memory discharged per certificate by `decide`.
* O11's `ops` condition: whether a hand-written body writing a `table … ops` carrier must
  `maintain` the invariant (codes N497–N500 and gifts 1235–1240 stay reserved for it).
* Finding 3: measure or prove the frozen-guarded-invariant claim, and reconcile `U003`.

## 10. Commits

* `61da807a` piece 1: `N496`, gifts 1231–1234, examples 09 and 17, positive probe, sentence.
* `65a5b1b0` piece 2: the legs in `Spec.lean`, `Zielsatz/Invarianten.lean`,
  `Zielsatz/InvariantenZeuge.lean`, `Beweis.lean`.
* piece 3: SATZKARTE §52 (renumbered §53 at the merge with master, O25 took §52), OFFEN O11, TODO, AGENTS §2/§7, this report.
