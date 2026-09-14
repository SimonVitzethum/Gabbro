# VERDICT: Is the project goal reached now? (lane 173, second independent review, 2026-09-14)

Owner's goal: "A Gabbro user who wants to formally verify a Gabbro program proves
only their OWN logic plus named hardware assumptions; everything else -- memory
safety, data-race freedom, contracts holding where claimed in concurrent runs, and
time -- is carried by the language."

**Verdict: reached for the Lean model, not yet for the implementation.**
(Same headline as my 2026-09-13 verdict, on a strictly stronger basis: Opus items
1-3, the ones that blocked the *model* half of that sentence, are now closed as
theorems. What separates "reached" from today is implementation linkage plus one
narrow new model edge (§5) and the unchanged time leg.)

Base: branch `muse/173` at `bb2cdde1`. No existing file changed. One probe,
`.tmp/sonde173.lean` (not committed): `./lean-probe` **0 errors**. It re-checks
the current flagship `ziel_ort_mehrfaden_ende` (statement, premises, axioms),
probe A refuted (`paP_nicht_sperre`, `paP_nicht_sperre_leer`, `paP_halt`) and
probes B/C plus the two-active-thread witness certified (`zPB_zertifiziert`,
`zPC_zertifiziert`, `mP_zertifiziert`).

The current flagship is `ziel_ort_mehrfaden_ende` (`ZielOrtStart.lean:142`,
SATZKARTE §16.4): premises of `ziel_ort_mehrfaden`, conclusion the
`ziel_ort_sperre_inv` conclusion (`VertragAmOrtG ∧ SperrInvG ∧ KeinLogikHaltG ∧
progress ∧ InvAmOrtG`) AND `StartEndeG` (start functions' value completion).
Deadlock freedom is the separate `keine_verklemmungG` (`Verklemmung.lean`).
Axioms of the flagship and every witness named here: `[propext,
Classical.choice, Quot.sound]` (probed).

I did NOT read `messung/URTEIL-OPUS-2026-09-14*`. "Opus items" below means the
8 separation items of `messung/URTEIL-OPUS-2026-09-13.md` §6.

## 1. The 8 previous Opus items: status today

| # | Opus item | Status | Theorem / evidence |
|---|---|---|---|
| 1 | Stuck hole (probe A: `ensures false` everywhere certified) | **CLOSED** | `KeineLogik` clause in `KoerperGutZ`; `paP_nicht_ganz` / `paP_nicht_sperre` (obligation fails for every `Q`, every well-formed family); `paP_halt` (the stuck state is now a refutation: `¬ KeinLogikHaltG`). Re-probed green against the current flagship. |
| 2 | Shared-state contracts at a lock boundary (probes B/C) | **CLOSED** | `ziel_ort_sperre` with `SperrInv`/`execStmtH`/`HavocOk`: `zPB_zertifiziert` (B: `wrap ensures konto[0]==100`), `zPC_zertifiziert` (C: read inside `locks`), `sP_zertifiziert` (two writers, same routine, non-trivial invariant `konto[0]==konto[1]`). Consequences settled: `StartExklusiv` is start-only (`startExklusiv_ohne_haelt`, same routine on all threads in the witness); single-thread footprint proved (`ziel_ort_einfaden`); `RufPasst.hh` relaxed to inclusion with lock floors (§15.1, `HelferZeuge`). Re-probed green. |
| 3 | One goal theorem (frames + registers/awaits + axiom ensures) | **CLOSED** | `ziel_ort_ganz_vertrag` derives `ziel_ort_rahmen` and register-local `ziel_ort_voll_ax`; flagship carries `KoerperGutRQ` + `KeineLogik` + `SperrInv` + `InvGutS` in one statement. |
| 4 | Transfer to checker (`programmImFragmentG`, `fussOrtGB`, held-set equality) | **PARTLY** | Held-set equality moved model-side (§15.1). `E245-E249` (`wirkungen.rs`) enforce footprint-guard fragments, `N240` (`startexklusiv.rs`) start exclusivity, `N275-N277` (`sperrinv.rs`) lock-invariant read/purity thirds. But: no Rust rule computes the composed predicates (`programmImFragmentG`, `fussSperreB`/`FussS`+`lokK`, `AbgK`, `fussMehrB`, `StufenOk` floors); `lean_g.rs` emits them as `example := by decide` (Lean-side export, needs the Lean toolchain per program; a bad program is never refused by the checker on these grounds). No checker rule produces `S` (no surface lock-invariant clause). |
| 5 | Mechanical path `.gab` → `Programm D`; `gabbro prove` obligation | **PARTLY** | T3 Lean lexer/parser through items + source-to-G on 104 exist (PLAN §3 "Done"); `gabbro lean-g` export; per-constructor certificates; `corr-lean` printing. But: only 104 has a generated pin; 0 of the remaining 104 corpus files have a machine-produced `Programm D`; and `gabbro prove` still targets `Body.lean` ("no heap, no separation logic, no pointers and no concurrency", `lean.rs:18-19`) -- a different model from `KoerperGutS`. No tool states `KoerperGutS` for a real program except hand proofs. |
| 6 | One corpus program with real sharing, certified through the mechanical path | **OPEN** | Real sharing IS certified at model level (two writers `sP`, two active threads `mP`, both with reached runs and logged contracts BY THE THEOREM) but over hand translations. Through the mechanical path only the sequential 104 closes (`schlusssatz_104`). No two-thread shared-carrier program goes `.gab` → theorem. |
| 7 | Model → C (lock primitives, thread creation, DRF-SC as named premises) | **PARTLY (stage (a) only)** | `schlusssatz_104` closes one single-threaded chain (§4). Concurrent stage (b): statement shape planned with premises in the right place (PLAN §3 item 4), proof research-sized and not started. The emitter still produces no thread notion; lock primitives are extern prototypes in no theorem; G runs SC interleavings while C runs weak memory. |
| 8 | Time (waiting bound under fairness + hold-time; ops→cycles premise; `kostenPasst` wired to K001) | **OPEN** | Unchanged. `frame_schritte_beschraenkt` / `kosten_passt_deklaration` bound a frame's OWN STEPS under scheduler assumption; TARGET 4 (`held <= N`) is still not in the model; `kostenK` is still a hand reading; `kostenPasst` is still not a checker rule. "And time" remains a step bound, not timing. |

Re-probe detail (`.tmp/sonde173.lean`, `./lean-probe` 0 errors): `paP_halt`
states the refutation shape (`∃ M, reachable ∧ ¬ KeinLogikHaltG`), i.e. probe A
now fails the flagship's *conclusion* on a reachable machine and its *premises*
(`KoerperGutS`) for every `Q`/`S` -- both directions, not just one. B/C were
certified under `ziel_ort_sperre`; the current flagship generalises it
(`ziel_ort_sperre_invL` generic in `lok`, old checks as special cases), so the
certifications carry forward structurally (witnesses unchanged, full build green
per SATZKARTE §16).

## 2. Flagship premises, classified; Rust-today for each decidable fact

Statement verified by `#check` in the probe. Classes: (a) own logic,
(b) named hardware, (c) decidable program fact, (d) other. DATA = binder.

| Premise | Class | Rust checker computes it TODAY? |
|---|---|---|
| `P O passes Q S fs sp init e0 K` | DATA (`K` per-thread call graphs; `reachB` computes them Lean-side) | n/a |
| `hO : GutO O` | (b) HARDWARE (axiom frames, held locks, trace) | n/a (assumption, per `extern`/`asm`) |
| `hRL : RegLokal O` | (b) HARDWARE, strong (no async device step; autonomously changing registers provably outside) | n/a |
| `hQ : AxVertragO Q O` | (b) HARDWARE (per-declaration axiom ensures) | n/a |
| `hlok : AxEnsLokal Q` | (c) decidable per declaration | NO rule (Lean-side) |
| `hS : SperrInvOk S` | (c): guard half decidable; locality by construction | PARTLY: `N275` (read set), `N276` (purity), `N277` (declaredness) decide thirds; no rule for the composition, and no surface syntax produces `S` |
| `hvoll` | (c) trivial enumeration | NO (emitted list, nothing checks completeness) |
| `hFrag : programmImFragmentG` | (c) DECIDABLE | NO rule (`SYNTAX.md`: Lean-decidable, not a checker rule; `lean_g.rs` prints `example := by decide`) |
| `hAbg : ∀ t, AbgK P fs (K t)` | (c) decidable (`abgB`) | NO rule |
| `hWurzel` | (c) decidable per thread | NO rule |
| `hFuss : ∀ f, FussS P S (lokK P K) f` | (c) decidable (`fussMehrB`, finitely many active threads) | NO rule. Neighbours exist (`H007` per-access guard, `H222` guarded carrier, `E220/E221` contract footprint, `E245-E249` guard fragments) but none IS this predicate |
| `hK : KoerperGutS` | (a) USER (sequential triple + caller duty + no-`logik`, over every `HavocOk` move) | NO -- and correctly so; but no tooling states it for real code (`gabbro prove` aims at `Body.lean`) |
| `hStart : StartGut` | (a) USER boot duty | NO |
| `hSstart` (lock invariants at start) | (a) USER boot duty | NO |
| `hex : StartExklusiv` | (d) start-config fact; (c) for constant starts | PARTLY: `N240` enforces the per-entry shape; the infinite-`Faden` universal only collapses for constant assignments |
| `hI : InvGutS` | (a) USER (owed invariants at normal return; trivial if none owed) | NO |
| `hr : RufErreichbarG` | run DATA | n/a |
| deadlock side (`keine_verklemmungG`): `StufenM`, `hLeer`, finite `ls` | (c) decidable program facts | NO rule computes floors; `hLeer`/finiteness unwired |

Honest count: of ~9 decidable premises, ZERO are computed by the checker as the
exact predicate the theorem needs; three have partial neighbour rules
(`N240`, `E245-E249`, `N275-N277`). The flagship also keeps one conditional the
fine print should name: its progress conjunct still hypothesises `HeldGenau`
(the unconditional drop is the separate `ziel_ort_sperre_fortschritt`); and
`e0` still excludes carrier-less declarations structurally (28/91 files by the
old surface count; padding with an unused lock is possible but not a pipeline).

## 3. Ordinary programs: what certifies end to end today

"End to end" = `.gab` file → machine-checked theorem with no hand translation:

- **Exactly one program: `beispiele/104-referenz.gab`** via `schlusssatz_104`
  (single-threaded, stage (a); §4 for the assumptions this still rests on).
- Model level (hand translation, Lean theorems real and witnessed on reached
  runs that move memory): 104 via `ziel_ort_einfaden`/`ziel_ort_sperre`
  (empty family); `mP` (two ACTIVE threads, private tables + shared lock +
  table invariant + start completion + deadlock refutation); `sP` (two writers,
  same routine); `helfer` (held-set inclusion); `eP` (unguarded single thread);
  B/C; loop witness (`konto[0] <= 100` shared invariant, `KeineLogik` proved);
  retry/cost witnesses. `108`/`118` pass the `lean-g` + certificate sieves but
  close no chain.
- Everything else in `beispiele/` (105 files): no. Locks-block-only readers,
  non-local devices, carrier-less declarations, same-routine lock-holding
  starts, per-slot frames, reason-answer frames remain outside or unwired as
  booked before; the footprint/call-graph/floor checks have no checker rule, so
  even in-fragment programs stop at the hand-translation gap.

## 4. `schlusssatz_104`: what it establishes, under what

`schlusssatz_104 (c : Cert104) (hc : certOkG c = true)` (Schlusssatz104.lean:1395)
is stage (a) for ONE program, `gP` (the Lean parser's output):

1. **Parse fidelity:** `uebersetze104 src104 = .ok (gP, gFs)` -- lex, parse,
   elaborate, lower, each stage a propositional equation.
2. **Model certificates:** the Lean-side print of `gP`'s two bodies IS the
   pasted printer output, and `certEnd104Ok` accepts both.
3. **Model judgement:** `programmImFragmentG`, `fussOrtGB`, `KoerperGutS` and
   `InvGutS` for every function.
4. **Every C run:** the certificate elaborates to the emitted unit
   (`progOf c = refCProg`); for both functions, from ANY related C state/args,
   the Gabbro call ends `ok` and EVERY C run ends related (C determinism).
5. **The machine:** `gPB` (gP + runtime idle root) is `gP` under a checked
   renaming with the same C behaviour, and the goal conclusion
   (`ziel_ort_einfaden` + `InvAmOrtG`) holds on every reachable machine.

The single premise holds by `decide` on the printed certificate
(`schlusssatz_104_praemisse`); memory-moving witnesses exist on all three
levels (C+Gabbro, machine). Outside Lean, five named assumptions (PLAN §6):
**A1** the C compiler follows `CSemantik`/`CSpeicher`/`CFormen*`; **A2** the
emitted text IS the `CS` data `refCProg` (hand transcription -- no C parser in
Lean); **A3** the `Konto` layout (pinned by `_Static_assert`); **A4** the
runtime starts thread 0 in a source function and idles the rest (this is where
the idle root, which the model needs and `gP` cannot supply --
`gP_kein_exklusiv`, `gP_kein_ruhig` -- enters); **A5** the Lean kernel plus the
definitions listed for human review. Open even here: printer still prints
`refD`'s locals map; source pinned comment-free; part-4/part-5 agreement rests
on the adequacy chain, not re-instantiated; renaming proved for 104's two
functions only. Chain count is therefore **1 of 105**, single-threaded, with
A1/A2/A4 as load-bearing non-Lean trust. (Note: `messung/KETTE-2026-09-13.md`'s
"CHAIN COUNT: 0" post-dates the counter, not the merge; PLAN §6 books 1.)

## 5. Adversarial attempt: a new hole

**Candidate found (model edge, narrow): a start function that ends in a reason
(`retGrund`) owes nothing and is certified.** Case:

- `StartEndeG` covers `RetKopf` only, and `RetKopf` is value-returns only
  (`ZielOrtStart.lean:50-55`: `.ret` shapes; no `retGrund` case). §16.6 admits
  it ("a start function ending in a reason owes nothing").
- `InvGutS` covers normal returns only; `VertragAmOrtG` logs returns at pops,
  and a root frame never pops.
- `KoerperGutS` (SperreSem.lean, quoted SATZKARTE §14.2): first clause
  constrains `.zurueck` outcomes and `logik (vorbedingung _)`; second clause
  excludes `.logik e` for all `e`. A body ending `.grund g` satisfies both
  vacuously (`grund` is not `logik`).
- So a start function with `ensures false` whose body fails with a reason
  meets every premise; the flagship certifies the program; the claimed
  `ensures` is never checked anywhere, and no invariant is either.

This is the same *class* as probe A (vacuous certification past an outcome the
obligation does not exclude), one outcome over: probe A closed `logik`, this
leaves `grund` at thread roots. Its weight is lower than probe A's was --
callee `grund` was already by-design outside the slogan ("reason returns carry
no contract", both verdicts), and only root frames are affected -- but it is a
genuine hole in "contracts hold where claimed": the start function's claimed
contract is exactly what `StartEndeG` was added to cover, and the reason path
around it is open. Recommended test: a `paP`-style probe with `fail`/`grund`
at the root must fail `KoerperGutS` or extend `StartEndeG`; until then the model
half of the verdict carries the caveat "for value-returning runs".

I also re-examined the usual suspects and they do NOT yield holes: `KeineLogik`
quantifies over all `logik` outcomes (loop/table/transition/descent all end in
`logik`, covered); the `HeldGenau`-conditional progress is as stated, not
stronger than stated; `fussMehrB` thread-locality on declared (not actual)
writes is conservative (refusals, not admissions); no premise quantifies over
all contracts/statements/expressions (the waves-1-2 defect class is absent at
the flagship -- checked by `#check` in the probe).

## 6. Verdict restated, with the separation list (model vs implementation)

**Reached for the Lean model (for value-returning runs), not yet for the implementation.**

MODEL -- closed since the last round: stuck hole (item 1), lock-boundary
contracts (item 2) with all three consequences (start-exclusivity settled,
held-set inclusion with floors, one-active-thread footprint), combined theorem
(item 3), held-set inclusion, retry bound, `else`-`leave`/`next`, table/group
invariants at returns, several active threads with thread-local carriers,
start-function value completion, deadlock freedom. Axioms standard throughout;
witnesses non-degenerate (memory-moving reached runs, cross-thread values,
logged contracts BY THE THEOREM).

MODEL -- still open (narrow, named): §5 start-reason edge; invariants checked
at returns only (never while locks are held, never at entries); no
termination/`abstieg` bound; progress stops at `awaits` visibility (A10),
hardware outcomes, spent `forever` budget, caller-shape-at-pop; adequacy gaps
(`else` inside loops, indirect calls, `Tief` admission); `e0` carrier-less
exclusion. None of these is load-bearing for ordinary value-returning programs;
the start-reason edge is the one I would fix first.

IMPLEMENTATION -- the actual distance, ordered by weight:

1. **C linkage:** one single-threaded chain (104, assumptions A1-A5); concurrent
   stage (b) is a plan with the premises named. Threads, scheduler, lock
   primitives, weak memory: trusted, in no theorem.
2. **Checker wiring:** exact decidable premises (`hFrag`, `hFuss`, `hAbg`,
   floors, `S` composition) have no producing rule; `lean_g`'s `by decide`
   export needs Lean per program; `S` has no surface syntax.
3. **User-obligation tooling:** `gabbro prove` aims at `Body.lean`, not
   `KoerperGutS`/`InvGutS`; the user has no mechanical way to state -- let
   alone discharge -- the actual obligation for their program (except 104's
   closed instance).
4. **Time:** unchanged, open -- step bounds under scheduler assumption, TARGET 4
   not in the model, `kostenPasst` unwired.

The direction of travel since the last round is correct (three model items
closed as theorems, first chain closed with the assumptions named rather than
hidden), and the remaining model edge (§5) is smaller than any item it
replaces. But "the language carries it" still overclaims: the Lean model
carries it (for value-returning runs); the implementation carries one program.

---
CUTS (this verdict file): proves nothing; it classifies, counts and cites.
Corpus counts: 105 `beispiele/*.gab` files; surface-heuristic exclusions quoted
from prior verdicts, not re-measured. No existing file was changed; probe
`.tmp/sonde173.lean` is uncommitted scratch. `#print axioms` record (probed):
`ziel_ort_mehrfaden_ende`, `paP_nicht_sperre`, `zPB_zertifiziert`,
`zPC_zertifiziert`, `mP_zertifiziert` depend only on
`[propext, Classical.choice, Quot.sound]`.
