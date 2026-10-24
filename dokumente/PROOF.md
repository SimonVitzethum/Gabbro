# Gabbro — the proof architecture

*Consolidated 2026-10-17. It replaces the former `PROOF.md` (1 712 lines of August
measurements), `dokumente/PROOF.md`, `dokumente/PROOF.md`, `dokumente/PROOF.md`,
`dokumente/PROOF.md`, the verdict files `messung/URTEIL-*`, the review of 2026-09-21,
`dokumente/PROOF.md` and the retired `TRAEGER-UND-HARDWARE` register. History is in git. Every
number below names the command that re-measures it (Part E, last section), or is marked historical (the retired counters are not guarded today); a claim that could
not be checked in this consolidation is listed at the end of that section.*

**What may be said:** *the goal theorem is proved over the Lean model, with a witness and
non-degeneracy, for the programs the exporter carries.* **What may NOT be said:** *Gabbro is
verified.* The checker inside the statement is the Lean Bool, not the Rust checker; the bridge
from the model to emitted code is only partly built (Part E).

**The one authoritative statement** is the header of
[`grammatik/Grammatik/Zielsatz/Kern/Spec.lean`](../grammatik/Grammatik/Zielsatz/Kern/Spec.lean)
(2 530 lines, of which about 1 470 are the header: THE ONE LIST of named assumptions, the NOT
CLAIMED list, the review package with file and line for every definition). This document is a
map of it. Where the two ever differ, `Spec.lean` wins and this file is wrong.

**Section ids.** Parts A–E carry their own ids (A1, B3, …). The sections of "Item 2 — which C"
keep the numbers §1–§5 of the former document, because code comments cite `PROOF.md §1`,
`§2` row 7 and `§3` for the legacy C lowering. Appendix: old → new ids.

---

# Part A — The criterion

## A1. Prove logic, nothing else

> Whoever proves a Gabbro program proves the **logic** of their program — and nothing else.
> Everything else falls out by construction or is named.

The dividing line (decided 2026-08-13): *an obligation is **plumbing** if its statement mentions
only the machine; it is **logic** if it mentions the subject.* Termination by running over a finite
set is plumbing; termination because "the scheduler makes progress" is logic.

| Plumbing — must fall by construction | Logic — written by the person |
|---|---|
| an index lies in range; no overflow | "the tree stays a tree"; "the refcount is the number of references" |
| frame condition (what is not touched) | "after `revoke`, `s` has no descendants" |
| lock held, lock order, no data race | "the message arrived at the right thread" |
| the loop ends because the set is finite | the loop ends because the algorithm makes progress |
| source ↔ lowering | the formulation of the invariant |

The number "proof lines : code lines" is a diagnosis, not the goal; a ratio counted without this
split is not a measured value. The one worked split (`delete_leaf` of the Caprock corpus,
2026-08-15) came out at 7 logic against 4 plumbing obligations, because a `match` over ten
variants is ten proof steps and one obligation.

## A2. Three outcomes, not two

Plumbing that **cannot** fall by construction (the Caprock zombie-stack reclaim: no core still
executes on a region when it enters the reclaim ring) is not left to the programmer and not
dissolved. It is **named and counted**: an `assume` with a falsifier in the axiom layer
(`gabbro annahmen`). Naming is not discharging; the layer is finite, named and ratcheted, and
that is what separates a gap paid in *reach* ("memory-safe under A1…An") from one paid in
*validity* (an unnamed assumption). Every gap the design leaves is meant to be moved from the
second currency to the first.

## A3. What the criterion does not decide

It is a decision, not a law of nature, and borderline cases are argued in the open. It orders
measurements, it does not replace them. A construct may be missing; a plumbing obligation that
stays hanging on the programmer refutes the sentence at exactly that point and names the
missing construct.

---

# Part B — The goal theorem

## B1. The statement

> A Gabbro user who wants to verify a program proves only their own logic plus named hardware
> assumptions. Memory safety, data-race freedom, contracts where claimed — in concurrent runs
> too — and time are carried by the language. *(Simon, 2026-09-13)*

`theorem gabbro_ziel : GabbroZiel` — statement `Zielsatz/Kern/Spec.lean`, proof
`Zielsatz/Atomar/BeweisAtomar.lean:343`; `Zielsatz/Kern/Beweis.lean` proves the version over plain
machine G directly. Everything is about ONE value `E : Einheit D`, the program the user wrote
(code with contracts, lock invariants, the axioms' declared `ensures`, declared starts with
arguments, declared initial memory, run-time roots).

```
∀ checker C, declaration D, unit E : Einheit D, complete enumerations of functions/locks/carriers,
  (a) C.akzeptiert E … = true             -- ONE Bool; PrueferX, sound against AkzeptiertSpecX
  (b) NutzerPflichtA E                    -- the USER's logic: every body at EVERY `forever`
                                          --   budget and against every value a shared-atomic
                                          --   read may return; plus the start duties
  (c) HardwareAnnahmen O E.Q              -- named hardware and foreign-code assumptions
  (d) Laufzeit E sp init                  -- the loader and the runtime's thread creation
  →  every reachable machine K of the THREAD machine over GX satisfies ZielFX
```

**Quantifier discipline** (the lesson of probes A and D): everything a prover could pick to
empty an obligation is universally quantified — the budget `passes`, the oracle (restricted only
by (c)), start memory, start assignment, the run. A premise that fits none of (a)–(d) is a
finding, not a premise.

## B2. What the conclusion says (legs of `Ziel`)

| Leg | In words | Needs |
|---|---|---|
| `speicherSicher` | every access carries its carrier's guards and the locks are held; bounds and types are intrinsic to `Programm D` | nothing (every well-typed program of G) |
| `rennfrei` | cross-thread access pairs with a write are lock-ordered, for every carrier except `atomic` ones (`schwach` covers those) | (a), (c) |
| `vertrag`, `invRueck`, `invGrund`, `startEnde`, `keinStartGrund`, `keinLogikHalt` | `requires` at every logged entry, `ensures` and owed invariants at every logged return, the start frame completes, no thread stops at a loop-invariant or transition check | (b), (c) |
| `sperrInv`, `sperrWechsel`, `sperrSicht` | every free lock has its invariant in memory; every acquire starts from it, every release restores it; no other thread touches a protected carrier while a lock is held | (a), (b) |
| `invRuhe`, `invSicht` | a table/group invariant holds wherever no unfinished thread is inside a writer, and at every point of a thread holding one of its guards outside every writer | (b) |
| `keineVerklemmung`, `keinZyklus`, `fortschritt` | no deadlock, no wait cycle (locks and join waits); every stop is one of the named stops (B5) | (a) |
| `keinKernHalt` | with the program's own interrupt handlers (`via idt`), no same-core handler deadlock under the named core plan | (a) `masken` |
| `schwach` | the weak-memory machine W adds no behaviour on an accepted program, for every order assignment | (a), (c) |
| `zeit` | a frame's own G-steps ≤ the syntax-computed `kostenTief` (finite call trees only) | nothing |
| `folge` | order of calls in every thread's call log (an entry or return directly behind a named function's return) | nothing |
| `spawnSicht`, `schlafendUnberuehrt`, `joinFrei`, … | threads created at run time (`start`, `child`) enter holding nothing, a spawn leaves the G state alone, joins end only when all roots are finished | (a), (d) |

*What `Ziel` adds over `NutzerPflicht`* is the point of the theorem: (b) is sequential per
function; the theorem returns it on the **interleaved** machine together with race freedom,
the global lock-invariant fact, progress and the weak-memory leg — none of which is in (b).
`speicherSicher`, `zeit` and `folge` hold with no premise at all; for them a user proof is never
needed.

## B3. Variants, and why nothing was weakened

Every extension is a **reviewed diff of `Spec.lean`**: premises and conclusion move only with
the old statement derived as a corollary.

| Statement | What it covers | Relation |
|---|---|---|
| `GabbroZiel` (`gabbro_ziel`) | thread machine over GX; atomic rely; conclusion `ZielFX` | the current statement |
| `GabbroZielSC` (`gabbro_ziel_sc_aus`) | the statement before the atomic rely (`Ziel` over G, sequentially consistent) | a corollary: every checker of before is a `PrueferX`, and with no shared atomic GX is G |
| `GabbroZielVor` (`gabbro_ziel_vor`) | the statement before run-time threads (units with no `gestartet`) | a corollary |
| `gabbro_ziel_g`, `gabbro_ziel_schwach`, `gabbro_ziel_folge` | `Ziel` on plain G runs; every leg on every machine W reaches; the order leg for every order specification a program passes | corollaries |
| `GabbroZielVerbund` (`gabbro_ziel_verbund`) | a program LINKED from two separately compiled units over one link declaration, the SAME hardware assumptions, link check `SchnittstelleSpec` (`gabbro link`, `N501`–`N505`) | a second statement; conclusion `ZielF` on the linked unit |

The atomic rely (2026-09-26): a flag, counter or per-core cell written by one thread and read by
another without a lock is admitted (`GeteiltV`, no contract may mention it — `N484`), the
user's proof must then hold *whatever the read returns* (`LogikPflichtA`), and `schwach` becomes
`SchwachX`. One caveat of the review is part of the record: "verbatim" for `GabbroZielSC` is the
text; machine W gained the field `rmw`, so the leg speaks about fewer W steps than W without it
would have admitted (assumption (2) of B4 carries the difference).

## B4. The named assumptions (the ONE list is the `Spec.lean` header)

Premise (c) and the runtime part of (d) are the only places where hardware or foreign code
enters. In the statement they are:

* `GutO` — axiom answers stay inside the declared write frame, keep held locks and trace;
* `RegLokal` — register and `awaits`-visibility answers depend only on the declared device
  carriers. It is stronger than hardware: a register with no `depends` answers the same in every
  world, so an autonomously changing status register breaks it (found in round 3, kept named);
* `AxVertragO` — axiom answers meet their declared `ensures` (this is the content of
  `E.Q`; `Q := false` is an honest vacuity, visible in the declaration);
* `Laufzeit` — each declared start is placed on a thread, the root runs elsewhere; a run-time
  root's arguments and entry world are the unit's; spawn sites are the checked ones
  (`N456`, `N461`); every spawn succeeds.

**Assumptions of the reading** (what G being the meaning of the emitted code needs; since the
weak-memory leg the clause "the hardware is DRF-SC" is withdrawn):
(1) machine W over-approximates the C11 (RC11) model at G's step granularity;
(2) the compiler and hardware implement C11 atomics as specified, and an `exchange` lowers to
one read-modify-write; (3) every lock primitive `<L>_nimm` is an acquire and `<L>_gib` a release
(own primitives are checked: `N323`, `N481`–`N483`; foreign ones are assumed); (4) carriers are
the locations; (5) what G reads without recording (foreign answers, register reads, `awaits`
visibility) sees G's memory.

**Not a premise but a report: the permitted stops** of `fortschritt`: hardware answers outside
the declared type (answerable types only), a register answer against its declared promise,
`nieZurueck` (an axiom declared `-> never` returns nothing), `flagge` (an `awaits` whose flag is
not visible — a wait, never a failure), `budget` (a spent `forever` budget: a model artefact).
Any other empty answer type is refused by the checker (`AkzeptiertSpec.antworten`, Rust
`N310`–`N314`). Progress is "every stop is named", not "every wait ends".

The axiom layer on the language side stays `gabbro annahmen`; one open line there: the MMU's
write of the accessed/dirty bits is an assumption (`A7`) no pass reads, and the construct that
would carry it (`hardware A, D;` at a `walk`) was priced and **not built**, because the
collision it guards needs a `group … ops` and a `walk … by ops` the grammar does not have.

## B5. NOT CLAIMED

Named in the header, never hidden; each extension of the goal is a reviewed diff.

**Computational universality is not proved.** The results in `grammatik/Grammatik/Berechenbarkeit/` (THEOREM-MAP 91)
establish exact conditional exits and the distinction between the core safety checker, unbounded machine-G stacks,
and the additional recursive-descent duty. A finite universal simulator and its correspondence proof are still open;
neither a `forever` loop nor removal of an arena's written `max` establishes Turing completeness.

* termination and waiting bounds under fairness (`zeit` bounds finite call trees only; a waiting
  bound exists separately, B6); starvation freedom; stack depth (G's stacks are unbounded);
* the C and the hardware (translation validation's job, Part E); linking at the C level;
* contracts, `requires`, `ensures` or invariants *over* a shared atomic (refused, `N484`);
  per-core cell merging beyond the reader's rely (OFFEN O17); the
  publish/await hand-off of an unguarded plain payload (refused by the checker);
* invariants inside a running writer or a held section (claimed everywhere else); a table
  invariant false at the start memory (the hypothesis of the leg); an invariant reading carriers
  outside its declared set;
* interrupt handlers: that the hardware schedules as `KernPlan` says; re-entry; handler on
  handler; the emitted C realises no masking at all — translation validation has nothing to
  relate `KernPlan` to (OFFEN O19-Rest);
* orders of effects that are not calls of Gabbro functions, across a compound statement, an
  indirect call or a lock block, "sometime before"; the names in `breaking I` (OFFEN O1-Rest);
* threads created at run time with per-spawn arguments, the end of a join wait, a failing spawn
  (OFFEN O21); a busy routine declared ONCE on several threads;
* linked units with differing hardware assumptions, callbacks through an import, sharing an
  atomic across a link, dynamic loading (OFFEN O28-Rest);
* floats beyond the kernel IEEE model (bit-exact is not accurate: error bounds need a separate
  discipline);
* **dynamic unbounded data structures** and **probabilistic statements** — out of scope by
  decision. NOT this case: an `arena … max M`, whose ceiling bounds it; its form is sugar over
  `Block`, but the exporter refuses `grow` (`LG005`), so no dynamic-arena program is certified;
* the exporter (`lean_g.rs`) is unverified: that `gE` is the source program is not claimed, and
  every form it drops is in the certificate's "NO FORM in G" ledger (declared `costs`, `reads`,
  deadlines, hold budgets, `traverse` annotations, `by ops`, `mut`, `pub`/`opaque`, `const fn`,
  the hardware around `entry`/`boot`).

## B6. What a green build covers per program (the certificates)

`target/zertifikate/REGISTER.txt` (generated on demand by `cargo test --test zertifikate`, never committed; certificates are elaborated by the Lean guardian stage 5) is THE ONE LIST of the programs under `beispiele/`
(top level and `gift/`) that the checker accepts. Measured now: **34 CERTIFIED, 211 UNCERTIFIED**
(`grep -c` over the file). The cargo test `crates/gabbro-check/tests/zertifikate.rs` recomputes
it from the tree and fails on any byte of difference; `GABBRO_ZERTIFIKATE=schreiben` rewrites it.

* **CERTIFIED**: the byte-exact output of `gabbro obligations --g` is in the build; it decides
  premise (a) *in Lean* for the exported unit (`gCheck … := by decide`) and states the goal
  theorem on it, leaving (b) `NutzerPflichtA gE` as the open hypothesis — the user's part. The
  Rust checker's verdict is not in the chain of reasoning: an exported program the Lean Bool
  refused turns `lake build` red. The register column `chain` says `chain-instance=<name>` where a
  Lean instance of the generic closing theorem for the emitted C exists, `chain=none` elsewhere.
* **UNCERTIFIED**: the exporter refuses the program (first refusal `LG001`–`LG007`). A green build
  says **nothing** about it; the goal theorem reaches it only through a hand-written term
  (`Korpus07`, `Korpus125`).
* A program outside `beispiele/` is covered exactly when its own `gabbro obligations --g` output
  elaborates; nothing checks that this was done.
* The Rust diagnostic codes are premises of nothing here: those mirroring `AkzeptiertSpec` are
  re-decided in Lean for every certified program; the rest guard properties the statement does
  not claim. Of the 216 sentences in the pass register (`gabbro paesse`, 12 passes) none is in
  state PROVED.
* The table and group invariant legs are vacuous for every certified program (the exporter
  writes `Inv := Empty` and refuses `maintains`); the lock legs carry the content there.

The funnel that motivated the register (2026-09-26, 129 top-level corpus programs: accepted by
the checker 129, exported 17, decided in Lean 2, chain closed 2) is the reason it exists: before
it, a green build said nothing for the other 112 and nothing turned red when a program was not
covered.

## B7. Anti-vacuity

A true statement over an empty world is worthless, so it is part of the architecture:
`Zielsatz/Kern/Proben*.lean` and `SpecProben.lean` prove, as theorems, that

* every premise holds JOINTLY on non-degenerate concurrent programs (`gabbro_ziel_zeuge`: two
  active threads, a shared carrier under a lock with a non-trivial invariant, a memory-changing
  run), written as `.gab` and exported — never hand-built;
* probe A (`ensures false` everywhere), probe D (`forever … leave` with `ensures false`),
  a table-invariant breaker, an unsatisfiable lock family and an out-of-range float all
  **violate** (b), and an unguarded shared write violates (a);
* positives: contracts over shared state at a lock boundary and readers in `locks` blocks satisfy
  all premises; `Erfuellbar` asks every declared start to run on some thread, so an empty start
  list no longer satisfies the witnesses;
* the run class is never empty (the idle root meets (d): `laufzeit_ruhe`); what stays in the
  user's hand is named: `E.starts = []`, and an unsatisfiable `E.Q`.

Every new theorem with a ∀-over-syntax premise needs a `_zeuge` on a non-degenerate fixture.
Required axioms: `#print axioms gabbro_ziel` is exactly `propext`, `Classical.choice`,
`Quot.sound` (printed by `grammatik/NachpruefungZiel.lean`; enforced by `instrumente/pruefe-lean.py` (stages 2 and 3), which also checks: no `sorry`, `admit`, `native_decide`, `unsafe`; the one
recorded `axiom`, `dma_inhalt`, is outside the goal's axiom set).

## B8. The Lean map

| Area | Where under `grammatik/Grammatik/` |
|---|---|
| statement, proof, probes | `Zielsatz/Kern/` (`Spec`, `Beweis`, `Akzeptiert`, `Proben*`), `Zielsatz/Atomar/` (the atomic rely, the statement as proved), `Zielsatz/Faeden/` (threads, pools, linking, idle root), `Zielsatz/Eigenschaften/` (invariants, masks, order, weak memory, divergence), `Zielsatz/ZielOrt/` (the per-place machinery) |
| machine G and semantics | `Logik/Ruf/RufMaschineG.lean` (small-step, thread-indexed), `Kern/Semantik/`, `Kern/Syntax/` |
| concurrency, races, locks | `Nebenlaeufigkeit/` (`Rennfreiheit/`, `Sperren/`, `Allgemein/` incl. `FadenMaschine`) |
| weak memory | `Speichermodell/` (`Maschine/MaschineW`, `GXMaschine`, `DRF`, `RMW`, `Sicht`; `Atomar/`) |
| progress, time | `Logik/Fortschritt/` (`KostenG`, `Lebendigkeit`, `Folge`, `Fortschritt`) |
| noninterference | `Nichtinterferenz/` (11 files, ≈4 150 lines) |
| floats, arenas, templates | `Bausteine/Gleitkomma`, `Bausteine/Arena`, `Bausteine/Schablonen` |
| C backend proofs | deleted 2026-10-18 (tag `archiv/c-emitter-2026-10-17`); the reference fixtures and corpus units that sat beside them are `Korpus/` |
| source → model | `Parser/` (the Lean parser, T3), `GabbroV/` (the GabbroV side, see `GABBROV.md`) |
| generated per program | `Zertifikat/` |

The whole tree is about 250 000 lines in 409 files; `Grammatik.lean` imports all of it, and the
Lean build also checks the fifteen theories of the former Isabelle tree (`Isabelle/`). The
`.thy` set in `grammatik/Beweise/` is frozen as a protocol and cross-check
(the retired `pruefe-beweise` ran it with `~/Isabelle2025-2`; not guarded today); **a new proof goes to Lean.**

---

# Part C — Review history

## C1. The protocol

The goal is judged by **two independent verdicts** — one Muse lane, one Opus agent — each
adversarial: nothing is accepted on the strength of a comment or a report. The four questions:
(1) does `Ziel` say the four legs and nothing weaker? (2) is every premise in exactly one of
(a)–(d)? (3) can a user-controlled choice empty an obligation? (4) does machine G run what
the language means? *The axiom list shows that the proof is valid; it says nothing about whether
the statement is the right one.* Two further reading questions decide strength: what `Ziel`
gives that `NutzerPflicht` does not already claim, and whether each `HardwareAnnahme` is really
hardware. After step 1 of the end sequence (AGENTS §1) the checker and emitter work follows.

## C2. Verdicts, one table

| Round / date | Muse verdict | Opus verdict | Found → repaired |
|---|---|---|---|
| 1 — 2026-09-13 | reached for the model, not the implementation | **not reached** | probe A: a false loop invariant makes the conclusion vacuous and (b) ignores it; probes B/C: no contract over shared state at a lock boundary, `locks` readers outside; a cosmetic `e0`; the model's typing stricter than the checker's (held-set equality). → `KeineLogik`, lock-invariant family `SperrInv`, table invariants in the conclusion |
| 2 — 2026-09-14 | reached for the model | **not reached** | probe D: `passes` is free data, a spent `forever` budget is a stop the prover chooses; time is a step bound only. A, B, C now behave. → `passes` universally quantified, deadlock freedom |
| 3 — 2026-09-15 | goal with named gaps | **not the goal yet** | P1 an unsatisfiable lock invariant empties (b) and (d); P2 `ws`/`Q`/`S` free parameters; P3 payload races dropped; `RegLokal` makes a register a constant. → `Einheit`, `StartPflicht`, `Laufzeit`, `Akzeptiert` as one Bool |
| 4 — 2026-09-15b | goal with named gaps | goal with named gaps; one unnamed | F1 an out-of-range float stops as "hardware" for every oracle; F2 deadlock leg only global; F3 stop classes. → `Logik.bereich`, `KeinWarteZyklus`, `HaltArt` |
| 5 — 2026-09-15c | no unnamed gap | unnamed gap | G1: `einpassen` held every sum, float and function-pointer answer to be impossible, so an axiom result of such a type stopped as "hardware" at every call. → decoding of sums, floats, pointers (`EinpassenVoll`) |
| 6 — 2026-09-15d | goal with named gaps, no unnamed gap | the same | one wording defect (W1), repaired: answers at empty types are refused (`antwortenB`, `N310`–`N314`); `nieZurueck` is for `-> never` only |
| Spec-diff reviews — 2026-09-23 | — | F9 clone handoff, F10 pools, F11 `keinKernHalt`: SOUND; F11 overclaimed in its header | one overclaim corrected |
| Spec-diff reviews — 2026-09-26 | — | A (run-time threads), B (weak memory), D (invariants beyond returns), E (linking), G (order leg), H (handlers), O25c (atomic rely): all SOUND; text repairs (B: two assumptions narrowed, D: "at every entry" narrower than worded, `invSicht` nominal, E: a known false accept of `gabbro link` for one-sided threads → OFFEN O28, H: the atomics sibling keeps F11's unconditional form, O25c: the "verbatim" caveat) | header text only; no definition moved after review |
| Reach audit — 2026-09-26 | — | what a green build covers: 177 accepted programs were silently uncovered | the register of B6; certificates in `lake build` |
| Static review of 13 lane groups — 2026-09-21 | — | findings in checker rules, Lean witnesses and claims larger than proofs (degenerate witnesses, a wrong literal found by a theorem written to catch it) | fix lanes F1–F11; the goal-relevant ones are F9/F10/F11 above |

The current standing is therefore: *the goal with named gaps — no unnamed gap found (round 6),
extended by seven reviewed diffs.* No external human review of the B2 package has happened yet;
it is the first point where an outside reader gets a lever on a few hundred lines instead of
the whole tree.

---

# Part D — Extension rules, noninterference, user logic

## D1. Rules for extending the goal

* **The criterion is counted per OBLIGATION, not per feature.** An extension stays in the
  carried fragment only if the checker discharges its premises; `gabbro obligations` before and
  after is the measure, on the extension's examples and on the corpus. *The first extension this
  rule refused:* a product/record former in `Ty` (so that `impl fn … -> Completion` can travel)
  generated zero obligations on the corpus — sieve (b) stayed 15 of 113 with every refusal
  skipped — and its price was the re-proof of every leg. Named absence OFFEN O15, closed as
  priced and rejected.
* **One assumption list**: lock primitives, thread creation, the idle root, the scheduler class
  for noninterference, the IEEE unit, device answers, the compiler. `Spec.lean`'s header is the
  one place that lists them.
* **Liveness**: `wartezeit_schranke` (`Logik/Fortschritt/Lebendigkeit.lean`) bounds a lock wait
  under `LaufzeitAnnahme` (FIFO plus a fairness window `F`) and `HardwareImAbschnitt`; the hold
  time is a premise. Flat locks give `(c−1)(held+1)+1` own steps of the waiter; nested locks
  blow up multiplicatively over rank levels (a depth-4 chain 1.6·10⁹ own steps at `c = F = 64`),
  shrunk by dominance and by non-preemptible sections. It is not in `Ziel`, and a green theorem
  over a number nobody can put in a data sheet is not counted as a result.
* **Higher-order contracts**: refinement is contravariant in `requires`, covariant in `ensures`
  (the wrong direction needs a poison probe); a pointer type carries `effects` and `costs`;
  closures over the call graph join over all admissible candidates (`KandOk`).

## D2. Gaps named by external review (2026-09-14) and their routes

| Gap | Route / status |
|---|---|
| Fixed-width arithmetic (`x & (x-1)`, CRC, alignment) | oracle plus certificate: `bv_decide` carries exactly one named axiom per proof (`verifyBVExpr … = true`); decision: list each by name in the one assumption list. Not built into the user path |
| Counterexamples for handed-over obligations | `gabbro counterexample`: search outside the trusted base, every hit confirmed by running it through the exported semantics; "none found" is never a proof |
| Linearizability of lock-free structures | the language names linearization points; one INTERNAL point per operation per path (excludes Michael–Scott and helping, and must say so). Not started |
| Real time (WCET) | a named interface with proven inputs: flow facts (loop bounds, paths, call graph, deadlines) as a certificate; the processor timing model is a named assumption. Not built |
| Unbounded nonlinear arithmetic | stays user logic; no certificate standard exists |
| Annotation burden | infer, then check: `effects` and `costs` are computed (`gabbro abgeleitet`); every inferred annotation is checked like a written one |
| Timing channels | constant-time discipline as an extension of the flow rule (Part C-style); not built |
| Linking, inline assembly, source trust (homoglyph/bidi), float accuracy, checker robustness, adoption | linking is a theorem since 2026-09-26 (B3); assembly is an assumption (`AxCorr`); the lexer refuses bidi controls; termination of every pass is not a registered sentence; the people problem is a tutorial path |

## D3. Noninterference — isolation as a theorem over machine G

Lean `Nichtinterferenz/` (11 files, ≈4 150 lines, standard axioms). **Proved:** for every
program passing the decidable flow condition `flussB`, every observer domain `B`, and every two
runs of G under the same schedule from start memories that agree on what `B` may see, `B` sees
the same at every step (`nichtinterferenz`). A scheduler is admitted if its choice depends only
on what `B` sees (`nichtinterferenz_planer`); the fixed-timetable partition scheduler is the
instance (`nichtinterferenz_zeitplan`). The metatheorem is proved once over all rules of
machine G (74 as counted in `SchrittTreu.lean`); the program supplies its premises by a check.
It is a hyperproperty over pairs of runs and cannot come out of per-run contracts.

**Model.** A policy `darf` (reflexive, transitive); labels on every carrier (tables, globals,
device carriers, lock-invariant carriers), every axiom and every entry root; a thread has its
root's domain. The observation of `B` is the memory of every carrier that may flow to `B` plus
the ghost-free state of every thread that may. Unwinding conditions: local respect, step
consistency, output consistency. Possibilistic and schedule-parametric.

**The flow rule `flussB`** (thread-granular): for every labelled root of domain `d` and every
function its call graph reaches, every carrier read has a label that may flow to `d`, every
write frame a label `d` may flow to, every foreign call is labelled below `d`, and no thread
starts at an unlabelled root of a multi-domain program. Explicit and implicit flows both need a
thread that reads `A` and writes `B`-observable data, so both fall. A statement-level rule
(program-counter labels) would admit a dispatcher serving two domains; its proof is not built —
until then one thread, one domain.

**Not covered:** timing and every physical channel; schedulers that look at more than `B`'s
observation (round-robin over runnable threads, load balancing, a timetable that skips a blocked
slot); enabledness (a scheduled thread that cannot step; locks shared across incomparable
domains, proposed checker code `I005`); declassification (only its statement exists:
`FreigabeNI`, delimited release; plain NI implies it, and with nothing released it is plain NI);
device output; everything below machine G.

**The sentence that is TRUE** (every sentence about isolation carries the scheduler class, the
timing exclusion and the level, or it is not written): *if a program is accepted by the checker
with domain labels, and runs on a runtime whose scheduler hands out slices by a fixed timetable
(or any rule that looks only at `B`'s state), a blocked slot left idle, then nothing in tenant
A's data changes what tenant B's threads compute or what B's memory holds, step for step — for
machine G, under: every foreign function and driver writes only what it declares, device
registers answer only from declared device state, every foreign function `B` may call acts only
on data `B` may see.* False and not to be written: "A learns nothing about B on a load-balanced
machine"; "as good as VMs including side channels"; "proved down to the binary"; "any Gabbro
program is isolated" (only labelled, checked ones); "tenants cannot interfere through shared
data" (a structure written by two tenants is *refused*, not made safe).

**Status of the language surface: not built.** The surface (`domain`, `flows`, labels on tables,
devices, roots) and the checker rules `I001`–`I004` are a proposal; no checker code issues them
(`grep` over `crates/` is empty). The theorem is Lean-side only. Corpus measurement, by `decide`
in `Nichtinterferenz/Korpus.lean`: of six multi-root programs, 108 is admitted, 104, 118 and 124
are refused for every label (a carrier written by two roots is interference in the theorem's
sense even where no data flows); one labelling with an auditor domain above both tenants admits
124 (`n124_zeuge`).

**Premises, counted:** `flussB` is checker-decidable from labels; the enumerations are
exporter facts; the hardware entries (`GutO`, `RegLokal`, `OrakelTreu`) and the scheduler class
are named assumptions; **user logic: none** — a program need not be verified to be isolated,
only labelled and checked. For the C line (deleted 2026-10-18, tag `archiv/c-emitter-2026-10-17`): the ticket lock was proved to be the
abstract lock (exclusion, FIFO), but the old entry "reveals only held or free" was **false** of it
(a waiter can measure its queue position), and "release only one's own" is a checker guarantee,
not a runtime one. Carrying a *pair* of runs to C needed two facts not proved. Comparison with
seL4's confidentiality proof: seL4 proves one kernel for a static schedule; here the metatheorem
holds for every program of the language over G, and does not reach the code.

## D4. User logic, obligations, and the channels to Lean

The user's own logic reaches Lean by two channels with different objects — they are regularly
confused:

| | Channel A | Channel B |
|---|---|---|
| command | `gabbro obligations --lean` (`--isabelle`, `--g`) | `gabbro lean a.gab b.gab` |
| says | Gabbro's own `ensures`/`requires` as duties | a Lean specification written **by hand** |
| good for | measuring how much the language says about itself; the generated duty files (`gabbro prove`) | frame properties with quantifiers ("clearing touches no other compartment") that a `spec fn` cannot state |
| guardian | `gabbro prove`, run by `instrumente/pruefe-gabbrov.py` | `instrumente/pruefe-gabbrov.py` (the retired `pruefe-lean-pflichten`, `-beweis` and `-programm` are not guarded today) |

`gabbro obligations --g` is the channel the goal theorem uses: it writes the unit as a G program
with the flagship's per-function duties (`KoerperGutS` + `InvGutS`) stated. Where the Lean parser
elaborates a unit (`lowerAllg`), the duty files of GabbroV *derive* (b) (`bruecke_nutzer`,
`bruecke_nutzerA`), given decided name and rank conditions — a parser fragment only (corpus
programs 104 and 108 at the time of the bridge); every other unit still carries (b) as an
assumption. See [`GABBROV.md`](GABBROV.md).

**Obligation tally.** The retired `PFLICHTEN` register and `zaehle-pflichten` (booked 2026-09, historical):
239 obligations over the ten fragments = 173 K (plumbing) + 66 L (logic); three `progress`
rows are assumptions with a falsifier, not obligations, so GabbroV's population is 63. K and L
are by the criterion of A1 (the machine against the subject), not "obligation against
assumption"; a discharged obligation still counts.

**The own-logic remainder (`hFree`).** A contract clause over a lock-shared carrier that is *not*
in invariant form still owes the per-run preservation proof over every foreign step. The checker
rule `D027` refuses such clauses in contract position of a shared-side function (the clause
restates instead of naming the invariant). What stays owed, as user logic outside contract
position: loop invariants over shared carriers, `spec fn` bodies, and clauses of functions
without a shared side, where they leave invariant form. A checker that refused every such shape
would refuse programs, not discharge them.

**The proposal "the user's logic, stated in Gabbro, checked by Lean" (not built).** Four verdicts
instead of two — `CARRIED` (a pass already establishes it), `DECIDED` (evaluated over a bounded
domain, certificate checked in Lean), `ORACLE` (a solver as untrusted oracle, certificate checked
in Lean), `OPEN` (handed to the person) — a report without any percentage (claims by verdict,
unclaimed slots counted from the *program*, inert claims), and mutation of the body to find claims
no mutation falsifies and mutations no claim catches. The sentence it rests on: *every verdict
other than `open` cites a Lean-checked artefact.* Not built: there is no `changes only`,
`never`/`always` form in `dokumente/SYNTAX.md` and no mutation run over the user's logic (`mutiere-nutzerlogik` was never built).
It must not infer `ensures`, and it removes Lean from the user's desk, not from the chain.

**Independence of the verification path (a plan, partly built).** A verifier that only
verifies what the checker already accepted verifies the wrong thing: the export must not depend
on the checker's verdict. Required: break the refusal list into language gaps and checker
knowledge; turn the 93 `foreign-body` refusals into 93 named assumptions (a contract is a
**hypothesis**, never an axiom); write the trusted base down (parser, export, the `Body`
semantics, the Lean kernel — not the passes); witness pairs for the export's fidelity; the
guardians inside the acceptance run. Built: `gabbro gabbrov pruefe` and the `Bruecke` of
`GABBROV.md`.

---

# Part E — Trust base and the lowering

## E1. What is trusted, by layer

| Layer | State |
|---|---|
| Lean kernel | external; every goal-theorem result uses the three standard axioms |
| The statement | reviewed (Part C); `Spec.lean` header is the list of what is assumed |
| The Rust checker | unverified. For a certified program its verdict is not in the chain (B6); for the rest, **the emitter and checker are trusted** |
| The exporter `lean_g.rs` | unverified; every dropped form is named per certificate; `gabbro corr-lean` and `gabbro certificate` print what a translation rests on |
| The emitter / lowering | trusted until the validation chain is closed; about 19 600 lines of Rust in `emit.rs` alone, and failures there are silent below every pass (see below) |
| Generator templates | `gabbro schablonen`: 41 entries, 30 machine-checked, 11 unproved, 3 of those CARRIED (the compiler rests on them), 6 premises without a pass (tooth 3); base mark 18 plus one seat per proved template; an entry leaves only proved or with its construct |
| Hardware | the named assumptions of B4 |

**The emitter's failure record** is part of the trust claim: `breite_von` once answered "8 bytes"
for any integer word it did not know, so a ninth word would write a wrong-width access onto a
device register — checker clean, `cc -Werror` clean. It is a total table now (`C001` otherwise).
A second case: a device table keyed by the bare name silently gave two same-named devices in
two modules the second one's offsets (now refused). Both are "a table whose key is narrower than
the distinction it is keyed on". The structurally different answer is the **certificate**: a
certificate that vouches for two different programs vouches for neither, and injectivity is
tested (`zeugnis_injektiv.rs`: nine traversal domains pairwise distinct). An injective
certificate is not a proof.

**The one emission rule (W6):** omitting a runtime check is justified by M1 (the range types)
alone, never by an invariant — the net that hangs on the type is recomputed per program; an
invariant hangs on a template.

## E2. The route to the machine

*Backend truth (2026-10-17).* The LLVM backend is current (`gabbro llvm`, `gabbro llvm-cert`,
see `LLVM-BACKEND.md`); the C11 emitter was removed (2026-10-17, final). The target-level proof — source → model → machine code of AArch64 or x86-64 — needs a
complete Lean model of the CPU and the per-access bridge from the target's memory model to W/GX
(`PLAN-TRANSLATION-VALIDATION.md`, `TODO.md` §5); it is not started and nothing here claims
it. The C-level proofs (`CBackend/`, the chain instances for 104 and 108, `LaufzeitC`) were deleted
on 2026-10-18 with the C backend; they live in the tag `archiv/c-emitter-2026-10-17`. The retired `zaehle-kette`
counted closed chains and the retired `pruefe-cformen` classified every emitted C form as lemma /
assumption / uncovered (at the 2026-09-26 audit: 51 / 4 / 27); both measured the removed C line.

## Item 2 — which C (legacy C lowering)

seL4 formalises C; Gabbro emits so little C that its semantics is a *finite table*. The sections
below keep the former numbering (§1–§5); code comments cite them as `PROOF.md §N`.

### §1. The target language is a closed list of forms

The emitter writes one C form per construct. Allowed: declarations (`static`, `extern`,
struct/union definitions, constants), types (`uint{8,16,32,64}_t`, `int…_t`, `_Bool`, `T*`,
`T[N]`, struct, union), statements (assignment, `if/else`, exhaustive `switch`, a counting
`for` loop, `return`, `goto` only as a generated loop exit, call), expressions (literal,
identifier, field, index, unary `!`/`-`, binary arithmetic/bit/compare operators, call, explicit
cast), plus `volatile`, `_Atomic` with a named order, `_Noreturn`, `restrict` (priced, off by
default), inline assembler at the named emission sites. **Never emitted:** preprocessor other
than `#if` out of `when`; `void*`; pointer arithmetic; union reinterpretation without a tag; the
comma operator; assignment in an expression; `?:`; implicit conversion; variadics; `longjmp`;
VLA; bit-fields.

The list is counted by a lexer, not by `grep` (by the retired `zaehle-c-formen`; the generated C
explains itself in English, and `for` appears 73 times as a word and 49 times as a statement),
and was ratcheted. First measured 2026-08-31 over 102 emitting units (8 001 lines of C):

| Set | Forms |
|---|---:|
| **A** allowed and used (derived: total minus C) | 35 |
| **C** used and not allowed (7 on the never list, 19 on neither, the rest under a generous reading) | **32** |
| **Forms in the emitted C** | **67** |

*Figures are the marks of the retired `zaehle-c-formen` (`MARKE_TABELLE = 67`, `MARKE_UNERLAUBT = 32`; historical, legacy C backend).
The first measurement, 2026-08-31, read 64 = 34 + 30; set B, allowed and never used, had 6
dead entries then. A rise of a mark needs its reason written in the instrument.*

The result is not the one the section assumed: the table stayed small because Gabbro is small,
not because the list was obeyed, and thirty forms were never decided — pointer arithmetic at
491 sites, `void` as a type at 930. Two rulings stand: `?:` is wrong in the generator
(`if (v > z) { z = v; }` costs 0 instructions at `-O2`), and `__builtin_unreachable` was
wrong at four of five sites (a `return 0;` directly under it contradicts it); the fifth is a
proof export into C's UB rules and is named as such. A second instrument over the 101 compiling
units (`-Wconversion -Wsign-conversion -Wcast-qual -Wvla -Wdouble-promotion -Wfloat-equal`)
finds zero hits.

### §1a. Where the instrument's headline was recorded

The retired `zaehle-c-formen` (2026-10-17, see git history) read two cells of this document, the rows
"**Forms in the emitted C**" and "**C**" of the table above. No guardian reads them now; the table is a
dated record of the legacy C backend.

### §2. The UB inventory — what kills each class

The proofs live in Gabbro; the danger is that the *emission* devalues them through C's own rules.

| # | UB class in C | Dies through | Residual risk |
|---|---|---|---|
| 1 | signed overflow | M1 proves the bound but C does not know it: unsigned types, otherwise `-fwrapv` | none if both stand |
| 2 | out-of-bounds access | M1/M4 in the source type; pointer arithmetic — see §1 | the 491 sites of §1 are an open ruling |
| 3 | division by zero | the denominator range excludes 0 | none |
| 4 | shift by ≥ width | M1 bounds the amount | none |
| 5 | strict aliasing | no cast between pointer types is emitted; `-fno-strict-aliasing` | none |
| 6 | evaluation order | assignment is not an expression; one effect per statement | none |
| 7 | implicit conversion | explicit casts everywhere; checked mechanically (`-Wconversion`) | none, zero hits measured |
| 8 | uninitialised read | nothing implicit; every declaration has a value | none |
| 9 | null pointer | no `null` in the language; an immutable pointer starting at `0` is refused (`N260`) | a `static mut` pointer starting at `0` (the NULL-initialised global idiom), and the `extern` boundary |
| 10 | union reinterpretation | `tagged` reads and writes via the tag | padding bytes are never read |
| 11 | wrong `restrict` | generated from `effects` — a real proof export into C | named; off by default, priced where a benchmark demands it |
| 12 | `volatile` semantics | weakly specified | an axiom, named |

Row 9 was right about the language and wrong about the product: a cast to `uintptr_t` is *still*
a null pointer constant when the value is `0`, so the first cure (2026-09-02) was spelling, not
cure; the verdict is the checker's (`N260`, gift 931), because no non-null C spelling of
address 0 exists.

### §3. The compiler options are part of the artefact

`-std=c11 -ffreestanding -fno-builtin -fwrapv -fno-strict-aliasing
-fno-delete-null-pointer-checks -fno-common -fno-stack-protector`, bound to a fingerprint next to
the assumption list. A lowering whose validity hangs on options nobody records is a promise about
somebody else's machine. Open: fail closed — a generated preamble that breaks when the options
differ.

### §4. The lowering as a statement: the coverage certificate

"Syntax-directed and non-optimising" becomes checkable as a bijection between evaluation sites,
which works only because assignment is not an expression and nothing is implicit. The emitter
writes a coverage certificate per run (site → C site, form, rule); an independent recomputer
with its own form table checks completeness, order, closure and no-extra-effect. **Cut C1** is
that recomputer's contract (`corrcert.rs`; the Lean side `CorrSite`, `vollB_sound`,
`korrespondenz_sound`). What is accepted is the mutation list, not the checker's existence. The
common-mode failure is named: both tables come from one specification text; the executable
witness pairs (a Gabbro fragment, expected C, expected behaviour, run through the real compiler)
are the only thing that measures against the compiler instead of a second reading.

### §5. What that achieves, and what not

Achieved: the target language is named and closed (so the correspondence is formulable at all),
ten of twelve UB classes die on existing rules, the lowering is recomputed per run, binary
validation stays possible. **Not achieved:** a formal C semantics. Structure does not imply
meaning; the table *Gabbro operation → C operation → condition* is hand-trusted, and
`restrict`/`volatile` remain trust.

## E3. The value thesis, shifted (measured, with search paths in the former document)

The founding assumption was the parser; the evidence says the language justifies itself at the
**kernel**, not at the parser. `format` earned brevity, not safety: 5 formats in 53 days with 0
errors of the class, and the only core parser that reads foreign bytes (**B40**, the DTB
fragment, 145 lines) already checks every access (`be32(data, n)?` is "check, otherwise
refuse"). Eight constructs carried evidence from the kernel side (`table … count`,
`lock … rank … held`, `locks shared` — 33 reads against 44 writes —, pairing, `walk`/`embeds`,
`BootPhase` — 7 sites against a gate of 5 —, M1 overflow, `traverse` — 0 of 571 loops over
something that is not a domain). The second number a dashboard needs: not only writing cost
(the ratio) but proof cost per change — W (value-statement) obligations per thousand lines, a
lower bound. A `format` is no longer the justification of the language, one of its conveniences.

## E4. Re-measuring

| Figure | Command |
|---|---|
| goal theorem and its axioms | `cd grammatik && lake build && lake env lean NachpruefungZiel.lean` |
| certificates and the register | `cargo test --test zertifikate -- --nocapture` (prints the totals); `instrumente/pruefe-lean.py` stage 5 |
| templates | `gabbro schablonen` |
| pass sentences | `gabbro paesse`, `gabbro paesse --per-statement` |
| emitted-C forms, closed chains, C-form classification | retired (`zaehle-c-formen`, `zaehle-kette`, `pruefe-cformen`; 2026-10-17, see git history); historical, not guarded today |
| obligation population | `gabbro pflichten <file.gab>` per file (the retired `zaehle-pflichten` summed it) |
| no `sorry`/`axiom` | `./instrumente/pruefe-lean.py` |
| whole acceptance | `./instrumente/abnahme.py` (the four guardians) |

**Not re-measured in this consolidation** (no `lake` or `cargo` run was allowed): the axiom set
of `gabbro_ziel`, the build state of every Lean file named above, the REGISTER regeneration, the
counts of the former August measurements (axiom counts, Caprock figures), and the emitted-C
marks beyond what the instrument's source records.

---

## Appendix — old → new ids

| Cited as | Now |
|---|---|
| `PROOF.md §1`, `§1a`, `§2` (row 7 = implicit conversion, row 9 = null pointer), `§3`, "Item 2" | unchanged, under "Item 2 — which C" |
| `PROOF.md` "cut C1", the recomputer | Item 2 §4 |
| `PROOF.md` "B40" | E3 |
| `PROOF.md` "own-logic debt", the `hFree` remainder | D4 |
| `PROOF.md` line numbers (`:107`, `:1078`) | dead; they pointed into the former text |
| `dokumente/PROOF.md` §2 (the statement), §4 (anti-vacuity), §5 (review package, the four questions), §6 (not claimed) | B1, B7, C1 and the `Spec.lean` header, B5 |
| `dokumente/PROOF.md` §8 (extension rules, liveness) | D1 |
| `dokumente/PROOF.md` §9, §10 (further gaps; linking; `counterexample`) | D2 and B3 |
| `dokumente/PROOF.md` §3, §7.4, §8, §9, §10 (the runtime list `LaufzeitC`) | D3 |
| `dokumente/PROOF.md` §2.3, §3 | D4 (independence of the path) and `GABBROV.md` |
| `dokumente/PROOF.md` | D4 (the proposal) |
| `dokumente/PROOF.md` | B6 |
| the retired `TRAEGER-UND-HARDWARE` register | the A7 / `hardware A, D;` decision in B4; its `H101` half belongs to the checker document |
