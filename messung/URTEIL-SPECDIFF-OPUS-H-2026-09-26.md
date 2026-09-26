# Verdict — the Spec diff of Opus agent H (OFFEN O19: handlers in the unit, the leg `KernHaltE`)

*Independent adversarial review, 2026-09-26. Branch `worktree-agent-a75fdc081ae4ed9bf`, head
`6da58e8d` (contains master `1683d0f7`; master has not moved since). Report
`messung/OPUS-H-KERNE.md`. Measured in the worktree through the queued wrappers only
(`./lean-bau`, `./lean-probe`, `./cargo-pruef`, `./emission-pruef`). Text fixes committed
separately (Spec header comment and OFFEN O19 only; no definition or proof touched). Nothing
merged into master, nothing pushed.*

## 0. Verdicts at a glance

| Question | Verdict |
|---|---|
| (1) Is (a) a restriction, and is it stated? | **Yes, stated, and harmless on every unit of before.** The new component `masken` refuses exactly programs with `P.unterbricht w = true` whose `reachB` graph takes a lock not declared `masks irqs`. Since the field defaults to `fun _ => false`, `maskenB_ohne` makes it `true` on every earlier program. Embedding lemmas correct (§1). Wording "exactly the programs `H102` refuses" slightly too strong: **F1, fixed** |
| (2) Is `KernHaltE` contentful, and is `KernPlan` satisfiable? | **Yes to both** (§2). `kernHaltE_verletzt` is a real 3-step run from the runtime start of the refused unit `kEv`, admitted by `KernPlan` on one core, at which the leg is false. `masken_zeuge` satisfies `KernPlan` on a real preemption of `beispiele/59` and applies the leg obtained from `korpus59_ziel` |
| (3) Handlers in `Programm` rather than `Einheit` | **Sound** (§3). `HandlerVon` reads the start machine, so `Ziel` needs no new parameter. The link demands one dispatch fact (`Verbindbar.unterbricht`), and the composed hull is re-decided (`SchnittstelleSpec.masken`). The correspondence to the source is an exporter fact pinned by K6, the same trust as every other exported field. Two adequacy notes: **F3** (a handler that is never started) is now stated in the header; **F4** is a note only |
| (4) "Holds for every core assignment" | **Stronger, not vacuous** (§4). The `∀ kern` includes the one-core assignment that the witnesses use. Assignments that separate the threads make the conclusion trivial, which is correct |
| (5) Named assumptions / NOT CLAIMED | **Complete for `gabbro_ziel`**: no `cli`/`sti` in the C, no re-entry, no handler-on-handler preemption, IPI without `via idt`, undeclared locks. **One omission, F2, fixed in the text:** the shared-atomics statement `gabbro_ziel_atomar` keeps F11's unconditional `KernHaltGA`, and `AkzeptiertX` has no handler component |
| (6) Build and axioms | **Green.** `./lean-bau`: exit 0, 0 error lines, 347 jobs. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `gabbro_ziel`, `gabbro_ziel_verbund`, `kernHaltE_aus`, `kernHaltE_verletzt` and `masken_zeuge`. No `sorry`, `admit`, `native_decide` or `axiom` in the diff (the three grep hits are English prose: "admit", "axiom whose result") |

**Verdict: SOUND** (F1–F3 are text fixes, committed; F4 is a note). The leg F11 made
unconditional (URTEIL-SPECDIFF-2026-09-23, F1) is now carried by (a), for `gabbro_ziel` and
`gabbro_ziel_verbund`, but not for the atomics sibling.

## 1. (a): the new component, and the embedding

* `AkzeptiertSpec.masken : MaskenDisziplin P fs` is defined as
  `∀ w, P.unterbricht w → ∀ f, reachB P fs w f → mE (NurMaskiert D) (P.rumpf f)`.
  `NurMaskiert` admits every call and every signature, and only `D.maskiert` locks. In `mS` the
  only constructor that takes a lock is `.locks` (read in `mS_und`), so the component judges
  exactly the `locks` statements of the graph. `maskenB_iff` is exact, given a complete member
  list.
* **Which accepted units are now refused.** Exactly those with a declared handler whose graph
  reaches an unmasked `locks`. No unit of before can be one, because the field did not exist
  and its default is `false` (`maskenB_ohne`). On the Rust side such a program is refused by
  `H102` and therefore never exported, *up to* the two differences F1 names.
* **Embedding.** `akzeptiert_nodup_gleich`: `Akzeptiert = AkzeptiertVor && maskenB`. Together
  with `maskenB_ohne` this gives "no-handler units keep their verdict". `kernHaltE_ohne_handler`
  proves the leg outright when there is no handler, so those units also keep their conclusion.
  `akzeptiert_vor_neu`, `akzeptiertSpecVor_neu` and `pruefer_vor_neu` take or conjoin the new
  component, and that is correct: an old checker never judged it. The claim "no-handler units
  keep verdict and conclusion" holds as stated.
* **F1 (wording, fixed).** The header said (a) is tighter "exactly on … the programs the Rust
  `H102` refuses". The Rust rule reads the effect hull, which fires on presence but may miss a
  lock behind a cut edge, and it skips locks its unit does not declare. The Lean component reads
  the full `reachB` graph over declared locks. The two agree where measured
  (`pruefe-akzeptiert-diff.py`: 24 units, K6, and the self-test flip of 59 that reproduces gift
  460). Neither inclusion is proved. Spec header and OFFEN O19 now say so.

## 2. Is the leg contentful, and is `KernPlan` realisable?

* **`KernHaltE`** quantifies over every `kern`, every `LaufG` run from `M0` to `M` with
  `KernPlan kern (HandlerVon P M0)`, and a handler `g` with another thread `f` on its core:
  `AnSperre M g L → L ∉ offen (M.faeden f).spur`. The handler set is no longer a parameter; it
  is read off `P` at the start machine. In `ziel_aus`, `M0` is `RufStartG P.mitRuhe sp init`
  (`kernHaltE_aus … sp init M`), and the idle root `none` is never a handler (`mitRuhe`).
* **`kernHaltE_verletzt`, read in full.** `kPv` is example 59 with the handler body replaced by
  `locks RING { }`, and `kEv` is the matching unit, whose `Laufzeit` holds. The run is: thread 1
  unfolds, thread 1 takes `RING`, thread 0 (the handler) steps to `locks RING`.
  * The schedule is `fs = 1, 1, 0` with `kern = fun _ => 0`.
  * `KernPlan` clause 1 holds: at the handler's first step, thread 1 holds only `RING`, which is
    unmasked.
  * `KernPlan` clause 2 holds: after the handler's entry, only the handler steps.
  * The leg's conclusion fails, because `RING` is held by thread 1 and the handler stands at it.

  So the leg is **false on a reachable machine of a real runtime start**. It is not a theorem of
  G, and `ziel_aus` has to discharge it from (a) (`kernHaltE_aus` uses `hA.abg` and
  `hA.masken`). `handler_abgelehnt` and `kPv_ohne_handler` (by `decide`) show that the handler
  component alone separates the shape. (b) and (c) are not claimed for `kEv`, and they need not
  be: the question is whether the conjunct has content, not whether `kEv` is a counterexample to
  `GabbroZiel`.
* **`KernPlan` is not vacuous.** `masken_zeuge` builds an admitted one-core run on the accepted
  example 59 with a real preemption: `RING` is held while the handler enters and stands at
  `locks TAKT`. It then applies `hZiel.keinKernHalt` obtained from `korpus59_ziel`, with no
  hand-supplied graph, feature set or discipline. The only other way to meet `KernPlan`, runs
  with no handler step at all, also satisfies it, and that is correct.

## 3. Handlers in `Programm`

* `Ziel` reads `P`, `M0` and `M` only, so `HandlerVon P M0` needs no new parameter.
  `Programm.mitRuhe` carries the field. `mitRumpf` (`{ P with rumpf := r }`) carries it too, and
  `p2_eq` now rewrites with `hV.unterbricht`.
* **Source agreement.** A unit whose `unterbricht` understates the source would get a leg about
  fewer threads. That trust sits in the exporter (`lean_g.rs` collects `via idt` with the same
  test as `Kontext::unterbricht`) and is pinned by the diff script's K6. It is the same class as
  every other exported field (`maskiert`, `starts`), not a new gap.
* **F3 (fixed in the text).** The leg speaks about threads. A function marked `unterbricht` that
  no declared start runs is checked by (a) but occurs in no G run. The exporter starts every
  dispatch root (`wurzeln`, lane 198), so this does not arise for exported units. It is now one
  sentence in the header.
* **Linking.** `Verbindbar.unterbricht : E₁.P.unterbricht = E₂.P.unterbricht` gives one dispatch
  fact for the link declaration, like one contract. `verbindeP` inherits `E₁`'s.
  `SchnittstelleSpec.masken` re-decides the discipline over the composed hull (`HuelleV`), and
  `akzeptiertSpec_verbinde` uses exactly it. `schnittstelleB_iff` is extended and exact. The
  Rust link check runs every pass on the linked program (`verbund.rs` header), so `H102`
  applies there too.
* **F4 (note, no change).** A unit exported ALONE names only its own handlers. A future Lean link
  export must therefore write the union into both units, or `Verbindbar` fails for any pair in
  which only one side has a handler. No link export exists today; the link witnesses are
  hand-built with the default.

## 4. "Every core assignment"

`∀ kern` sits inside the leg, so it is at least as strong as any fixed assignment. It is not
vacuous: the one-core assignment is in range, and both witnesses use it. No pinning is claimed,
and OFFEN O19 says which core a thread runs on is no fact of the unit.

## 5. Named assumptions and NOT CLAIMED

The header's NOT CLAIMED hunk names:

* `KernPlan` as the hardware assumption inside the leg;
* no `cli`/`sti` in the emitted C, so translation validation has nothing to relate `KernPlan` to;
* no re-entry and no handler-on-handler preemption (a handler thread runs once in G, and
  `KernPlan` lets nothing else of the core step while it runs);
* an IPI without `via idt` (`beispiele/57`);
* undeclared locks.

All of these are true of the definitions. **F2 (omission, fixed in the text):**
`ZielAtomar.keinKernHalt : KernHaltGA` (`AtomarAkzeptiert.lean`) is still F11's form, which is
proved for every program (`kernHaltGA_gilt`), and `AkzeptiertX` has no `masken`.
`gabbro_ziel_atomar` therefore still has the vacuous conjunct that URTEIL-SPECDIFF-2026-09-23
found. It is not weakened by this branch, only not reached. OFFEN O19 and the Spec handler block
now say so.

## 6. Build evidence (this review)

| Measurement | Result |
|---|---|
| `./lean-bau` at `6da58e8d` | exit 0, 0 error lines, 347 jobs |
| `./lean-probe` `#print axioms` | `gabbro_ziel`, `gabbro_ziel_verbund`, `kernHaltE_aus`, `kernHaltE_verletzt`, `masken_zeuge`: `[propext, Classical.choice, Quot.sound]`; `handler_abgelehnt`, `maskenB_iff`: `[propext, Quot.sound]` |
| `./cargo-pruef` | exit 0; 1401 passed, 0 failed, 1 ignored |
| `./emission-pruef` | exit 0, `ALL PASS -- 51 durchgestochen, 311 von 311 uebersetzen, 2 umgekehrte Probe(n)`; no MARKE mismatch; ASan stage 6b NOT run on this machine (named by the script, not a pass) |
| `./lean-bau` after the text fixes (Spec header comment) | exit 0, 0 error lines, 347 jobs |

## 7. Part 2 (merge preparation)

Master was still `1683d0f7`, which the branch contains, so no merge was needed: no conflict, and
certificates not regenerated (this review changes no Lean definition and no exporter code).
`./lean-bau`, `./cargo-pruef` and `./emission-pruef` are green as in §6. Ready for
`opus-merge.sh`.
