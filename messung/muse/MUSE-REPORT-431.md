# MUSE-REPORT-431: Continuous Lean proof reserve — ValidationBudget

Lane 431, branch `muse/431`, clone `/home/simon/Dokumente/gabbro-muse/a431`.
Task: prove generic fail-closed fuel/resource-limited decode/validation
traversal facts over the actual canonical decoder and bytes.

## What was done

`grammatik/Grammatik/X86/ValidationBudget.lean` (new module, 487 lines;
`import Grammatik.X86.ValidationBudget` already at the end of
`grammatik/Grammatik.lean` from the skeleton commit; no other file touched):

- Defs (skeleton, kept): `decodeFuel` (fuel-bounded traversal over
  `Codec.decode` with the `laenge + rest.length == bs.length` and
  `laengeOk` runtime gates), `validAllFuel` (accepts only on empty rest),
  `entriesOkFuel` (fuel-bounded per-entry check), plus new
  `bildEintraegeOkFuel` (entry check instantiated with the canonical
  `Bild.eintragEnthalten` — same check `wohlgeformt` uses, no second register).
- §1 fail-closed base: `decodeFuel_zero`, `decodeFuel_nil_succ`,
  `validAllFuel_zero`, `decodeFuel_step_refusal`.
- §2 full acceptance: `validAllFuel_none` (exhaustion refuses),
  `validAllFuel_some_empty` (acceptance is full consumption),
  `validAllFuel_rest` (leftover bytes never validate),
  `decodeFuel_cons_eq` (definitional one-step unfolding, `rfl`),
  `decodeFuel_ins_le_fuel` (actually-derived bound `ins.length ≤ fuel`),
  `decodeFuel_mono_succ` + `validAllFuel_mono_succ` (more fuel preserves
  acceptance; raising the budget never revokes a result).
- §3 entries: `entriesOkFuel_cons_eq`, `entriesOkFuel_zero_cons`
  (both `rfl`), `entriesOkFuel_head_fail`, `entriesOkFuel_true_head_tail`
  (head AND tail checked, rest never bypassed), `entriesOkFuel_length_le`
  (`es.length ≤ fuel`), `entriesOkFuel_succ_step`, `entriesOkFuel_mono`.
- §4 image entries: `bildEintraegeOkFuel_zero_cons` (`rfl`),
  `bildEintraegeOkFuel_head_tail`, `bildEintraegeOkFuel_all` (every
  accepted entry is canonically contained in an executable section).
- §5 witnesses over REAL artefacts: `wit_decode_ret`, `wit_valid_ret`
  (canonical `ret` byte under fuel 2), `wit_timeout_refuses` (fuel 1
  refuses what needs fuel 2), `wit_unknown_refuses` (`0xFF` refused),
  `wit_two_rets_fuel` (fuel 2 refuses two `ret`s, fuel 3 accepts —
  no leftover bypass), `wit_entries_image` (`0x1000` contained,
  `0x5000` refused in the real witness image),
  `joint_decode_entry_memory` (decode acceptance + entry acceptance +
  a real memory-changing write/read, reusing `Bild.schreibLese_zeuge`,
  no second memory model).
- `CUTS:` block plus `#print axioms` for every main theorem (all
  `propext`-only, two `rfl` facts axiom-free, the joint witness
  `[propext, Quot.sound]` via the reused Bild witness — all standard).

Every premise of every theorem is used; no `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`; no Prop-typed premise; English only.

## Check results

- `./lean-probe grammatik/Grammatik/X86/ValidationBudget.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (module olean builds;
  `grammatik/.lake/build/lib/lean/Grammatik/X86/ValidationBudget.olean`
  fresh). Axiom prints are standard (see above).
- `./lean-bau` last line:
  `== exit 1; 2 error line(s) in the COMPLETE output`
  392/393 targets build; the ONLY failing target is the umbrella
  `Grammatik` import-only step, crashing with
  `libc++abi: terminating ... failed to create thread / Lean exited
  with code 134`.
- `gabbro_ziel` axiom re-check (`./lean-probe .../BeweisAtomar.lean`):
  blocked by the same worker crash (exit 134).

## What remains open / findings

1. **Umbrella crash is environmental and pre-existing, not mine.**
   With my import line temporarily commented out of `Grammatik.lean`,
   `./lean-bau` fails identically (391/392, same crash at the umbrella
   step); the line was restored byte-identically (`git diff` shows no
   change to `Grammatik.lean`). No `Grammatik.olean` ever existed in
   this clone. Small-file probes (`Typen.lean`, my module) pass while
   the umbrella and `BeweisAtomar.lean` crash — a worker/thread-creation
   failure under the current 15-lane machine load, not a proof error.
   The `gabbro_ziel` check is invariant under my change regardless:
   no Zielsatz module imports my file, I added no axiom and changed no
   existing theorem or definition.
2. **Elaboration finding (apparatus, not mathematics):** the first
   versions of `decodeFuel_ins_le_fuel`/`decodeFuel_mono_succ` using
   `simp [decodeFuel]` / `simp only [decodeFuel]` crashed the Lean worker
   the same way (exit 134) while smaller files probed green. Rewriting
   with an explicit definitional unfolding equation
   (`decodeFuel_cons_eq`, proved by `rfl`) plus `rw`/`simp only` with
   single local hypotheses is stable and green. Recommend: do not use
   the fuel-traversal equation lemmas as simp rules on open-fuel goals.
3. **Narrower than the future:** bounded traversal helpers only. No
   timing/cost claim (counts only, no ms/cycle/asymptotic statement), no
   complete source validator, no whole-image closure, no hardware claim
   (model bytes/memory only; TSO-per-byte vs multi-byte atomicity,
   interrupts, faults, FP/flags open), OS/binding contracts treated as
   user logic (never assumed), holder/quiescent invariants not used.
   Consumer: the direct-compiler validation stage budgets by count
   (DESIGN §588-599, §614-617: fuel-bounded search, exhausted budget
   refuses, more budget keeps the valid result).

## Anything in the task I believe is wrong

Nothing. The "no quadratic-cost/millisecond claim without measurement"
and "boundedness only where actually derived" constraints were followed:
the only bounds proved are `ins.length ≤ fuel` / `es.length ≤ fuel`,
derived by induction, with no time interpretation.

## Integration-gate response (second turn, same day)

Gate evidence: `RuntimeError: Lean merge build failed` with the umbrella
`Grammatik` step crashing (`failed to create thread`, exit 134,
397/398 in the main checkout). Decisive detail: **every
`ValidationBudget.lean` line in the gate log is `info:`** — my module
compiled green inside the integration build too (all 27 axiom lines
printed, standard axioms). No error line references any owned file.

Repair verdict after re-verification in my clone (branch `muse/431`,
commit `c1a41a1a`, tree clean):

- `./lean-probe grammatik/Grammatik/X86/ValidationBudget.lean` still
  `== 0 error(s) ... exit 0`.
- `./lean-bau` still `== exit 1; 2 error line(s) in the COMPLETE
  output`, failing only at the umbrella step (392/393 here).
- Mechanical gate rules re-checked on the owned files: no `sorry`,
  `admit`, `axiom` declaration, `native_decide` or `unsafe` (grep-clean;
  `#print axioms` lines are not declarations); umbrella diff is exactly
  one additive import line; INHABITATION needs no `_zeuge` (no premise
  quantifies over program syntax, no `ZEUGE:` target in the task);
  `CUTS:` + per-theorem `#print axioms` present; English only.
- Control experiment stands: umbrella crashes identically with my import
  removed, and no `Grammatik.olean` ever existed in this clone.

**No owned-file repair is indicated by the evidence, and none was
made** (fabricating a change would only add review noise). The failing
target is outside my owned files and fails identically without my
module. Concrete blocker for the coordinator, not assumable away: the
umbrella `Grammatik` olean build crashes the Lean worker at thread
creation in both checkouts, repeatedly across load levels — needs
infra-level action (rebuild in a quiet window, worker memory/thread
budget, or an umbrella split decided at coordinator level). My module
adds exactly one small olean to that closure and builds green on both
sides of the gate.

No acceptance of the full source/binary chain is claimed; the
narrower-than-future statement of the first report section is unchanged.
A fresh independent review of the changed commit is expected per the
gate instruction; reviewers can reproduce the green module check with
`./lean-probe grammatik/Grammatik/X86/ValidationBudget.lean`.
