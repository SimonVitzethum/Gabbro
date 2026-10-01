# MUSE-REPORT-421: WordAtomicity — aligned whole-word observation over the LOCK path

## Task
Create `grammatik/Grammatik/X86/WordAtomicity.lean` (+ one additive umbrella import):
a thin consumer layer over the accepted `Speicher`/`TSO`/`LockedOps` vocabulary.
One aligned whole-word update primitive observation (the accepted `lockSchritt`
XADD shape only), frame/disjoint-footprint lemmas, concrete refusals, a
word-level tearing witness from `paket_reisst`, and the explicit OPEN bridge.
No new executor, no assumed word atomicity, no source RMW closure.

## What was delivered (all in owned files only)
- `grammatik/Grammatik/X86/WordAtomicity.lean` (new, ~360 lines)
- `grammatik/Grammatik.lean`: one additive line `import Grammatik.X86.WordAtomicity`
- This report.

## New definitions/theorems
- `WortGuard` (admission guard: empty own buffer, `ausgerichtet8`, readable and
  writable footprint) — consumer: lowering/validator admit exactly this shape.
- `WortBeobachtet` (word observation: `read64 m a = some v`).
- `wort_schritt_liest_zurueck`: LOCK add reads back the installed word in one
  transition (composes `lockSchritt_xadd_erfolg` + `read64_nach_write64`).
- `read64_braucht_lesbar`, `write64_braucht_schreibbar`: successful accesses pin
  their permission guards (derived, not assumed).
- `wort_guard_aus_voraussetzungen`: LOCK premises jointly establish `WortGuard`.
- `wort_bleibt_unter_disjunkt`: disjoint word observation survives the LOCK step
  (composes step equation + `read64_rahmen`).
- `wort_rahmen_byte`: bytes outside the footprint are unchanged.
- `lock_verweigert_ohne_ausrichtung`, `lock_verweigert_bei_vollem_puffer`,
  `lock_verweigert_ohne_schreibrecht`: misaligned / nonempty-buffer / refused-store
  steps are `none`, never a silent split.
- `wort_fuss_reisst`: two bytes inside one word footprint, issued separately,
  tear (specialization of accepted `paket_reisst` via `addrOff_ne8`).
- `wortRiss2`, `wortRiss3`, `wort_fuss_reisst_zeuge` (single-core concrete tear:
  first byte new, second pre-flush, memory observably changed).
- `WortNachW` (empty inductive) + `kein_wort_nach_w`: no bridge proved here.
- Joint witnesses: `wort_schritt_liest_zurueck_zeuge` (all premises jointly on
  `lockStart`/`lockAddr`, read-back + memory change), `wortFern` +
  `wort_fern_disjunkt` (second word at 8192, disjoint via
  `disjunkt_von_intervallen`) + `wort_bleibt_unter_disjunkt_zeuge`,
  `lock_verweigert_ohne_ausrichtung_zeuge` (address 4097),
  `lock_verweigert_bei_vollem_puffer_zeuge` (`zaunStart`, core 1).
- Every premise of every theorem is used by its proof; no `Prop`-typed premise;
  no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

## Check results
- `./lean-probe grammatik/Grammatik/X86/WordAtomicity.lean`:
  **0 errors, exit 0.** All `#print axioms` within the standard set
  (subsets of propext/Classical.choice/Quot.sound; no sorryAx).
- `./lean-bau`: **392/393 targets green, including `Grammatik.X86.WordAtomicity`**.
  The final umbrella aggregation step (`Grammatik.lean` olean) aborts with
  `libc++abi: ... failed to create thread`, exit 134.
- The umbrella failure is environmental and pre-existing, proved by experiment:
  with my import stashed (pristine tree, 391/392) the identical step crashes
  identically. Other lanes' integration logs show the same abort on unrelated
  modules under current machine load (swap exhausted, dozens of competing
  `lean` processes). Reverting my change cannot make it green.
- `gabbro_ziel` axiom gate: unchanged by construction. My file is a new leaf
  imported only by the umbrella; nothing in `Zielsatz/` imports it and it
  imports nothing from `Zielsatz/`, so it is not in `gabbro_ziel`'s import
  closure. All `Zielsatz` modules built/replayed green in the same runs with
  standard axioms.

## What remains open (see CUTS in the file)
No new executor; atomicity only via the accepted `lockSchritt` XADD shape under
its declared guards; byte-wise installs tear; no W/GX refinement (`WortNachW`
empty); no hardware/silicon, timing, decode, ABI, source, checker or goal claim.

## Integration gate (post-review, merge day)
- Independent review accepted the isolated candidate; the merge gate failed with
  `RuntimeError: Lean merge build failed`, step `[397/398] Building Grammatik`,
  `lean exited with code 134`, `failed to create thread` — the same umbrella
  aggregation abort documented above, in the merge tree
  (`/home/simon/Dokumente/Gabbro`), with zero error lines in
  `Grammatik/X86/WordAtomicity.lean` (its `#print axioms` info lines are all
  clean and standard).
- Repair analysis: there is no defect in the owned module to repair. The cited
  evidence contains no type error, no axiom violation, no name clash and no
  witness gap attributable to lane 421. The failing job elaborates only the
  import-all umbrella; the lane module itself built green inside the same gate
  run. No owned file was changed for this; re-verified `./lean-probe
  grammatik/Grammatik/X86/WordAtomicity.lean` = 0 errors, exit 0, and local
  `./lean-bau` still stops only at the identical environmental umbrella abort.
- Concrete blocker for the merge (outside lane scope): the umbrella job cannot
  spawn threads under current machine contention (many concurrent lane `lean`
  processes, swap pressure). It resolves only by easing machine load or by
  coordinator-side build gating (serializing the umbrella step); a fresh
  independent review of the changed commit is still required as instructed.
- No acceptance of the full source/binary chain is claimed; the deliverable
  remains the isolated, probe-green module plus this report.
- Repeat gate failure (same `[397/398]` abort, same zero module errors):
  re-verified again — local `./lean-bau` still 392/393 green with only the
  environmental umbrella abort. Still no owned-file repair applicable; blocker
  unchanged and outside lane scope.

## Session notes (retained)
- During the session the `decide`-based refusal witnesses were rewritten to apply
  the general refusal theorems, because `lockSchritt` equations over `TSOZustand`
  have no `DecidableEq` (function fields) — `rfl`/`decide` misuse corrected.
- `OhneUmbruch` goals are stated as raw `toNat` inequalities (`decide`-friendly)
  since the def is opaque to typeclass search.
- Initial `paket_reisst` application wrongly mixed cores 0/1; the concrete tear
  is now single-core (`wortRiss2`/`wortRiss3`), matching `paket_reisst`'s shape.
