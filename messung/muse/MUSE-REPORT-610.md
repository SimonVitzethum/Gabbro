# MUSE-REPORT-610: Independent overnight closure review of 598

## Scope

Reviewed exact candidate of lane 598 (checked validator to loaded fetched
execution) against its owner task, the HARD RULES and the overnight
closure bar: connect accepted components, weaken nothing, prove the gap
with concrete counterexamples or label blocked.

CANDIDATE: 598 eab258215d5b7823fe0bbd6846c6bec0f7ef5f81

VERDICT: ACCEPT

## What the candidate contains

Three files, additions only, base
0044c2585bdd2ebad67d8d7bd5c3a4db11b171eb:

- `grammatik/Grammatik/X86/ValidatorExecution.lean` (new, 439 lines).
- `grammatik/Grammatik.lean` (one appended line:
  `import Grammatik.X86.ValidatorExecution`).
- `MUSE-REPORT-598.md` (report).

New deliverable: optional strengthened entry check `valEintrittStark`
(mapping AND containment AND executable byte AND successful
`fetchDekodiert` from actual loaded bytes), with generic soundness
`valStark_wohlgeformt`, `valStark_eintrag`, `valStark_ausfuehrbar`,
`valStark_fetch_exist`, `valStark_fundstelle`, `valStark_gibt_deckung`
(entry-at-decoded-start via `fetchDekodiert_entspricht` +
`decode_abdeckung`), `valStark_schritt` (loaded step agrees with
`byteschritt` via `byteschritt_weiter`). Old `valX86`/`wohlgeformt`
untouched. Counterexamples: interior byte (`innen_gegenbeispiel`),
BSS byte (`bss_eintritt_gegenbeispiel`), truncated window-vs-fetch pin
(`stumpf_fetch_verweigert`), permission mutations
(`permission_verweigert`, `valStark_store_wx_verweigert`). Positive
joint witness `valStark_store_zeuge` (admitted biased store entry,
fetch decodes store, step moves 42 into data, zero before, real
write/read with changed byte, interior refusal).

## Verification performed (independent, this lane)

- Identity: `.tmp/review/author-598` file is byte-identical to
  `git show eab25821:.../ValidatorExecution.lean` (diff empty).
- Transient copy of the exact file into the working tree (removed
  afterwards; tree verified clean): `./lean-probe` result
  `== 0 error(s) in the COMPLETE output; exit 0`. Note the probe ran
  against oleans NEWER than the candidate base (this checkout), so the
  file is also compatible with the current tree.
- `#print axioms` output (from that probe run): every theorem depends
  on at most `[propext, Quot.sound]`; most decide-theorems on
  `[propext]` only, `innen_eintrag_innen` on none. Standard subset,
  better than the report's claim.
- Forbidden constructs: strict grep for `sorry`, leading `axiom`,
  `native_decide`, `unsafe`, leading `admit` finds nothing (only the
  English words "admits/admission" in comments).
- Producer signatures checked by hand: `decode_abdeckung` tuple order
  `(heq, hok, hshape, _)` matches; `fetchDekodiert_entspricht` `.1`
  feeds `decode_abdeckung`, `.2.2.2` is the executable-prefix fact;
  `byteschritt_weiter` applied with matching arguments;
  `bildStore_fetch_store`, `bildStore_schritt_speichert`,
  `schreibLese_zeuge` reused (not re-proved) in the joint witness.
- Premise use: every generic theorem uses all its premises
  (`valStark_schritt` consumes `h` via `valStark_eintrag` and
  `hf`/`hs` via `byteschritt_weiter`). No `Prop`-typed premises, no
  discarded premises, no restated conclusions (Bool-conjunction
  projections are legitimate eliminations, not renamings).
- No source checker/Spec/goal edits, no optimiser-reserved files, no
  OS assumptions, no new IR or interpreter, no second model: admission,
  fetch, step and refusal all share `bildZustand`/`bildStoreStart`
  states (`valStark_store_start` is `rfl`).
- No Lean name collisions with the current tree (grep over
  `grammatik/` for the new names finds nothing else).
- CUTS block present and precise; no `valX86_sound`, source, silicon,
  multi-step, relocation, TSO/GX, cost or termination claim.

## Findings against the closure bar

- The interior-entry gap is REAL and proved: `innen_valX86`
  (`valX86 = true` with entry `0x1001` inside a 3-byte instruction)
  typechecks, while `innen_fetch_verweigert` shows the actual fetch
  refuses. Not self-consistency: old Bool and fetched execution
  genuinely disagree on the pinned images.
- The truncation pin is the strongest detail: the 15-byte
  `eintrittDekodiert` window decodes by reading zeros past the
  executable boundary while `fetchDekodiert` refuses, which justifies
  the fetch-based (not window-decode-based) strengthened check.
- Bounded accepted scope: one optional Bool check plus its entry-leg
  consequences and pinned counterexamples/witnesses. Consumer for a
  future `valX86_sound` entry leg is named; nothing more is claimed.

## Integration note (not a defect)

`grammatik/Grammatik.lean` gained umbrella imports from lanes 596, 600
and 602 after the candidate base, so the serial merge needs the routine
import-union resolution. The candidate's import line is unique; no
content conflict is possible beyond the shared file tail.

## Open (unchanged, correctly labelled)

`valX86_sound`, source correspondence (IR287 pending), hardware,
multi-step control flow, relocation re-decode, TSO/GX bridge, costs.
All listed in the file CUTS, none claimed.

## Next independent tasks (suggestions only, unstarted)

- Per-entry decode-boundary traversal from each listed entry
  (fuel-bounded, fail-closed) reusing `decodeFuel`.
- Patched-relocation-site re-decode correspondence.
- Multi-step control-flow validation over `valEintrittStark`-admitted
  entries.
