# MUSE-REPORT-1147: Whole-word atomicity of guarded aligned accesses

## What was done

New file `grammatik/Grammatik/X86/HwWordAtomicity.lean` (~425 lines) plus one
`import Grammatik.X86.HwWordAtomicity` line appended to `grammatik/Grammatik.lean`.
It connects the ACCEPTED `WordAccessGrouping` / `WordDrainInterleaving` family to
the coherent `HwMaschine` / `HwSchritt` of `HardwareExecution`, lifting the
accepted definitions unchanged (never redefined, never copied).

- Family event type `HwWortZugriff` (`wortAusgabe a v`, `wortSpuelung`) and
  adapter `adapterWort1147 : HwAdapter HwWortZugriff` (word stores ride the
  accepted `hwWortAusgabe`, drains flush the oldest entry).
- (1) `HwWf` preserved: `adapterWort1147_wf` (both arms touch only
  memory/buffers via `setTso`).
- (2) Exact agreement: `adapterWort1147_ausgabe`, `adapterWort1147_spuelung`
  (both `rfl`), and exact embedding `adapterWort1147_spuelung_einbettung`
  (adapter drain = one `HwSchritt.spuele` step with the buffer head).
- Guarded observation on the machine over the transparent wrapper `hwWortM`
  (`hwWortM_ansicht`, `hwWortM_wf`): `hw_wort_gruppe_liest_zurueck` and
  `hw_wort_gruppe_rahmen` lift the accepted read-back/frame lemmas, with
  `hw_wort_fremd_beobachtet_ganz` / `hw_rahmen_fremd_beobachtet_ganz` reading
  the whole word back through EVERY core projection (one shared memory).
- (3) Refusals: `adapterWort1147_spuelung_verweigert_leer`,
  `hw_teilwort_keine_gruppe`, `hw_overlap_keine_gruppe`
  (alignment admits what the exclusion check refuses), `hw_ausrichtung_vA`.
- Hardware assumption `HwWortAtomar` stated, named, never inhabited, assumed,
  or discharged; `HwWortBruecke` empty (`kein_hw_wort_bruecke`).
- (4) Witnesses: `hw_verflochten_zeuge` (joint over every premise of the
  guarded observation: group, readability, alignment, trace, end membership,
  both buffers empty, per-state exclusion, reachability, whole read-back per
  projection, both memory changes, owner-only forwarding, real foreign
  issue+flush, well-formedness) and `hw_riss_zeuge` (real machine tearing step
  with mixed word), plus `hw_erster_schritt_reisst`.
- CUTS block and `#print axioms` for every main theorem (all within
  propext/Quot.sound; several depend on no axioms at all).

## Last build result

`./lean-bau`: `Build completed successfully (601 jobs).`
`./lean-probe grammatik/Grammatik/X86/HwWordAtomicity.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`.

## Repair after the failed integration gate (no merge happened)

Integration evidence: the merge build failed ONLY on
`Grammatik.X86.HwWordAtomicity` with `lean::exception: failed to create
thread`, exit 134 — a resource-class failure (address-space/thread
exhaustion under the integration build's `-j2 -M4096` budget), not a proof
error. No unknown identifier, no unsolved goal, no axiom violation was
reported; the candidate's `#print axioms` output stays within
propext/Quot.sound.

Repair inside the owned module (no guarantee touched, no theorem weakened,
statements byte-identical): three kernel `decide` proofs replaced by
definitional `rfl` (`hw_ausrichtung_vA`, the two forwarding facts in
`hw_verflochten_zeuge`); the one genuine disequality keeps its `decide`
(`rfl` cannot prove `≠`; attempted and reverted). Local `./lean-probe`
0 errors and full `./lean-bau` 601 jobs green after the change.

Honest status: the failure mode matches the known environment ceiling
("failed to create thread even on unchanged source"); nothing in this
module's elaboration plausibly exhausts 4 GiB (closed-term evaluations over
8-entry buffers). If the gate fails again with the same signature, the
blocker is environmental (parallel-build memory pressure), not this
candidate. A fresh independent review is still required for the changed
commit; no acceptance of any source/binary chain is claimed.

## What remains open

Single-copy bridge to silicon and any per-access W/GX simulation
(`kein_hw_wort_bruecke` states the gap); no source/checker/contract/entry/
timing claims. No SDM extract is present in this clone, so the textbook
single-copy rule for one aligned access is cited only as the shape of the OPEN
assumption, not as checked provenance.

## Where the task statement needs a correction

"Observed whole by every foreign core (no mid-drain mixed word)" is not
provable for the grouped word itself and must not be claimed: the accepted
byte drain passes through mixed words by construction (`hw_erster_schritt_reisst`,
`hw_riss_zeuge` — this is also true on real silicon for separate byte stores).
What the guard delivers, and what is proved, is whole observation at the
drained END state through every core plus whole observation of every DISJOINT
word at every visited state. The task's own THEOREM line ("per-byte facts do
not give whole-word atomicity") is therefore the result, with `HwWortAtomar`
naming exactly the undischarged remainder.
