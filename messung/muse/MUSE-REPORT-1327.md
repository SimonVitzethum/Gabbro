# MUSE-REPORT-1327: TSO projection of the isa, addr and muldiv union tags

## What was done

New file `grammatik/Grammatik/X86/HwKapsteinTsoIsaAddr.lean` (~415 lines) plus one
`import Grammatik.X86.HwKapsteinTsoIsaAddr` line appended to `grammatik/Grammatik.lean`.
No other existing file touched. Every accepted definition is reused unchanged
(lifted, never redefined); no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`;
`#print axioms` for every theorem shows only `[propext, Quot.sound]`, `[propext]`,
or no axioms (subset of the goal standard).

The three tags left as FINDINGs by lane 1295 are now classified over the reused
projection `kapTso` (lane 1295's `tsoAnsicht` projection, never redefined):

- **isa** — exact classification `(a) / (b)` per step (`kap_isa_tso_klass`):
  register steps are silent (only core data moves, `kapTso_setKernVonZustand`),
  loads observe with forwarding (`loadByte`, observed and demanded values named),
  stores are single `issueByte` events with the footprint (core, address, value)
  named. Reachability (`kap_isa_tso`): silent legs reuse `.start`, stores use one
  TSO issue step.
- **muldiv** — classification `(a)` (`kap_muldiv_tso_still`, `kap_muldiv_tso`):
  every step is silent. A success re-embeds core data only (memory-freedom is the
  cited accepted `wdSchritt_speicher`); the divide trap and refusals admit no
  successor at all. The footprint is the accepted width step itself.
- **addr** — stores are the requested `concIssue` fold
  (`kapTso_concIssue_erreichbar`: admitted gate plus the `issueListe` induction
  over `entriesOf`, reusing lane 1295's `kapTso_issueListe_erreichbar`;
  `kap_addr_store_issue` names the exact footprint from `adrEff` (`hwAddrOf`
  over the acting core's pre-state registers) and the pre-state source register;
  `kap_addr_store_tso` for reachability). Loads are silent forwarding
  observations (`kap_addr_load_still`: `concLoad` value named, destination merged
  through the accepted `mergeRegNarrow`), reaching via `.start` (`kap_addr_tso`).
  Width cases 1/2/4/8 bytes (`kap_addr_breiten`, via `entriesOf_laenge`); a split
  across a group boundary stays the accepted tearing refusal (`kap_addr_tearing`:
  the exhibited partial buffer and foreign-footprint overlap are no `WortGruppe`).
- Union lifts `kap_union_isa_tso`, `kap_union_addr_tso`, `kap_union_muldiv_tso`
  (each inverts its `HwVollSchritt` constructor exactly) and the joint summary
  conjunction `kap_drei_tso` (each leg uses its own premises).
- Joint witness `kap_isa_addr_muldiv_zeuge`: one exhibited union step per tag
  (buffered isa byte, width-4 SIB addr store, register-only muldiv divide, reusing
  `kap_step_isa`, `kap_step_addr`, `kap_step_muldiv`) reaches through the
  projection, beside the two-core non-degeneracy on the same TSO model
  (owner-only forwarding 42, foreign core reads stale 0, drain installs 42 /
  `0x04` into shared memory, observed from both cores).
- `wort`/`stapel` needed nothing here: both are already classified by lane 1295
  (`kap_union_wort_tso`, `kap_union_stapel_tso`); verified by grep, no new lemmas.

No high-priority FINDING: every memory write of these three families travels the
accepted issue path (`issueByte` / `concIssue` fold); register-only forms provably
leave the projection unchanged. Canonical memory is never written except through
TSO drains (cited, not re-proved).

## Exact names of new theorems (no new definitions)

`kapTso_setKernVonZustand`, `kap_isa_tso_klass`, `kap_isa_tso`,
`kap_muldiv_tso_still`, `kap_muldiv_tso`, `kapTso_concIssue_erreichbar`,
`kap_addr_store_issue`, `kap_addr_store_tso`, `kap_addr_load_still`,
`kap_addr_tso`, `kap_addr_breiten`, `kap_addr_tearing`, `kap_union_isa_tso`,
`kap_union_addr_tso`, `kap_union_muldiv_tso`, `kap_drei_tso`,
`kap_isa_addr_muldiv_zeuge`.

## Last build result

`./lean-probe grammatik/Grammatik/X86/HwKapsteinTsoIsaAddr.lean`: `== 0 error(s)`.
`./lean-bau`: `Build completed successfully (691 jobs)`, including `Built Grammatik`.
Grep for `sorry|admit|axiom|native_decide|unsafe|sorryAx` in the new file finds only
the English words "admitted"/"admit no successor" and the required `#print axioms` lines.

## What remains open (see CUTS)

- The remaining 13 union tags (lockRmw, lockFetch, uc, port, fp, fehler, tor, vec,
  nested, int, system, bild, instanzen) keep lane 1295's FINDING status.
- No W/GX bridge (target-only reachability); no whole-word atomicity beyond the
  accepted byte-drain equations and the cited tearing refusals; no source, checker,
  contract, entry, ABI, loader, budget or liveness claim; no hardware correspondence
  beyond self-consistency (vendor-neutral: nothing Intel-only or AMD-only is pinned).

## What I believe is wrong in the task

1. The MECHANISM paragraph describes connecting ONE family via a new `HwAdapter`
   and a new event type, which does not match the TASK (classify three already-plugged
   union tags over the existing projection). The file follows the TASK: no new adapter
   or event type is defined; the accepted plugs are classified, not rebuilt.
2. "Exactly one accepted TSO event" as a single-step claim does not hold for addr
   stores (a width-4 store is four byte issues, a width-8 store eight); the file proves
   the honest multi-step form (`TSOErreichbar` over the `concIssue` fold) and keeps
   single-step exactness only where it holds (isa stores, silent observations).
3. The CONTEXT's "14 pilot forms" census is stale relative to the current tree, but it
   does not affect this lane's proofs, which depend only on the cited accepted lemmas.
