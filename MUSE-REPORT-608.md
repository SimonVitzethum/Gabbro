# MUSE-REPORT-608: Independent overnight closure review of 596

## Identity

- Directory verified: `/home/simon/Dokumente/gabbro-muse/a608`, branch `muse/608`. Match; proceeded.
- Owned file only: `MUSE-REPORT-608.md`. No other clone paths touched; no Lean imports added; no `grammatik/` edit; no network/push/model calls.

## Candidate under review

- CANDIDATE: 596 `60ccda1aba792381359c89b62b5305a97973b789`
- Base: `0044c2585bdd2ebad67d8d7bd5c3a4db11b171eb`; pinned HEAD object verified present (`git cat-file -t` = commit, log tip matches report commit).
- Files (diff vs base, exactly 3, +717/-0): `MUSE-REPORT-596.md`, `grammatik/Grammatik.lean` (one umbrella import line, appended at end), `grammatik/Grammatik/X86/TSOTrace.lean` (new, 614 lines).
- Task source: `.tmp/review/author-596/OWNER-TASK.md` (Lane 596: TSO history preservation across actual finite traces). Report source: `.tmp/review/author-596/MUSE-REPORT-596.md`. Build log: `.tmp/review/author-596/BUILD-EVIDENCE.json` (incremental `lean-probe` history with honest intermediate failures, final `lean-probe` 0 errors, final `lean-bau` exit 0 / 0 error lines / 440 jobs).

## What was checked (actual evidence, not report text)

1. **Forbidden patterns** (`grep` over the exact candidate file): no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no `intro _`, no `have _ :=`. No `Prop`-typed premise (only hit is the `def SpurInv ... : Prop` definition itself). No `forall rho`/`forall v` contract-quantification pattern.
2. **Axioms**: build evidence prints `#print axioms` for all 28 theorems: only `propext`, `Quot.sound`, or none. Standard subset of the goal axioms. No `Classical.choice` needed; nothing beyond standard.
3. **Untouched boundaries**: `TSOHistory.lean` and every other existing file unchanged (name-only diff confirms). No `Zielsatz/Spec`, checker (`saetze.rs`/passes), or friend-reserved optimiser (`OptimizationRules`/`OptimizationWitnesses`) edits. No named OS assumptions.
4. **Reuse is real**: every claimed reuse resolves in-tree — `TSOZustand`, `issueByte`, `flushKern`, `loadByte`, `neuestens`, `flush_schreibt_kopf`, `issue_haengt_an` (`TSO.lean`/`TSOHistory.lean`/`FenceDrain.lean`), `weiterleitung_ist_jüngste`, `histVon`, `fremd_weiterleitung_unsichtbar` (`TSOHistory.lean`), `sbStart/sbNach1/sbNach2/sbGespült/sbX/sbY/sbEins/sbX_ne_sbY/sb_schritt1/sb_schritt2/sb_flush_schritt/pufferSetze_*` (`TSO.lean`). No guessed ISA: addresses/bytes/buffers are the canonical `Adresse`/`Byte`/`TSOEintrag` vocabulary.
5. **No new executor / no new source semantics**: `SpurSchritt` projects every step onto `issueByte`/`flushKern` equations; no new TSO stepper, no `execStmt`/`exec` competitor, no extra IR. New names (`SpurKnoten`, `spurStart`, `SpurSchritt`, `SpurErreichbar`, `SpurInv`, `traceHist/traceSicht/traceFrisch`, `spurW*`) do not redefine canonical vocabulary.
6. **No timestamp reset**: issue keeps `frisch`, flush advances `+1`; `spur_verlauf_waechst` proves `n0.frisch <= n.frisch` by induction. No claim that projection clocks ARE source W timestamps — CUTS states the discipline is projection-local. So there is no "reset timestamps as W-run correspondence" to reject; the file explicitly refuses that reading.
7. **No smuggled simulation**: flush appends `e.wert` from the buffer entry pinned by `he : puffer c = e :: rest` together with `h : flushKern ... = some ...`. FIFO pins `e = ⟨a,v⟩` from the two-issue history (`spur_fifo_aelteste`). Value flows entry → memory/message, never conclusion → entry.
8. **Premise use** (manual): every main theorem consumes all its premises — freshness uses both invariant halves; `spur_ein_flush` uses `hinv` for `Frisch` and invariant preservation; `spur_fifo_aelteste` uses `h1/h2/hempty/heq/h/hh` (buffer-shape chain, flush fact, history membership); forwarding wrapper forwards both `hload`/`hpend` to the canonical lemma. `spur_freigabe_sicht` is a definitional `rfl` pair over the `nachricht` constructor — a projection helper, not a deep claim; acceptable as labelled.
9. **Forwarding + release views**: both task-mandated points are proved facts, not obstructions — youngest-split forwarding via `weiterleitung_ist_jüngste` (all premises kept), writer-view release via `setze` at the flush clock. No `blocked` label is needed because nothing is blocked; the report correctly does not claim closure beyond bytes.
10. **Joint witness** (`spur_zeuge_gelenk` chain `spurW0..spurW4`): reached from start over four steps; two cores; `spurW_speicher` shows BOTH canonical bytes change (`decide`); `spurW_laden` shows both cores read back `1` (`decide`); both release messages `Lesbar` at joined views; `spurW_uhren` gives clocks 1 and 2 with `1 ≠ 2`. Non-degenerate per the task (two buffered stores, two memory-changing flushes, distinct stamps). Note on scope: this is a TSO-trace witness, NOT a source `exec`/run witness — which the task did not ask for. It must not be cited as source-level inhabitation.
11. **CUTS**: precise and load-bearing — byte layer only; no typed-carrier W/GX, no multi-byte atomicity (cites `hist_zerreissen` tearing), no LOCK RMW, no `SchrittW`/G-step/run induction (explicitly owned by BridgeWrite573/BridgeRead574), forwarded-but-unflushed values have no message (snapshot half cites proved `fremd_weiterleitung_unsichtbar`), `histVon` preserved as bounded legacy evidence, no fairness/timing/device/fence-beyond-gate claims.
12. **Legacy preservation**: `spurStart_legt_snapshot_vor` links start nodes into unchanged `histVon`; `TSOHistory` unmodified.
13. **Consumer API**: `traceHist/traceSicht/traceFrisch` plus `spur_ein_flush`, `spur_verlauf_waechst`, `spur_fifo_aelteste`, `spur_freigabe_sicht`, `spur_weiterleitung_ist_jüngste` — stable named set matching the 573/574 handoff claim; no over-claim of a full bridge.

## Findings that are NOT defects (recorded to bound scope)

- `spur_fifo_aelteste` takes the history equation `hh` as a premise rather than deriving it; the derivation lives in the `SpurSchritt.flush` constructor equation, and the joint witness supplies the definitional instance. Conditional form is honest; callers (573/574) must thread the actual step equation, not assume it.
- No planted mutation-run evidence is supplied (Lean module; analogue would be drop/reorder mutants). Preservation is structural (`spur_schritt_erhaelt`, `spur_verlauf_waechst`, FIFO pinning) plus `decide` witness facts. Bounded acceptance rests on proof + witness, not mutation testing.
- Build green was verified from the author's evidence log (final `lean-bau` exit 0, 440 jobs), not re-executed here: re-running a full build from this reviewer clone would violate the owned-paths rule (candidate file is not present in this working tree, and adding it would exceed ownership). Fresh-candidate review therefore rests on the exact pinned file inspected byte-for-byte plus the complete incremental probe log — the reviewer received the exact candidate, never a changed draft.

## Out of scope (no verdict given)

- Tools595 (read-only monitor, identity, restart/pause behaviour, fixture reproduction), Rust618 (verifier/test verdicts, native thread-creation diagnosis), Docs594/604/605 (concrete-code decisions/ownership): none are touched by candidate 596 (3-file diff confirms), so this review gives NO verdict on them. They need their own exact-candidate reviews.
- Full typed-carrier TSO→W/GX and source-to-final-bytes validation remain OPEN (candidate CUTS say so; this review agrees).

## Repair locations

- None. No minimal repair is required for acceptance of 596 within its stated bounds.

## Bounded accepted scope

- ACCEPTED: append-only TSO trace projection (`SpurKnoten`/`SpurSchritt`/`SpurErreichbar`/`SpurInv`), one-flush extension, finite-trace growth with monotone clock and message preservation, FIFO oldest-delivery, release-view and youngest-forwarding facts, legacy `histVon` link, and the joint two-core byte-level witness — all at byte granularity, projection-local clocks, no W/GX or source-run claim.
- NOT accepted (still open, owned elsewhere): per-access W store/read bridges (573/574 against accepted 567/570 interfaces), typed carriers, atomicity, LOCK, run induction, fairness/timing, and everything under 595/618/594/604/605.

## Verdict

- VERDICT: ACCEPT
