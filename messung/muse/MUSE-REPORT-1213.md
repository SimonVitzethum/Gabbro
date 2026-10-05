# MUSE-REPORT-1213: LOCK words to W history — timestamp and value link

## Status: GREEN — `./lean-probe` 0 errors, `./lean-bau` 640 jobs success

Clone `/home/simon/Dokumente/gabbro-muse/a1213`, branch `muse/1213` (verified
via `git rev-parse --abbrev-ref HEAD`). Owned files only:
`grammatik/Grammatik/X86/TsoRmwLink.lean` (new, 441 lines),
`grammatik/Grammatik.lean` (one appended import line),
this report.

## What was done

New file `grammatik/Grammatik/X86/TsoRmwLink.lean` (namespace
`Gabbro.Grammatik.X86`), imports only `Grammatik.X86.TsoRmwBridge` and
`Grammatik.Speichermodell.Sicht`. Reuses the accepted evaluator and
witnesses unchanged (never a second model); lifts lane-1145 lemmas where
the work is a lift, proves the genuinely new history-level facts directly.

New definitions (exact names):
- `LockHist` — abbrev, `Adresse → List (Nachricht Adresse Wort)`.
- `LockBlick` — abbrev, `Sicht Adresse`.
- `RmwLink ev hist v a wahl neu wneu : Prop` — structure with fields
  `liesWert` (read pairing = message value), `lesbar` (`Lesbar`),
  `frisch` (`Frisch`), `angrenzend` (`neu = wahl.ts + 1`, exactly the
  `SchrittW.rmw` shape), `schreibtWert` (write pairing = installed value).
- `witHist`, `witBlick`, `witWahl` — concrete witness history/view/message
  (word 10 at timestamp 1 on the witness address, timestamp 2 fresh).

New theorems (exact names, every premise feeds the proof):
- `rmwLink_adapter_wf` — plug preserves `HwWf` (lift of `tsoRmwAdapter_wf`).
- `rmwLink_puffer_verweigert`, `rmwLink_unaligned_verweigert` — planted
  refusals: pending own store / misaligned word admit no link event (lifts).
- `rmwLink_xadd` — XADD value link: read pairing = history message value,
  write pairing = installed word, `RmwLink` with `rmw` adjacency, full word
  footprint (`Fuss`), from the accepted step equation with the SAME guards.
- `rmwLink_cmpxchg_erfolg` — same for CMPXCHG success (via
  `CmpxchgErfolgForm`).
- `rmwLink_cmpxchg_fehlschlag_nur_liest` — CMPXCHG failure is read-only
  (`ev.geschrieben = ev.gelesen`, word written back unchanged) with the
  same value link and adjacency.
- `rmwLink_kette` — history-level chain: second read pairing = first write
  pairing, `w1.ts < w2.ts`, `neu1 < neu2` (genuinely new, `omega` over the
  two adjacencies; all four premises used).
- `rmwLink_kette_ohne_puffer` — machine-level chain with no intervening
  buffered store (`hbuf1`/`hbuf2` are the guards), lifting
  `tsoRmw_kette_ohne_verlust` via `apply … <;> assumption`.
- `witWahl_mem`, `witWahl_lesbar`, `witNeu_frisch`, `witWahl_wert`,
  `witNeu_adj` — witness pins (membership, readability, freshness of
  timestamp 2, value/stamp equalities).
- `rmwLink_zeuge` — joint witness on the reached two-core run (word
  10 → 15 → 22 across cores 0/1, event words equal to the history message
  value, `rmw` adjacency discharged, owner-only forwarding, `HwWf`, both
  planted refusals). Non-degenerate: two memory-changing steps, one
  buffered store forwarded to its owner only.

File ends with a `CUTS:` block and `#print axioms` for every theorem.
No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no new silicon claim
(provenance: Intel SDM 325462-093US via accepted 662 module + lane 1145);
English only.

## Last `./lean-bau` result line

`Build completed successfully (640 jobs).` — full `grammatik/` build green
including the new module. `./lean-probe
grammatik/Grammatik/X86/TsoRmwLink.lean`: `== 0 error(s) in the COMPLETE
output; exit 0`. `#print axioms` per main theorem: `[propext,
Quot.sound]` for the link/chain/witness theorems, `[propext]` for the
witness history pins, no axioms for the two `rfl` pins — all within the
goal's standard set (`propext`, `Classical.choice`, `Quot.sound`).

## Repair during verification (honest record)

First probe found 2 errors, both in `rmwLink_kette_ohne_puffer`: `apply
tsoRmw_kette_ohne_verlust <;> assumption` unified the 36 explicit
metavariables against the wrong same-shaped hypotheses (empty-buffer and
read/write guards repeat per step). Repaired by passing all 38 arguments
explicitly by position in the exact binder order of the cited lemma;
re-probe 0 errors. No premise added, no conclusion weakened.

## Known verification risks (for the follow-up)

None remaining — all `simp`/`decide`/`rw`/`omega` steps closed under the
prober. Name collisions checked by grep: none (all hits are the new file
itself).

## What remains open (also recorded in the file's CUTS)

- The link is over the GENERIC history shape, not over a concrete Gabbro
  program's carriers: no accepted x86-address → carrier mapping exists yet
  (source/table-write consumers own it). The `rmw` field of a full
  `SchrittW` is shaped, not discharged; no per-access target-to-W/GX
  simulation is claimed.
- Narrower widths, other addressing modes, split-lock detection, fetched-byte
  dispatch, fairness/retry bounds: open as before.

## Task critique

The task is sound but one bullet overreaches as stated: "the `rmw` field is
discharged for a step with no intervening buffered store" cannot mean the
`SchrittW.rmw` field itself (which quantifies over Gabbro `Glob`s and needs
the missing address→carrier map). What IS proved is the exact shape of that
field (`neu = wahl.ts + 1` + `Frisch`) at `Adresse`/`Wort` for every accepted
locked step, plus strict increase along chains. The report and CUTS state
this boundary explicitly; nothing is claimed beyond it.
