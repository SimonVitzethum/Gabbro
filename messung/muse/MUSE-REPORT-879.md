# MUSE-REPORT-879: Optimiser rule — spill freshness rule

## What was done

New file `grammatik/Grammatik/X86/OptSpillFresh.lean` (registered in
`grammatik/Grammatik.lean`), implementing the DIRECT-COMPILER-DESIGN
section 7 row "Layout / allocation": local premise "colouring vs
recomputed liveness; spills fresh private frame slots, token-threaded,
save/restore on all paths", certificate "B+C map", failure "fused 16-byte
spill over two live carriers; spill slot overlapping neighbour frame;
address-taken spill via call arg", phase L.

- Certificate shape: `SpillCert` (six validator-decided `Bool`s) with
  admission `spillZulassen` (conjunction; refusal falls back to another
  certified translation, never to a warning).
- Refusals proved of the decided `Bool`: `spillVerweigert_nachbar`,
  `spillVerweigert_adresse`, `spillVerweigert_fusion`,
  `spillVerweigert_token`, `spillVerweigert_wege`,
  `spillVerweigert_frisch`, plus positive probe
  `probe_spillZulassen_ok`.
- Preservation lemmas over reused canonical vocabulary (`Stapel`,
  `Speicher`, `SpillPrivate`, `CostSummary`; no new ISA, no second IR):
  `spill_rundreise` (value + fault round-trip), `spill_fremd_bleibt`
  (disjoint carrier reads survive — contracts at their place),
  `spill_berechtigungen` (permissions unchanged — no fault added/removed),
  `spill_bytes_behalten` (whole little-endian bytes — IEEE bit patterns,
  no rounding/width change).
- Connection `OptSpillFresh_verbindung` over arbitrary values with
  validator-decided side conditions: admission `hAdm` plus recomputed
  analysis citations (`hBoundOf`: B-map slot in frame; `hSepOf`: B+C
  neighbour/foreign disjointness; `hAlle`: C boundedness so spill work is
  counted in `expandBound`). Seven conjuncts: value, permissions, outside
  bytes, IEEE bytes, disjoint reads (contracts/call-logs: one private
  `write64`/`read64` pair, no new call or shared access), both-orders
  commutation with a disjoint foreign store (concurrency, via
  `spill_fill_kommutiert`), counted budget (`expandBound_gilt`).
  No `ensures` derived; out-of-frame/permission refusals stay loud `none`.
- Witness data `spillWv`, `spillWw`, `spillWm'`, `spillWm2`,
  `spillWmab`, `spillWmba`, and joint witness
  `OptSpillFresh_verbindung_zeuge`: all premises jointly inhabited on the
  checked frame (slot 1 spills `42`, slot 3 is the disjoint foreign word
  `22`), beside non-degenerate `refD` (`refEin_schreibt`), the reached
  memory-changing run `MB` (`refB_erreicht`, `refB_schreibt`: slot
  `0 -> 100`), and an observably changing spill slot byte.
- Every premise of every new theorem is used by its proof; no `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe`; no premise typed `Prop`
  itself. Axioms are standard subsets of
  `propext, Classical.choice, Quot.sound` (see `#print axioms` output).

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (511 jobs).`
`./lean-probe grammatik/Grammatik/X86/OptSpillFresh.lean`:
`== 0 error(s) in the COMPLETE output; exit 0`.

## What remains open (see CUTS in the file)

SCFG-side application waits for the accepted 287 interface (only the
TSO-side commutation of `SpillPrivate` is reused); no aligned multi-byte
atomicity beyond byte-extensional agreement; no LOCK RMW; no
source-to-target simulation; no cost/fairness/timing claim beyond the
counted `expandBound`; no new ISA form.

## Remarks on the task

Nothing in the task appears wrong. One scoping note: the "call logs"
conjunct is carried as absence of new call/shared access (the spill is a
private target word pair, token-threaded, save/restore on all paths)
rather than a source `Folge` event equality, since the spill lives below
the source language; the joint witness keeps the source run beside the
target spill so the non-degeneracy is joint, not assumed.
