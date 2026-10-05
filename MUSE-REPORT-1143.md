# MUSE-REPORT-1143: TSO to W bridge — fragment READS

## What was done

New file `grammatik/Grammatik/X86/TsoReadBridge.lean` (~1690 lines) plus one
`import Grammatik.X86.TsoReadBridge` line in `grammatik/Grammatik.lean`.
It closes the OPEN read leg of `CarrierTraceBridge.lean`: a typed-carrier
read whose value comes from canonical memory or own-buffer forwarding yields
an actual typed-carrier `SchrittW` whose G step reads the carrier.

Exact new definitions/theorems:

- §1 lifts (no redefinition, all accepted lemmas applied):
  `hwLade_erhaelt_wf` (read case of `hwSchritt_wf`),
  `hwLade_trifft_speicher` (machine read at a committed address is the
  canonical byte, via `load_ohne_eintrag`), `beitrag_tabelle_le` (a relaxed
  table read contributes at most its timestamp).
- `lesespur_assignSlot` (+ `_zeuge`): a one-read `assignSlot` step prepends
  exactly write+read events (read analogue of `assignSlot_spur`).
- `schrittW_aus_lesefragment_gruppe` (+ `_zeuge`): full `SchrittW` for a
  one-read fragment write with a COMMITTED group read; `lies` derived from
  `wLesbar_aus_gruppe`, freshness above the read-joined view.
- `schrittW_aus_lesefragment_weiterleitung` (+ `_zeuge`): full `SchrittW`
  for the FORWARDED case; value link `hWert` and youngest-split exhibition
  from `wLesbar_aus_weiterleitung`; read observations live at their own
  TSO state `sR`, the drain at `s2` (shared source fragment only).
- `stale_kein_globaler_wert`, `gruppe_kein_globaler_wert` (proved refusals:
  no global value for unflushed/torn stores).
- Witness vocabulary: two-table declaration `rdD` (write `false` holds 9,
  read `true` holds 0), copy fragment `rdS`, nine-word memory `rdM9`,
  eight-flush drain `rdS2`–`rdS11` with foreign issue, forwarded state
  `rdSF`, reading W `rdW1` (timestamp-1 message), clock-2 projected node
  `rdNB11` (one real flush step), G machine `rdMachine`.

Last `./lean-bau` result line: `Build completed successfully (601 jobs).`
`./lean-probe` on the new file: `0 error(s)`. `#print axioms` for every
main theorem: at most `propext, Classical.choice, Quot.sound`. No `sorry`,
`admit`, `axiom`, `native_decide`, `unsafe`. No existing file edited except
the import line; no existing theorem touched.

## What remains open (see file CUTS)

No hardware correspondence claim; forwarded witness traces only the last
drain flush (clock-2 node), the full 9-step projection stays OPEN; the
forwarded value link and reading-W shape are explicit lowering-certificate
premises; no run induction to W runs, no GX refinement, no `valX86_sound`.

## What in the task I believe is wrong

The MECHANISM paragraph asks for an `HwAdapter` over the coherent machine
with `HwWf` preservation as the deliverable shape. For a TSO→W bridge lane
that shape does not fit: the read bridge connects TSO states to W steps,
not an ISA family to `HwMaschine`. I proved the BRIDGE paragraph instead
(`SchrittW` read steps, the actual OPEN leg), and connected to the machine
only where it is real: `HwSchritt.lade` observations preserve `HwWf` and
return the canonical byte when committed (§1). The adapter plugs of
`HardwareExecution` §11 are untouched for their owning producers.
