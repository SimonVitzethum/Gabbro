# MUSE-REPORT-567: Canonical byte-TSO history projection

Lane 567, branch `muse/567`, clone `/home/simon/Dokumente/gabbro-muse/a567`.
Owned files only: `grammatik/Grammatik/X86/TSOHistory.lean` (new),
`grammatik/Grammatik.lean` (one additive import), this report.

## What was built

The ONE reusable target-to-`Sicht` history/view projection over the canonical
`TSOZustand` (`issueByte`, `loadByte`, `flushKern` from `Grammatik.X86.TSO`),
instantiated at `Adresse`/`Byte`, for consumers BridgeWrite573 and BridgeRead574.

Definitions (namespace `Gabbro.Grammatik.X86`):
- `histVon (s : TSOZustand) : Adresse -> List Nachricht` — committed history:
  initial `⟨0, 0, ∅⟩` plus current canonical byte at timestamp 1. Pending
  own-buffer entries are deliberately NOT in it.
- `sichtVon (s : TSOZustand) (c : Nat) : Sicht Adresse` — core `c` knows `a`
  at 1 iff it holds a pending own-buffer entry for `a`, else 0.

Theorems:
- `sichtVon_le_eins`, `histVon_mem`, `histVon_lesbar` — view bound, committed
  byte present and readable at every core view.
- `neuestens_none_kein`, `neuestens_jüngste` — buffer shape lemmas: no match
  means no entry; a match splits the buffer into older prefix, the matching
  entry, and a younger suffix free of `a` (youngest wins, proved, not assumed).
- `load_lesbar_ohne_weiterleitung` — unforwarded load reads the canonical byte,
  readable in history at its actual value.
- `weiterleitung_ist_jüngste` — forwarded load value equals the youngest
  own-buffer match, with the split to prove it.
- `issue_hist_bleibt` — issue is globally invisible (history pointwise unchanged).
- `spülen_baut_frische_nachricht` — flush makes timestamp 2 `Frisch` for the old
  history and the flushed value `Lesbar` in the new history.
- `fifo_hist_konsistent` — two issues plus flush: older value readable (via
  `fifo_reihenfolge`).
- `hS2`, `hS3`, `h_schritt2`, `h_flush` — concrete same-core two-issue/flush
  computation witnesses.
- `hist_zerreissen` — tearing reuse of `paket_reisst` on the above.
- `fremd_weiterleitung_unsichtbar` — REFUSAL: fence-ready core 0 coexists with
  core 1 forwarding `7` over canonical `0`, with NO message for `7` in history.
- `hist_zeuge_gelenk` — JOINT WITNESS: reached (`TSOErreichbar sbStart sbNach2`),
  two-core, memory-changing flush, both stale loads, plus history readability
  of the flushed value.

Axioms: every theorem depends at most on `[propext]` (several on nothing,
one on `[propext, Quot.sound]`) — subset of the standard goal axioms.
No `sorry`/`admit`/`axiom`/`native_decide`. No premise has type `Prop`;
every premise is used (checked by hand per theorem).

Last `./lean-bau` result line: `Build completed successfully (428 jobs).`
(`./lean-probe` on the module: 0 errors.)

## Stable producer interface (for 573/574)

Producers: `histVon`, `sichtVon`.
Consumer facts: `histVon_lesbar` (goal shape: `Lesbar` at actual values),
`spülen_baut_frische_nachricht` (fresh timestamp 2 + new readable message —
the per-access `wahl`/`neu` seed for `SchrittW`), `weiterleitung_ist_jüngste`
+ `neuestens_jüngste` (forwarding decomposition), `issue_hist_bleibt`
(silent-issue justification), `fremd_weiterleitung_unsichtbar` (why foreign
buffers never enter the committed history), `hist_zeuge_gelenk` (joint shape).

Measurable next integration: 573 proves a `SchrittW` write leg consuming
`spülen_baut_frische_nachricht` + `fifo_hist_konsistent`; 574 proves the read
leg consuming `load_lesbar_ohne_weiterleitung` + `weiterleitung_ist_jüngste`.
Both reuse `hist_zeuge_gelenk` as the inhabited target run.

## Open / CUTS (in-file, complete)

Address/Byte is intermediate only: no typed-carrier W/GX mapping, no
multi-byte atomicity, no LOCK RMW, no per-access `SchrittW` construction, no
G-step access decomposition, no run induction (consumers' work). Timestamp
discipline is projection-local. No fairness/timing/device claims. No new
executor — all TSO facts reused, none duplicated (checked against
`TSO.lean`, `FenceDrain.lean`, `ObservationProjection.lean`: no overlap —
FenceDrain owns drains, ObservationProjection owns pilot-step observation,
this module owns history/view projection).

## Task feedback

Nothing in the task was wrong. One note: the `sb` witnesses issue on two
different cores, so the tearing example needed its own same-core pair
(`hS2`/`hS3`) — built, computed by `rfl`, no duplication of the TSO model.
