# MUSE-REPORT-274: TSO to existing concurrency model

*Lane 274, branch `muse/274`, model opencode-go/muse-spark-1.3-contributor.
Docs-only design task. No Lean file added, no Lean/cargo build run
(docs-only: file/claim checks instead, per wave rules). Tree was clean at
start; only two files are touched by the final commit.*

## What was delivered

- `dokumente/x86/TSO-GX-BRUECKE.md` (owned file): the exact generic
  per-access x86-TSO to W/GX refinement obligation against the REAL
  definitions, with file:line references checked against this tree.
- This report.

## Work done

Read, in full: `X86/Typen.lean` (87 lines), `Speichermodell/Sicht.lean`
(717), `MaschineW.lean` (690), `GXMaschine.lean` (389), `AtomarW.lean`
(298), `AtomarLauf.lean` (431), `DRF.lean` (388), `AtomarFortschritt.lean`
(162), `Zielsatz/BeweisAtomar.lean` (613), `CTicket.lean` header; read the
load-bearing parts of `Zielsatz/Spec.lean` (atomic-rely block :2077-2319,
assumption block (5), `FortschrittG` :1828, `KernPlan` :1858,
`ZeitAb` :1896), `RufMaschineG.lean` step rules (`blatt` :265,
`dannBlatt` :354, `dannLocks` :715, `dannExchange` :1933,
`dannGleit` :1957), `RennfreiVoll.lean` access predicates (:499-523),
`Orakel` (:454), `KoerperGutSA` (AtomarRec.lean:39), `HavocA`
(AtomarSem.lean:49), `FussSX` (AtomarReplay.lean:29). Every file:line
cited in the bridge document was re-verified by grep after writing;
three wrong line numbers found that way were corrected (KernPlan,
HandlerVon, dannGleit).

## Findings (exact names)

1. One G step is multi-access: `dannExchange` reads
   `.inr g :: neuE.orte` then writes `g` in one step (RufMaschineG.lean:1933);
   `blatt`/`dannBlatt` run a whole leaf via `execStmt`. Bridge MUST be
   per-access; block-atomic mapping is incomplete (concrete interleave
   trace in the doc).
2. Strategy chosen: per-access forward simulation x86-TSO → W
   (direction x86 ⊆ W), then `schwach_ist_gX` → GX, then existing legs.
   Rejected: G-step-as-transaction (refuted + breaks `SperrWechselGX`
   boundaries).
3. Reuse points with directions checked: `PrueferX`/`AkzeptiertSpecX`
   (`FussSX` over `GeteiltV`), `NutzerPflichtA` (`KoerperGutSA` vs every
   `HavocA (GeteiltA ...)` — note duty is over `GeteiltA`, not `GeteiltV`;
   `koerperGutSA_mono` narrows), `SchwachX` as landing zone (universal
   `ord` forces order-parametric simulation — obligation O-ord),
   `RennfreiBisGA`, `SperrWechselGX`/`SperrSichtGX` (GX-step linearisation,
   ticket `tritt`/`gibt`), `ZeitAbX` (needs O-time transfer),
   `FortschrittG` (needs O-stutter + fairness assumption),
   `KernHaltEA` (needs O-irq + buffer drain at handler entry),
   `FolgeG` (free; control-flow constraint recorded for lane 275).
4. Two places where the bridge must CONSTRAIN flushing, not admit it:
   O-spawn (thread-start drain + view join) and O-drain (foreign/device/
   `sichtbar` reads need MFENCE so assumption (5)'s "last write" holds).
5. Safe-direction alignments named, not hidden: W's non-FIFO writes ⊇ TSO
   FIFO; W's `seq_cst`-as-release/acquire ⊇ x86 LOCK lowering; promise-free
   no-LB matches TSO. MMIO/DMA excluded (O-mmio); infinite stutter needs a
   fairness assumption; starvation stays NOT CLAIMED consistently.
6. Lemma dependency order D-tso/D-access/D-lower/L-read/L-write/L-view/
   L-step/L-run + legs is proposed as wave-B work; O-access (~70 rules,
   pattern `exchange_liest_schreibt`) flagged as the largest work item.
7. No impossibility blocking the strategy; §6 lists nine named
   mismatches, none requiring a goal-statement change.

## CUTS / open

- No TSO machine, access extraction, lowering map or simulation lemma is
  proved here — by task design (docs-only).
- `./lean-bau` NOT run (no Lean touched); `./cargo-pruef` NOT run (no Rust
  touched). Last full check outcome: none required; claim checks via grep
  all pass.
- Anything in the task I believe is wrong: nothing. The "no toy proof"
  and "no goal change" constraints were satisfiable as stated.

## Commits

- This report + `dokumente/x86/TSO-GX-BRUECKE.md`, one commit.
