# MUSE-REPORT-51 (lane 51, REFERENCE FIXTURE attempt B of 2 -- COMPLETE)

## What was done

New file `grammatik/Grammatik/ReferenzB.lean`, wired into the build as an
import of `grammatik/Grammatik.lean`. All in namespace `Gabbro.Grammatik`,
English only, no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`,
`./lean-bau` green for the whole project (43 jobs).

1. Declaration `refD` (kept from the first attempt): `Tab = Unit` (one
   table `konto`, `count = 2`, one field `()` of type `.int 0 100`),
   `Lock = Unit` (one lock `m`), `braucht () = [.inl ()]`,
   `geteilt = true`, `Fn = Bool` (`einzahlen = true`, `lies = false`).
   Signatures: `refSigEin` (`params [.int 0 10]`, `erg none`, `haelt [()]`,
   writes) and `refSigLies` (`params []`, `erg (some (.int 0 100))`,
   `haelt [()]`, no writes).
2. Contracts: `einzahlen` requires `true`, ensures `old(konto[0]) <=
   konto[0]`; `lies` requires `true`, ensures `result = konto[0]`.
   Bodies: `refRumpfEin` is `konto[0] := 100; call lies; ret`, `refRumpfLies`
   is `ret konto[0]`. Program `refP`; oracle `refO` with `refO_gut`;
   start memory `refSp0` (both slots `0`).
3. F-machine run from `RufStartF refP refSp0 initB` (thread 0 runs `lies`,
   thread 1 runs `einzahlen 7`): step A `nimmt` (`refSchrittAF`), step B
   writing `blatt` `konto[0] := 100` under the STORED `refRho7`
   (`refSchrittBF`), step C `ruf` of `lies` (`refSchrittCF`), step D
   `rueck` with value `100` through the READ world (`refSchrittDF`).
   Proof pattern follows `schritt1F`/`schritt2F`/`schritt3F` in
   `RufMaschineF.lean`; order differs (write before call) because the kept
   `refP` puts the write first in the `einzahlen` body.
   - `refB_erreicht : RufErreichbarF refP refO 0 (RufStartF refP refSp0
     initB) MB` (via `refM0F_start` rewrite, as `reach3F_start`).
   - `refB_schreibt : MB.speicher.slots () 0 () ≠ refSp0.slots () 0 ()`
     (slot `0 -> 100` via `storeSlot_hit`, as `refPCschreibt`).
   - `refB_schreibt_zeuge`: joint existential over `MB` (reachability +
     memory move; non-degenerate: table written, four reached steps).
4. PC run from `GenStart refSp0` over `refB_prog` (thread 1: `take`,
   writing `leaf`; thread 0 rests): `refB_pc_take` lands definitionally
   on the existing `refPC1pre`; `refB_pc_leaf` fires the writing leaf at
   the advanced counter.
   - `refB_pc_erreicht : PCReach refP refO 0 refB_prog (GenStart refSp0)
     refPC2 refB_pc2`.
   - `refB_pc_schreibt` (reuses `refPCschreibt_zeuge`).
   - `refB_pc_schreibt_zeuge`: joint existential over machine + counter.
5. The section-5 D-machine run is KEPT as the documented negative result
   (`refReachC`: `nimmt`, writing `blatt`, `ruf`; no `rueck`).

## Exact names of new definitions/theorems (F + PC targets)

`initB refM0F refFrei0F refSelf0F refRang0F refM1F refSchrittAF refReachAF
refM1Fkopf refM1Fhaelt refM2F refSchrittBF refReachBF refM3F refM2Fhaelt
refSchrittCF refReachCF refCallerFF refV100back MB refRetLies
refRetLies_orte refM3Frho refM3Frest refSchrittDF refReachDF refM0F_start
refB_erreicht refMB_slot refB_schreibt refB_schreibt_zeuge refB_prog
refB_pc1 refB_pc2 refB_pc_take refB_pc_leaf refB_pc_erreicht
refB_pc_schreibt refB_pc_schreibt_zeuge`
(plus the kept first-attempt names `refD refP refO refO_gut refSp0`,
`refM0B..refM3B`, `refReachA/B/C`, `refProgB refPC0 refPC1pre refPC2
refPCschritt refPCschreibt refPCschreibt_zeuge`.)

## Last `./lean-bau` result line

`Build completed successfully (43 jobs).` with
`== 0 error line(s) in the COMPLETE output`.
`./lean-probe grammatik/Grammatik/ReferenzB.lean`: `0 error(s)`.
Every `#print axioms` in the file reports only
`[propext, Classical.choice, Quot.sound]`.

## What remains open

Nothing from the task: all five items are delivered (`refD`/`refP`/
`refO`/`refO_gut`/`refSp0` kept; `refB_erreicht` with `ruf`, writing
`blatt`, `rueck`; `refB_schreibt`; `refB_pc_erreicht`/`refB_pc_schreibt`
from `GenStart`; both `_zeuge` companions). Open by design (see CUTS):
no contract discharge connects `rueck` events to `ReqAmEintritt`/
`EnsAmRueck` on either machine.

## Notes on the task (reviewer follow-up)

- The diagnosis was correct: both `rueck` blockages were artefacts of
  `RufMaschineD`. On `RufMaschineF` the same bodies go through with the
  same `rfl`-style proofs: `hpop : ... = [refCallerFF] := rfl` (the
  suspended caller keeps its START entry world `refSp0.welt []`),
  `hv : refV100back = ... := rfl` (value computed from the post-write
  slot through the read world `ErgExpr.orte refRetLies = [Sum.inl ()]`).
  One naming correction of mine along the way: the caller frame's `s0`
  is the start world, not the call-time world (that is the callee's
  `s0`); mistaking them reproduces D blockage (1) on any machine.
- Order deviation: F proves `ruf, blatt, rueck` (callee writes); this
  fixture proves `nimmt, blatt, ruf, rueck` (caller writes first) because
  the kept `refP` puts the write before the call. All three required
  step kinds are present; the `blatt`/`ruf`/`rueck` proofs follow the
  `schritt1F/2F/3F` argument shapes.
- `refB_pc_schreibt` reuses `refPCschreibt_zeuge` (same machine
  `refPC2`, same inequality) rather than re-proving; the joint
  existential `refB_pc_schreibt_zeuge` adds reachability + counter.
- No universal premise over program syntax was added, so rule 13 needs
  no companions beyond the two ZEUGE targets, both delivered with
  non-degenerate witnesses (written table, multi-step reached runs).
