# MUSE-REPORT-1257: Pipeline spills — splice save/reload at split points, callee-saved and arguments

## What was done

New file `grammatik/Grammatik/X86/PipelineSpillSplice.lean` (~1150 lines,
namespace `Gabbro.Grammatik.X86.PipeSpillSplice`), plus one
`import Grammatik.X86.PipelineSpillSplice` line appended to
`grammatik/Grammatik.lean`. Follow-up of lane 1191 (`PipelineSpill.lean`):
split points name a position/slot/register/direction, splicing inserts
lane 1191's save/reload fragments there; the closing theorem preserves the
source meaning and the frame privacy; callee-saved/argument handling reuses
`PipelineCalls.lean` over the `Stapel` layout.

Definitions: `SpleissRichtung`, `SpleissPunkt`, `spleissFrag`,
`spleissEins`, `spleissSeg`/`spleissMehr`, `spleissSortiert`,
`spleissPlanOk`, `spleissRufOk`, `rufRettFrag`/`rufHolFrag`,
witness values `spleissPts0`, `spleissPtsFern`, `spleissPtsUnsortiert`,
`spleissPtsAdr`, `spleissR1`, `spleissB1`, `spleissS0`.

Main theorems: `spleissEins_gestalt`, `spleissFrag_gerade`,
`lauf_praefix`, `spleiss_save_fremd` (save touches only `c.adr`),
`spleiss_load_fremd` (reload touches only `c.adr`/dst),
`spleissPlan_spill/pos/sortiert/saveReg`, `spleissMehr_nil/einz`,
`spleiss_paar_rundreise` (save→middle→reload value round-trip with
explicit middle-segment run and slot-byte preservation premises),
`spleiss_haelt_bedeutung` (fetched run with world+env represented,
slot-vs-table privacy, pairwise slot separation, slot-vs-extent
separation, per-point fragment admission),
`spleissRuf_ruf/spill/unten`, `spleissRuf_spillGerettet`
(`spill_gerettet_getrennt`), `spleissRuf_spillStapel`
(`bereich_getrennt`), `spleissRuf_spillArg`, `spleissRuf_rettetAlle`,
`spleissRuf_argTraeger`, `rufRett_lauf`/`rufHol_lauf`, eight general
refusals (`spleiss_verweigert_pos/unsortiert/adr/tabelle/aussen/
kollision`, `spleissRuf_verweigert_rot/hoch`), one positive and eight
refused splice probes (position and address-register also through the
refusal theorems), call-boundary positive/refused probes, joint
witnesses `spleiss_haelt_bedeutung_zeuge` (witness program, rows
7→35, 9→6) and `spleiss_paar_rundreise_zeuge` (reached
memory-changing save/reload of `42` beside writer program `zeugenU`).

## Verification

- `./lean-probe grammatik/Grammatik/X86/PipelineSpillSplice.lean`:
  `0 error(s)`, no warnings.
- `./lean-bau`: `Build completed successfully (644 jobs)`.
- `#print axioms`: every new theorem depends at most on
  `[propext, Classical.choice, Quot.sound]` (standard); all defs and
  all `decide` probes are axiom-free.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no file edited
  except the owned import line; optimiser files untouched.

## What remains open (also in CUTS)

- Lane 1227's homing (`PipelineSpillHoming.lean`) is not merged in
  this tree: split points are bare positions, homing is not decided here.
- The splice validator inherits `slots.Nodup` from lane 1191, so a
  same-slot save/reload pair is proved per pair
  (`spleiss_paar_rundreise`), not plan-admitted.
- Discharging a middle segment's non-interference (`hmid`,
  `hslotmid`) and agreement of declared extents `daten` with placed
  tables are producer/deployer obligations, as documented.
- No full loaded-image connection of spliced bytes (re-decoding after
  splicing), no TSO freshness beyond the reused vocabulary,
  pilot-only shapes.

## What I believe is wrong in the task

- The task says "follow-up of lane 1227 (`PipelineSpillHoming.lean`)"
  and "splice lane 1191's save/reload fragments at the split points":
  the homing file does not exist in this checkout, so there are no
  homing-decided split points to splice at — positions are defined
  here instead. If lane 1227 lands later, `SpleissPunkt.pos` wants to
  be constrained by its homing output.
- The task's "correctness theorem in the style of
  `pipeline_correct_entry`" is delivered as `spleiss_haelt_bedeutung`
  in the style of lane 1191's `spill_haelt_bedeutung` (the direct
  precedent in this follow-up chain), reusing `pipeline_correct`
  rather than the image/entry stack — the loaded-image connection of
  spliced bytes is recorded OPEN rather than claimed.
