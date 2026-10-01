# MUSE-REPORT-574: Projected TSO loads to source W reads

## What was done

New file `grammatik/Grammatik/X86/BridgeRead.lean` (~470 lines) plus the
additive umbrella import in `grammatik/Grammatik.lean`. It consumes the
ACCEPTED interfaces of TSOHistory567 (`histVon`/`sichtVon`,
`load_lesbar_ohne_weiterleitung`, `weiterleitung_ist_jüngste`,
`histVon_lesbar`, `sb*`/`hS*` witnesses, `sb_flush_aendert_speicher`)
and SourceMemory570 (`RepSlot`, `zahlWort_wortZahl`, `read64`,
`witD`/`witSigma`/`witHT`), plus real `Sicht` rules (`Lesbar`) and real
W vocabulary (`RufMaschineW`, `NachrichtW`, `TraegerGleich`, `LiestG`,
`mitSpeicher`, `HavocA`). No source checker/Spec/goal/emitter change, no
new executor, no second IR, no guessed ISA.

Definitions: `achtBytes` (8-byte `Fin 8` assembler), `ladeWort8`
(8 real `loadByte`s assembled; `none` if any byte unreadable),
`brueckenRahmen`/`brueckenFaden`/`brueckenG`/`brueckenW` (minimal
witness G/W machines over `witD`).

Theorems (all premises used; `Lesbar` derived, never assumed):

- `lesbar8_hit` -- one byte of the `lesbar8` permission.
- `ladeWort8_ohne_weiterleitung` -- committed group = canonical
  `read64` word (no pending entry on any footprint byte).
- `ladeWort8_aus_lesungen` -- group assembles from eight loaded bytes.
- `ladeByte_ist_jüngste` -- per-byte youngest-forwarding split
  (from accepted `weiterleitung_ist_jüngste`).
- `gruppenwert_rep` -- committed group parses via `wortZahl` to exactly
  the source slot value (representation roundtrip).
- `wLesbar_aus_gruppe` -- COMMITTED W-read simulation: value identity
  plus the `SchrittW.lies` consequent (`Lesbar` at the actual message
  with `TraegerGleich`) for every recording G step, from projection
  facts + explicit history/view-link premises (`hMem`, `hProj`, `hTs`,
  `hTraeger`).
- `wLesbar_aus_weiterleitung` -- FORWARDED W-read simulation: group
  assembly, per-byte youngest splits, value link, same `lies`
  consequent. The cross-side value identity (`hWert`) is an explicit
  premise owned by the lowering certificate / write side (lane 573).
- `havoc_erhaelt_gruppenwert` -- atomic-rely leg: a group-read value at
  a carrier outside `T` survives every `HavocA` environment (the exact
  rely class of `NutzerPflichtA`).
- `stale_lesbar_sb` (positive): stale committed byte is `Lesbar`.
- `gruppe_reisst_fremd` (refusal): forwarding core sees `(1,1)`,
  foreign core sees torn `(1,0)` after a partial flush, with joint
  reachability and memory change.
- `gruppe_fremd_weiterleitung_uneinig` (refusal): fence-ready core sees
  committed zeros while the forwarding core sees the pending `1` --
  local drain is no foreign drain (OBS-5 shape).
- `wLesbar_aus_gruppe_zeuge` -- JOINT witness: reached two-core state
  `sbGespült` (two issues, memory-changing flush), represented slot
  value 0 at address 8, timestamp-0 message with covered view, plus
  the simulated read, reachability, the flush change, and the
  table-writing function.

## Last build result

`./lean-bau`: `Build completed successfully (441 jobs).`
`./lean-probe grammatik/Grammatik/X86/BridgeRead.lean`:
`== 0 error(s) in the COMPLETE output`.
Axioms per theorem: `[propext]` or `[propext, Quot.sound]` only --
subset of the goal standard, no `sorry`/`admit`/`axiom`/`native_decide`.
Goal statement files untouched (only additive import).

## What remains open (next integration)

- No full `SchrittW`/`RufSchrittW` derived (the G step is the lowering
  consumer's); `schwach_ist_gX` therefore cited, not applied. First
  consumer step: feed `wLesbar_aus_gruppe.2`/`wLesbar_aus_weiterleitung.4`
  into a real `SchrittW.lies` field for an executed reading program,
  then apply `schwach_ist_gX` to land in GX.
- Forwarded GROUP values need the lowering certificate's `hWert`;
  mixed committed/forwarded footprints have no value simulation.
- Typed carriers beyond one `.int`-as-word slot, run induction to W
  runs, `valX86_sound`, and the source-to-final-bytes closing theorem.

## Producer/consumer interface (stable)

Producer (this lane): `ladeWort8`, `ladeWort8_ohne_weiterleitung`,
`ladeWort8_aus_lesungen`, `gruppenwert_rep`, `wLesbar_aus_gruppe`,
`wLesbar_aus_weiterleitung`, `havoc_erhaelt_gruppenwert`.
Consumer (validator/lowering): assume only these plus `RepSlot`/checked
`repOk` Bools; discharge `hWert` per lowering; establish `hProj` from
the run relation. Measurable next check: one executed reading program
whose `SchrittW.lies` field is exactly `wLesbar_aus_gruppe.2`.

## Task remarks

Nothing in the task was found wrong. Two readings were decided and are
recorded: (1) "instead of assuming Lesbar" is honored by deriving the
`lies` consequent from membership + view-bound premises, with the
cross-side value identity explicit (`RepSlot` for committed, `hWert`
for forwarded); (2) `schwach_ist_gX` is not reused yet, per its own
guard -- no real W execution is derived here, only its read consequent.
Tactic note: this tree has no Mathlib tactics (`tauto`,
`interval_cases`, `fin_cases`, `le_refl` unavailable); proofs use core
tactics, explicit conjunction projections, and `decide` on concrete
states.
