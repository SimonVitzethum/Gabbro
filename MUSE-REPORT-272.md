# MUSE-REPORT-272: Pilot instruction execution

Lane 272 (wave A). Owner file: `grammatik/Grammatik/X86/Ausfuehrung.lean`
(869 lines, 26 defs, 69 theorems). Plus the one allowed umbrella line
`import Grammatik.X86.Ausfuehrung` in `grammatik/Grammatik.lean`.
Nothing else touched. No new source features, codes, gift/example numbers,
CLI switches, or MARKE_EMIT changes.

## What was built

`schritt : Decodiert -> Zustand -> Option Zustand` steps every one of the
14 canonical `Befehl` constructors over the real shared helpers:

- `laengeOk` gates on decode length 1..15 (checked data, not trusted
  metadata); `ripNach` advances RIP before any relative displacement is
  applied; `dispWort` sign-extends the int32 displacement via lane 270's
  `sext .b32`; `effAddr` is base register plus extended displacement.
- MOV preserves flags (`schrittRegister` carries `s.flags`).
  ADD/SUB/XOR reuse lane 270's `add64`/`sub64`/`xor64` flag snapshots;
  CMP runs `sub64` for flags and writes no operand.
- Loads/stores use lane 271's `read64`/`write64`; failure is `none`.
- `jump32`/`jumpIf32` target the post-decode address (`bedingung`
  from lane 270 for the condition); `call32` pushes the post-decode
  address then transfers; `push64` reads the source BEFORE decrementing
  rsp (so `push rsp` stores the old top); `pop64` into rsp takes the
  loaded word and discards the increment; `ret` pops the target.
- `lauf` folds a decoded list; failure is loud `none`, never a halt.

Equations: one per form, split success/refusal for the five memory forms
(`schritt_load64_erfolg/verweigert`, `schritt_store64_erfolg/verweigert`,
`schritt_push64_erfolg/verweigert`, `schritt_pop64_verweigert`,
`schritt_call32_erfolg/verweigert`, `schritt_ret_erfolg/verweigert`),
taken/untaken for `jumpIf32`, rsp/other-destination for pop
(`schritt_pop64_top/reg`), plus generic `schritt_laenge_verweigert`.
Frames: memory preservation for all non-storing forms, eight-byte
footprint frames plus permission preservation for store/push/call
(reusing lane 271's `write64_rahmen`, `write64_erhaelt_berechtigungen`),
register/flag preservation per form.

Witness and probes (all `decide`-evaluated, i.e. executed semantics):
`zeuge_speicher_aendert_sich` runs mov/store/load and reaches rbx = 42
with the memory byte observably changed 0 -> 42;
`probe_sprung_genommen/nicht_genommen` (je taken to 4114 / falls
through to 4098); `probe_ruf_kehr` (call+ret round trip lands
(4101, 8192)); `probe_schub_liest_alt` (push rsp stores old top);
`probe_nimm_rsp_gewinnt` (pop rsp takes loaded word 7).

## Last full check

`./lean-bau`: `exit 0; 0 error line(s)`, `Build completed successfully
(369 jobs)`. Every `#print axioms` reports exactly
`[propext, Quot.sound]`. No `sorry/admit/axiom/native_decide/unsafe`
(the 18 grep hits are all `#print axioms` lines).

## Open / gaps (see also CUTS in the file)

Decoder/encoder, per-access TSO refinement, source correspondence,
ABI/image/entry, timing/progress/cost, whole-executable acceptance,
narrow-width instruction forms. `lauf` is sequential only.

## Notes for the coordinator

- The task's dependency (lanes 270/271 reviewed and integrated) held:
  both plus 273 were already merged in this base.
- Toolchain finding (not a task defect): struct literals/updates
  `{ x with a := ..., b := ... }` fail to parse in Lean 4.34.1 when a
  newline follows a field-separating comma ("unexpected identifier;
  expected '}'"). Bisected from the canonical shape down to a 6-line
  reproducer; every literal in the file is therefore single-line.
  Dotted constructors and dot-access in field values are fine on one
  line (also verified by reproducer, counter to my first hypothesis).
- Nothing in the task statement looked wrong. One naming note:
  `schrittPopTop`/`schrittPopReg`/`schrittCall`/`schrittRet` take the
  stack register as an explicit argument so lemma statements stay
  parser-safe; all call sites pass `Register.rsp`.
