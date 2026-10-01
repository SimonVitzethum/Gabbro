# MUSE-REPORT-337: Reviewed organisation plan A3 — ShiftLogic

Lane 337, work allocation A3 (`dokumente/x86/WORK-ALLOCATION.md`), reviewer 375.
Branch `muse/337`, clone `/home/simon/Dokumente/gabbro-muse/a337`.

## What was done

New file `grammatik/Grammatik/X86/ShiftLogic.lean` (467 lines) plus one
additive import line at the end of `grammatik/Grammatik.lean`. Only owned
paths touched; no source/checker/Spec/goal/emitter/doc/friend-reserved file
edited.

The file is an EXTENSION layer over the real canonical vocabulary, not a
second evaluator:

- Reused, never redefined: `shlB`/`shrB`/`sarB`/`andB`/`orB`/`notB`,
  `and64`/`or64`, `SchiebeGueltig`/`LogikGueltig`/`SchiebeNachweis`
  (`Ganzzahl.lean`); `sint`/overflow characterisation (`FlagBeweis.lean`);
  `write64`/`read64`/`zeugenSpeicher` (`Speicher.lean`); the f64 model
  (`Gleitkomma.lean` via `Gleitprofil.lean`). The `Befehl` type and the
  `schritt` function (14 pilot forms) are untouched.
- New definitions: `negW`, `negTrag`, `negUeberlauf`, `NegGueltig`,
  `negWf` (§1 NEG with fully defined flags, AF as nibble borrow via
  `afSub`); `shlTrag`/`shrTrag`, `shlUeberlauf`/`shrUeberlauf`/
  `sarUeberlauf`, `shlNachweis`/`shrNachweis`/`sarNachweis` (§2 per-shift
  evidence over the reused values and the reused `SchiebeGueltig`);
  `logikFlags`, `andW`, `orW` (§4 width-correct logic snapshots);
  `negDrei`/`negEins`, `shiftSondenSpeicherNach`, `ShiftOp`,
  `shiftOpWert` (§§5–7).
- New theorems: `negW_ist_sub`, `negWf_gueltig`, `negTrag_heisst`,
  `negUeberlauf_heisst`, six `...Nachweis_eins/ohne_eins` validity
  theorems (every premise used: `h` computes the `Option` overflow in
  the `eins` case and discharges `none`/`≠ 1` in the `ohne_eins` case),
  `schiebeZaehler_periode_schmal`, `shrB_b64_breite_ist_null`,
  `sarB_b64_breite_ist_null`, `probe_zaehler_ueberlauf`,
  `negB_b64`, `andW_wert`, `orW_wert`, `andW_b64_flaggen`,
  `orW_b64_flaggen`, `probe_logik_schmal`, `probe_neg`,
  `sdiv_ist_kein_sar`, `float_sub_self_kein_null`,
  `staerke_braucht_bereich`, `shift_maskiert_speicher_zeuge`,
  `shiftOpWert_routen`.

## Task direction coverage

- Target direction (SHL/SHR/SAR/AND/OR/NOT/NEG, count mod 64/32,
  per-op flag facts): §§1–4, §7.
- Witness (shift with masked count plus flag read changing memory):
  `shift_maskiert_speicher_zeuge` — `1 << 66 = 4` (masked count 2),
  `shlNachweis` carry `false`, result `4`, joint with a real
  `write64`/`read64` roundtrip through `zeugenSpeicher` that changes
  byte 0 (`0x00` → `0x04`). Nonzero word, memory observably changed.
- Refusal (oversized-count behaviour pinned): `probe_zaehler_ueberlauf`
  (`shlB .b64 1 65 = 2`, `shrB .b64 8 66 = 2`, `sarB .b8 0x80 39`,
  `shlB .b32 1 33 = 2`) plus the width-is-null theorems.
- Refusal (`x - x -> 0` on floats refused): `float_sub_self_kein_null`
  (NaN − NaN stays NaN, NaN ≠ +0, over the binary64 model — no float
  width guessed: `Ty.fl` is binary64, f32 bridge untouched).
- Refusal (signed division vs shift): `sdiv_ist_kein_sar` at target
  level (`sarB` floors −3 to −2, `divS` truncates to −1), complementing
  `StaerkeReduktion.sdiv_kein_shift` at source level. Not a peephole.
- Policy (no strength reduction without range evidence):
  `staerke_braucht_bereich` (unchecked shift ≠ product at `2^63 << 1`);
  the consumer gate is the existing checked `shlW_keinUeberlauf`.

## Verification

- `./lean-probe grammatik/Grammatik/X86/ShiftLogic.lean`: 0 errors.
- `./lean-bau`: Build completed successfully (386 jobs), green.
- `./lean-probe grammatik/Grammatik/Zielsatz/BeweisAtomar.lean`: 0 errors;
  `gabbro_ziel` depends on axioms `[propext, Classical.choice,
  Quot.sound]` — exactly the standard set, unchanged.
- Every `#print axioms` in the file reports subsets of the standard set.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (grep shows only
  the required `#print axioms` lines). No `Prop`-typed premise. No new
  `Befehl`/`schritt`/checker/goal definition.

## Semantic mismatch found while resolving names (reported, not invented)

- `Ganzzahl.lean` already defines `andB`/`orB`/`notB`, `and64`/`or64`,
  `shlB`/`shrB`/`sarB`, `SchiebeGueltig`/`LogikGueltig` and
  `schiebeZaehler_periode_b64`. This file reuses all of them; an early
  draft duplicated the 64-bit period theorem and the duplicate was
  removed. `Wort.lean` already owns the name `negB` (sign BIT test), so
  the NEG value operation is named `negW` — reviewers please note the
  near-collision is deliberate and documented.

## Honestly open (see CUTS in the file)

- Count-mask widths, NEG AF, shift CF/OF corners past the width, and the
  zero-count flag preservation (value identity proved, no snapshot
  claimed there) are stated executable semantics, not verified against
  silicon. SAR-by-1 overflow is constantly `false`; its operand
  parameter is carried only for uniform dispatch (`_x`).
- No `Befehl` extension, no `schritt` change, no codec, no TSO/GX
  bridge, no source correspondence, no cost/time transfer, no
  final-image acceptance. Full final-byte/source/hardware correspondence
  stays OPEN. The shared IR (lane 287) is still pending; §7 names the
  exact evidence a future shift/logic form must present, nothing more.
- No `_zeuge` companions: no theorem here quantifies over program
  syntax (`Vertrag`/`Stmt`/`Expr`/…), and the task names no `ZEUGE:`
  target; the joint memory witness above is the task's Witness
  deliverable. If the merge gate wants per-theorem `_zeuge` anyway,
  that is a concrete repair request I will implement.
