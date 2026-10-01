# MUSE-REPORT-286: Width-aware IEEE target data and f32 bridge evidence

Lane 286, branch `muse/286`, model opencode-go/muse-spark-1.3-contributor.
Owned files only: `grammatik/Grammatik/X86/Gleitprofil.lean` (new),
one additive import line in `grammatik/Grammatik.lean`, this report.

## What was done

New file `grammatik/Grammatik/X86/Gleitprofil.lean` (573 lines), built
skeleton-first (<=60 lines, probed green, committed) then one checked
increment at a time. Full `./lean-bau`: exit 0, 0 errors, 369 jobs,
`Build completed successfully`.

Contents, by section:

1. **MXCSR target profile** (§0): `MXCSR` (`BitVec 32`), `mxcsrBit`,
   `mxcsrRundungRNE` (RC bits 13-14 clear), `mxcsrMaskenAlle` (bits 7-12),
   `mxcsrGueltig` (RNE, FTZ bit 15 off, DAZ bit 6 off, all masks set).
   Theorems: `mxcsr_standard` (`0x1F80`), refusals `mxcsr_ftz_verweigert`
   (`0x9F80`), `mxcsr_daz_verweigert` (`0x1FC0`),
   `mxcsr_runde_unten_verweigert` (`0x3F80`), `mxcsr_maske_verweigert`
   (`0x0F80`), all by `decide`.
2. **Per-context state** (§1): `FPKontext` (owns its MXCSR, no global),
   `kontextReset`, `sichere`/`stelleHer` as pure data movement (software
   save/restore = user logic), `sichere_stelleHer`, `stelleHer_sichere`,
   `kontextReset_gueltig`, `kontext_nicht_global` (valid and refused words
   coexist as two contexts).
3. **Sticky-flag gap** (§2): `mxcsr_sticky_egal_gueltig`
   (`0x1FBF`/`0x1F80` both valid), `mxcsr_sticky_egal_verweigert`
   (`0x9FBF`/`0x9F80` both refused) -- the check ignores bits 0-5;
   sticky semantics stays unmodelled (CUTS).
4. **Pattern helpers** (§3): `muster32`/`bites32` (`BitVec 32`),
   `muster64`/`bites64` (canonical `Wort`) over kernel-computable `GBits`
   (no opaque Lean `Float`). Width facts `f32_breite32`, `f64_breite64`.
   Inverse facts both directions both widths: `bites32_muster32`,
   `bites64_muster64` (need `wf`, via `zuBits_lt` + `ausBits_zuBits`),
   `zuBits_ausBits32`/`zuBits_ausBits64` (need only the bound, proved via
   two-level Nat decomposition + `omega` over literal divisors),
   `muster32_bites32`, `muster64_bites64` (via `BitVec.eq_of_toNat_eq`).
   Generic `ausBits_wf` (every dense format, hence f32/f64).
5. **Width arithmetic** (§4): `fadd32/fsub32/fmul32/fdiv32`,
   `fadd64/fsub64/fmul64/fdiv64` wrapping the existing IEEE model
   (named `f*` -- `add64`/`sub64` already belong to `X86.Wort`).
   `wf` preservation for all eight ops from `Gleitkomma.add_wf` etc.
6. **Signed zeros/subnormals** (§5): `fadd32_nullN`, `fadd64_nullN`
   (`-0 + -0 = -0`), `fadd32_subnormal`/`fadd64_subnormal`
   (min+min = next, as exact triples), `muster32_null`/`muster64_null`
   (`-0`/`+0` bit patterns).
7. **f32-vs-f64 counterexample** (§6, the centerpiece):
   `f32_rundet_16777217` (`ofInt f32 (2^24+1) = ofInt f32 2^24`),
   `f64_trennt_16777217` (the f64 pair differs), `gegenbeispiel_werte`
   (exact values `⟨2^23,1⟩` vs `⟨2^52+2^28,-28⟩` -- differing VALUES),
   `gegenbeispiel_muster` (f32 patterns coincide, f64 patterns differ),
   `quelle_gegen_f32` (source-type-aware: `gleitAusInt (2^24+1)` is the
   true integer while genuine f32 computes `2^24`). All kernel `decide`s.
8. **NaN/SSE gaps** (§7): `nan_nutzlast_offen32` (two payloads, both
   `.nan`, unequal -- classification pins no payload),
   `nan_klasse_berechnet32` (`0/0` classified, never given a payload),
   `SSEAdd32Entspricht` -- the correspondence claim NAMED and unproved;
   no theorem concludes anything about executed SSE bytes.
9. **Memory round-trips** (§8): `zehntel32_modell`/`zehntel64_modell`
   (stored patterns are the model values' bits, reusing the existing
   `zeuge_zehntel32/64`), `speicher32_rundlauf` (4-byte write/read via
   `write32`/`read32_nach_write32`), `speicher64_rundlauf` (8-byte via
   `write64`/`read64_nach_write64`) -- both nonzero (`0.1f32`/`0.1f64`)
   with `m.bytes a ≠ m'.bytes a` through `writeBytesN_hit`.

Axioms: every theorem depends on a subset of `[propext, Quot.sound]`
(verified `#print axioms` output, 0 errors). No `sorry`, `admit`,
`axiom`, `native_decide`, `unsafe`; no `Prop`-typed premise; every
premise is used. No `Ty.fl`/Spec change, no Rust, no diagnostic/gift/
example/CLI numbers, no MARKE_EMIT.

## Last build result

`./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
`Build completed successfully (369 jobs)`.

## What remains open

Everything in the file's `CUTS:` block; in particular the reviewed
width-extension work this profile prepares but does not do: a width in
`Syntax.lean` `Ty.fl`, a width dispatch in `Semantik.lean`
(`gleitRechne`/`bruch`/`gleitAusInt`/`gleitWortPasst`), per-width
`Typen.lean` values, and the binary32 correspondence rows of
`CFormenF.lean`. Sticky flags, NaN payloads, SSE correspondence,
concurrency/TSO, decoder/ABI/costs are open by design (gaps named in
§7 + CUTS, not assumed).

## Findings during the work (believed-correct, for review)

- `set_option X in` does NOT parse when a doc comment sits between it
  and the theorem (this toolchain); option first, then doc, then
  theorem parses. Cost two iterations.
- `{ s with field :=` + newline + value + `}` fails to parse in a
  structure update (single line works). Cost three scratch probes.
- `set_option maxRecDepth 100000` (+ `exponentiation.threshold 2048`
  for the `2^1074`-scale f64 case) is needed even for the small-triple
  subnormal `decide`s; same two elaboration-only options the model file
  already carries. Recorded in CUTS.
- No TARGET statement needed weakening; no extra premise was added
  anywhere (all inverse/round-trip theorems use only bound/`wf`
  premises that the proofs consume).
- Inhabitation: no theorem quantifies over program syntax
  (`Vertrag`/`Stmt`/etc.), so no `_zeuge` companions are owed; generic
  target helpers carry real boundary probes (`0x1F80`, `0x9F80`,
  `0x1FC0`, `0x3F80`, `0x0F80`, `0x1FBF`, `0x9FBF`, min-subnormal
  triples, `16777217`) and both memory witnesses change memory
  observably with nonzero patterns.
