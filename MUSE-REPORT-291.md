# MUSE-REPORT-291: Checked relocation arithmetic and byte patching

Lane 291, Lean-first tranche. Owned files only:
`grammatik/Grammatik/X86/Relokation.lean`, this report, and one additive
line in `grammatik/Grammatik.lean` (`import Grammatik.X86.Relokation`).
No Rust, no numbers minted, no other files touched.

## What was built

`Relokation.lean` (namespace `Gabbro.Grammatik.X86`), reusing only the
canonical `Byte`/`Wort`, `wortByte`/`bytesWort`, `sext`, and address
arithmetic of `Typen`/`Speicher`/`Wort`. No second image, register, or
ISA model.

- §0 Site admissibility: `RelArt` (`codeOperand`/`datenFeld`) with
  `relAnnahmeEndgueltig` constantly `false` and `relAnnahme_offen`:
  helper-level facts never admit a site. Code-operand vs data-field
  admissibility is explicitly OPEN and belongs to the checked
  image-plus-decoder proof; caller-claimed starts/kinds untrusted.
- §1 rel32 fit/encoding: `tcNat`, `rel32Passt` (signed-32 `decide`),
  `rel32Enc`/`rel32Enc64`, four little-endian `rel32Byte`s,
  `rel32Bytes`, sign-extending `rel32DecOpt`, and generic
  `rel32_rundgang` (decode of encode is `d` under exact fit bounds).
- §2 Canonical equations: `rel32_adress_gleichung`
  (`ofNat ziel = ofNat next + ofNat enc64` from `ziel = next + d`),
  `rel32_next_rip` (machine start+length reaches the Nat sum under the
  exact no-wrap premise), `rel32Fuer` with `rel32Fuer_verweigert`
  (out-of-range is `none`, never wrapped) and `rel32Fuer_trifft`.
- §3 abs64: `abs64Bytes` via canonical `wortByte`, `abs64Wort` via
  canonical `bytesWort` (wrong width is `none`), `abs64_rundgang`
  proved by exactly `bytesWort_wortByte`.
- §4 Finite patching: `patchAt` (overrun is `none`, including an empty
  patch past the end) with `patchAt_bereich` (success implies
  `off + len ≤ img.length`), `patchAt_laenge`, `patchAt_stelle`
  (site bytes exact, `[off+k]?` notation), `patchAt_rahmen`
  (outside bytes preserved).
- §5 Double patches: `disjunktStellen` (+ `Decidable` instance),
  `patchZwei` refusing overlap, `patchZwei_verweigert`,
  `patchZwei_erhaelt_erste` (first site survives a disjoint second
  patch), `patchRel32`/`patchAbs64` with `patchRel32_stelle` and
  `patchAbs64_stelle` plus width facts (4 / 8).
- §6 Concrete probes: `-5` is `FB FF FF FF` with decode-back and
  canonical-`sext` agreement; both signed-32 boundaries fit with exact
  bytes; `±(2^31)` variations refused; `rel32Fuer` refuses `2^31` and
  hits `-10`; real backward-jump address equation (`0x1005→0x1000`)
  and next-RIP probe; abs64 bytes/read-back; overlap `none`,
  disjoint exact bytes, overrun `none` — all `decide` or instances of
  the generic theorems.

## Verification

- `./lean-probe grammatik/Grammatik/X86/Relokation.lean`: 0 errors.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (369 jobs)` (one more than the 368
  baseline: the new file).
- `#print axioms`: every theorem uses only `propext`/`Quot.sound` or
  nothing — no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no new
  axiom, no `Classical.choice`. The goal theorem's axiom set is
  untouched.
- Every premise of every theorem is used (linter-silent); no
  `Prop`-typed premise; no conclusion restates a premise.
- Inhabitation: no premise quantifies over program syntax and the task
  names no `ZEUGE:` target, so no `_zeuge` is owed; the §6 probes are
  real operand/byte values over the actual helpers.

## Findings (not weakenings)

1. The modular target equation needs no wrap premises:
   machine-level `ofNat` addition is wrap-consistent on either side, so
   `hn`/`hz` were dead weight there (caught by the unused-variable
   linter) and were removed. Exact no-wrap premises live only where
   they are load-bearing: next-RIP formation (`rel32_next_rip`, each
   bound drops one `% 2^64`).
2. This toolchain's core has no `List.get?` (renamed to `List.getElem?`,
   `[i]?` notation); the file uses the new names throughout.
3. `fin_cases` is unavailable; the abs64 function-equality case split
   is explicit nested `cases` with an `omega`-closed impossible case.

## Open (not claimed)

As stated in the file's `CUTS`: site admissibility (needs checked
image + decoder), loader/linker behaviour and load bias, entry states,
per-instruction source correspondence, control-target and ABI checks,
concurrency refinement, cost transfer. Complete relocation acceptance
is explicitly OPEN/refused at helper level; no final-byte source claim
is made.
