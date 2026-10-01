# MUSE-REPORT-435: DecodingCoverage (continuous Lean proof reserve)

## Task

Lane 435: create `grammatik/Grammatik/X86/DecodingCoverage.lean` (+ one additive
X86 import in the umbrella), proving a useful canonical decoder/fetch coverage
and suffix/window congruence fact: the executable entry-byte relation derives
from the actual decoder, not from encoder round trips. Every accepted actual
pilot form with its exact length; unknown/truncated/unsupported bytes fail
closed. No claim of complete x86 coverage or a full source validator.

## What was actually open (read before writing)

- `Codec.lean` CUTS: "The general length soundness (every successful decode of
  an ARBITRARY input consumes exactly its stated length within 1..15) is
  proved only for round-trip instances (`roundtrip_len_ok`)."
- `Byteschritt.lean` CUTS: the same arbitrary-input statement "is not proved
  here"; `fetchDekodiert` checks the equation at runtime instead.
- `dokumente/x86/WORK-ALLOCATION.md:148` policy: "length from decoding only,
  never an emitter annotation." This module proves exactly that policy for the
  pilot decoder and is consumed by the closing validator (length needs no
  trusted annotation and no encoder round trip).
- No existing fact was duplicated: round trips, fetch bounds, fetch-to-decoder
  correspondence, image mapping and loaded-memory facts are reused, never
  re-proved. No second IR, executor, or mini-machine was built.

## What was delivered

New module `grammatik/Grammatik/X86/DecodingCoverage.lean` (756 lines) plus
`import Grammatik.X86.DecodingCoverage` appended to `grammatik/Grammatik.lean`.
Nothing else touched (`git diff --stat master`: exactly these two files).

Design point: inner decoder levels receive inputs shorter than the stated
`d.laenge` (their bytes exclude outer REX/opcode/ModRM bytes), so a naive
per-level length equation is false. Every level instead proves the uniform
statement `exists pre, input = pre ++ rest' /\ pre.length + OUTER = d.laenge`
with `OUTER` = 3 (reg-reg, mem), 2 (ModRM), 1 (REX), 0 (top). This composes by
prepending one level's bytes; the top level additionally gets the plain length
equation, take/drop congruence and the classification.

Definitions (2): `eintrittFenster` (loaded-image entry window through the
checked section mapping), `eintrittDekodiert` (actual decoder over that
window, capped at `fetchCap`), `decktAb` (coverage shape: all 14 `Befehl`
constructors with exact lengths 1 / 1-or-2 / 3 / 10 / 7-or-8 / 5 / 6),
`dcReg`, `dcStart`, `dcEintrittCode/Daten/Datei/Bild/Start`,
`dcAbholProg/Bytes/Speicher/Start` (witness data).

Theorems (21 + 3 witnesses):
- `parseLe32_suffix`, `parseLe32_len`, `parseLe64_suffix`, `parseLe64_len`
- `decodeRegReg_abdeckung`, `decodeMem_abdeckung`, `decodeModrm_abdeckung`,
  `decodeRex_abdeckung`
- `decode_abdeckung` (main: equation + `laengeOk` + `decktAb` + prefix split,
  decoder side only)
- `decode_fenster_kongruenz`, `fetch_fenster_kongruenz`,
  `geholt_schritt_aus_decoder` (byte-step agreement for arbitrary fetched
  bytes, reusing the existing `byteschritt` correspondence lemmas),
  `eintritt_abdeckung`
- `decode_nichts_imm_kurz`, `decode_nichts_speicher_ohne_versatz`,
  `decode_nichts_opcode_falsch`, `decode_nichts_modus_eins`,
  `decode_nichts_zweig_ohne_versatz` (all new shapes vs `Codec`, all `rfl`)
- `decode_abdeckung_zeuge`, `eintritt_abdeckung_zeuge`,
  `geholt_schritt_aus_decoder_zeuge` (joint concrete witnesses; each decodes
  real store bytes AND runs a real memory-changing step 0 -> 42 at the data
  address: plain `schritt`, loaded-image `schritt`, and `byteschritt` through
  `ausgangByte`; the fetch/entry witnesses reuse shared `zeugeSpeicher`,
  `zeugeFlags` and `ausgangByte`, nothing re-modelled).

## Checks (all green)

- Incremental `./lean-probe` after every chunk: 0 errors throughout.
- Full `./lean-bau`: `Build completed successfully (393 jobs)`.
- Goal gate: `#print axioms gabbro_ziel` = exactly
  `propext, Classical.choice, Quot.sound` (unchanged).
- Own `#print axioms`: every theorem depends only on `propext` (and
  `Quot.sound` where `omega`/`simp` arithmetic is used) — no `sorryAx`.
- Banned tactics: `grep` for `sorry|admit|axiom|native_decide|unsafe` finds
  only `#print axioms` lines. Every theorem premise is used by its proof;
  no `Prop`-typed premises.
- No Rust, emitter, checker, Spec, Bild, Typen or execution file was modified,
  so no `cargo`/emission re-measurement is owed by this lane.

## What remains open (also in the file's CUTS block)

1. No hardware correspondence (self-consistency of the pilot vs BYTE-PILOT.md
   only); no complete-x86 claim (14 forms; the rest is refused, not covered).
2. No source correspondence, no TSO/multi-byte-atomicity bridge, no
   concurrency, cost, ABI or relocation claim.
3. No whole-image validation: entries decode one window each; image coverage,
   control-flow validation and relocation re-decoding stay open.
4. The loaded-image execute-permission bridge (entry containment implies an
   executable fetch window) is not proved; the fetch side works from a
   `Zustand` whose permissions are checked at runtime, as before.

## Where the result is weaker than the task text (plainly stated)

"Unknown/truncated/unsupported bytes fail closed" is proved as five new
representative `rfl` refusals (truncated imm64, displacement-less access,
unsupported opcode `0x06`, mod=1 form, displacement-less `0F` branch) PLUS the
general positive classification (every success IS one of the 14 canonical
forms at its exact length). The dual exhaustive direction — every
non-canonical byte string refuses — is not proved and would be a much larger
case analysis over rejection shapes; the task's fail-closed demand is met in
the same sense as `Codec`'s existing refusal list, extended by five shapes.
