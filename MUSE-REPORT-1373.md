# MUSE-REPORT-1373: AES-NI, PCLMULQDQ, MOVBE and the SSSE3 remainder

Lane 1373, clone `/home/simon/Dokumente/gabbro-muse/a1373`, branch `muse/1373`.
Status: COMPLETE and green. `./lean-bau`: `== exit 0; 0 error line(s)` (711+ jobs,
including the new file). `./lean-probe` on the new file: 0 errors.
`pruefe-kein-sorry.py --rev muse/1373 --diff master`: 0 violations.
`lean-layout.py --check`: passes (after `--apply`).

## Deliverable

NEW FILE `grammatik/Grammatik/X86/Befehle/Sse/SseAesClmul.lean` (~2900 lines;
the task named `grammatik/Grammatik/X86/SseAesClmul.lean`, but HARD RULE 18
and the layout gate require the `Befehle/Sse` folder for `^Sse` names:
`--check` fails (exit 1, NOT PLACED) at the root path, so the file was built
at the root and placed with the sanctioned `lean-layout.py --apply`, which
moved it; the import appended to `grammatik/Grammatik.lean` is therefore
`import Grammatik.X86.Befehle.Sse.SseAesClmul`, not the task's
`Grammatik.X86.SseAesClmul`).

Seventeen admitted rows: AESENC/AESENCLAST/AESDEC/AESDECLAST/AESIMC
(`66 0F 38 DC/DD/DE/DF/DB /r`), AESKEYGENASSIST (`66 0F 3A DF /r ib`),
PCLMULQDQ (`66 0F 3A 44 /r ib`), MOVBE (`0F 38 F0/F1`, 16/32/64-bit,
base+disp memory, no SIB), PHADDW/PHADDD/PHSUBW/PHSUBD/PSIGNB/W/D/PMULHRSW
(`66 0F 38 01/02/05/06/08/09/0A/0B /r`). Canonical REX-first byte order
follows the accepted tree convention (VectorCodec, SseThreeByte); silicon
wants legacy prefixes before REX (named in CUTS).

Main definitions: `AesClmulOp`, `AesClmulDec`, `encodeAesClmul`,
`decodeAesClmul`, `roundtripAesClmul`, `movbeTausch`/`bswap16`,
`aesSBoxNat`/`aesInvSBoxNat` (+GF `aesXtime`/`aesMul`, `aesEncRound`,
`aesEnclastRound`, `aesDecRound`, `aesDeclastRound`, `aesImc`,
`aesKeygen`), `vecPclmul`, `vecPhadd`/`vecPhsub`/`vecPsign`/`vecPmulhrsw`,
`stepAesClmulReg`, `movbeStore`/`movbeLoad`, `KapAes`/`kapDecodeAes`,
`adapterAesClmul`, `aesClmulWit_zeuge` (joint witness).
Key theorems: per-row round trips (MOVBE with `base ≠ .rsp ∧ base ≠ .r12`
premises, CompactForms-Disp0 pattern, since SIB is refused);
`kapDecodeAes_alt/neu/nichts` (exact old-chain agreement); per-row
`kapDecode` refusal pins (20× `decide`: no old row shadowed);
`adapterAesClmul_wf/reg/lad/spei` + planted refusals; frame theorems
(rip/flags/speicher/gpr/fremd). Axioms: only `propext`/`Quot.sound`,
no `sorryAx` (full `#print axioms` list at the file end).

## Findings (task text corrections, all verified against the supplied SDM)

1. AES rounds XOR the key LAST (`DEST := STATE XOR RoundKey`), not first.
2. PHADD/PHSUB WRAP; only PHADDSW saturates. The task's "PHADD/PHSUB
   saturating forms" is wrong per SDM Vol. 2B 4-294 ("does not set bits in
   EFLAGS"); the file models wrapping, PHADDSW stays refused.
3. PMULHRSW has no saturation step (`((a*b)>>14)+1`, bits `[16:1]`,
   arithmetic shifts); `_mm` check: `0x7FFF*0x7FFF -> 0x7FFE`
   (my first pin value `0x8000` was hand-arithmetic error, caught by
   `decide`), `0x8000*0x8000 -> 0x8000` (distinguishes from saturation).
4. S-box transcription typo found by a temporary `#eval` hunt
   (`invS[0x7E]` was `0x8B`, must be `0x8A`; duplicate `0x8B` with
   `invS[0x3D]`), fixed; mutual inversion over all 256 bytes now proved
   both directions. Hunt scaffolding removed.
5. `rfl` round trips need FLAT encodings (nested `++` blocks definitional
   unfolding in this toolchain) and no pair-match on computed values in
   decoders (restructured to the accepted CompactForms/SseThreeByte
   if-chain shapes); SIB bases are genuinely refused, hence the premises.
6. MOVBE is F0=load/F1=store, 16-bit via `66`, 64-bit via REX.W, flags
   unaffected; disp8 is sign-extended.

## Open / not claimed (see CUTS for the full list)

No MMX/memory-XMM/SIB/RIP-relative/disp-less/REX.W-XMM/`66`+REX.W/VEX/EVEX
forms; no PHADDSW; no LOCK path; no fault delivery beyond explicit refusal;
no source/IR/ABI/loader/entry/budget link; no W/GX bridge; no timing/power.
A maintainer wires `decodeAesClmul` behind every arm of `kapDecode`
(`HwKapsteinDecoder.kapDecode`), same position as the `avx2` arm.
`instrumente/lean-layout-map.json` (modified by `--apply`) left
uncommitted — coordinator bookkeeping, not lane-owned.
`--apply` moved the file out of the lane-owned root path only after the
final green edit; no further edits to it are possible from this lane.
No Rust changes (Lean-only lane); `cargo-pruef`/`emission-pruef` untouched.

## Verification log

- `./lean-probe`: 101→22→10→4→3→1→0 errors across the build (each error
  class fixed: duplicate structure, `prefix` keyword, encoder REX order,
  SIB premises, `List.get?` absence, `set_option` placement, S-box typo,
  PMULHRSW arithmetic, `regSet_gleich`).
- Last `./lean-bau` result line: `== exit 0; 0 error line(s) in the
  COMPLETE output` (Build completed successfully).
- Probe was repeatedly blocked by slot contention and one wiped `.lake`
  cache (rebuilt via incremental `./lean-bau` runs); no credentials,
  network, or foreign paths touched.
