# MUSE-REPORT-700: Essential multiply/divide widths and immediate IMUL

## Scope delivered

New module `grammatik/Grammatik/X86/MulDivWidthHardwareForms.lean`
(2058 lines, ~185 definitions/theorems) plus the additive umbrella
import in `grammatik/Grammatik.lean`. Nothing else touched.

Admitted widths are 32 and 64 bits (`WdBreite.w32/w64`):
- one-operand MUL (`F7 /4`) with EDX:EAX / RDX:RAX products,
  zero-extended at 32 bits;
- DIV/IDIV (`F7 /6 /7`) over the implicit EDX:EAX / RDX:RAX
  dividend with `#DE` (halt, no successor) on divisor zero and
  quotient overflow;
- two-operand IMUL (`0F AF /r`) and three-operand IMUL with signed
  immediates (`6B /r ib`, `69 /r id`, REX.W sign-extends the dword);
- dividend preparation `98` (CWDE/CDQE) and `99` (CDQ/CQO) with
  width/REX effects, all flags preserved.

## Exact names of the main results

- Width/division core: `WdBreite`, `wdLesen`, `wdSchreiben`,
  `u64aus32`, `s64aus32`, `divWeitU32`, `divWeitS32` with refusal
  (`divWeitU32_verweigert_bei_null/ueberlauf`,
  `divWeitS32_verweigert_bei_null`, answer (`divWeitU32_antwortet`)
  and zero-extension (`divWeitU32_antwortet_zero_ext`) facts.
- Flags: `wdMulFlagsU/S` with `wdMulFlagsU_gueltig`,
  `wdMulFlagsS_gueltig` (against `MulGueltigU/S`), `wdMulFlagsU_zf`,
  `wdMulFlagsS_sf`.
- Step: `WdBefehl` (7 forms), `WdDecodiert`, successor builders
  `wdMulRegs`, `wdDivRegs`, `wdImul2Regs`, `wdNachMul`,
  `wdNachDiv`, `wdNachImul2`, `wdNachImul3`, `vor98Schritt`,
  `vor99Schritt`, `wdSchritt` reusing `MulDivErgebnis`, with one
  equation per arm (`wd_mul32_erfolg`, `wd_mul64_erfolg`,
  `wd_div32_erfolg/halt`, `wd_div64_erfolg/halt`,
  `wd_idiv32_erfolg/halt`, `wd_idiv64_erfolg/halt`,
  `wd_imul2_erfolg`, `wd_imul3_erfolg`, `wd_vor98_erfolg`,
  `wd_vor99_erfolg`, `wd_vor_flags`, `wd_laenge_misslungen`).
- Bytes: `wdRex` (+`wdRex_len`), `nimmNach66`, `nimmPraefix`,
  `decodeWdF7/AF/Nach0F/Imm8Tail/6B/Imm32Tail/69/NachPraefix`,
  `decodeWd`, `wdEncode`, `wdEncodeImul3`, immediates
  (`imm8Erweitert`, `wdU32AusBytes`, `imm32AusNat`).
- Round trips: `wdRoundtrip_mul/div/idiv/imul2/vor98/vor99`
  (generic, any suffix) plus 16 pinned byte/decode pairs including
  compact `-3`/`-128` and dword `100000`/`-70000`.
- Length: per-layer facts, `decodeWd_len_ok` (arbitrary input,
  exact consumption, 1..15), `decodiertWd_laenge_ok`,
  `wdEncode_len_ok`.
- Execute/fetch: 14 `decodeWd_exec_*` theorems, `wd_halt_ist_kein_ok`,
  `wdGeholt`, `wdFetchDekodiert`, `WdAusgang`, `wdByteschritt`,
  `wdByteschritt_weiter/halt/verweigert_ohne_fetch`.
- Probes: 16 `wd_nichts_*` refusals (LOCK, 0x66, F6, /5, mem-mode,
  REX.R/X, double REX, bad escape, short immediates), 10
  `probe_wd_*` value probes, fetched end-to-end
  `probe_wd_bytesschritt`, joint witness `wd_zeuge_gemeinsam`
  (compact decode + high-register compact step + negative division
  + real-RAM change + overflow halt + LOCK/width/imm refusals +
  instantiated `decodiertWd_laenge_ok`).

## Checks run

- `./lean-probe grammatik/Grammatik/X86/MulDivWidthHardwareForms.lean`:
  `== 0 error(s)`.
- `./lean-bau` (twice): `Build completed successfully (469 jobs).`
- `#print axioms` for every main theorem: subset of
  `[propext, Classical.choice, Quot.sound]` (standard goal axioms).
- No `sorry/admit/axiom/native_decide/unsafe` in the new file.
- No premise has type `Prop` itself; every premise is used.
- No theorem quantifies over program syntax, so no mechanical
  `_zeuge` obligation; the joint witness instantiates the generic
  results on a memory-changing run instead.

## Findings during the work (all repaired, none weakened)

1. `CDQ` first modelled as `trunc32 (sext32 EAX)` (= EAX, wrong):
   silicon broadcasts the sign bit into all of EDX. Repaired to
   the `negB`-gated broadcast; the `decide` probe caught it.
2. Imm-tail lengths were off by one (`npfx+4/+7` instead of
   `+3/+6`); the pins caught it.
3. Two hand-computed pin bytes were wrong (REX `67` vs `68`,
   ModRM `194` vs `208`); `decide` caught both.
4. The `nimmPraefix` three-arm list match blocked round-trip
   reduction over variable suffixes; restructured to two arms with
   a `nimmNach66` tail.

## Open (explicit CUTS in the file)

- 8/16-bit MUL/DIV/IDIV/IMUL and CBW/CWD refused (essential OPEN;
  obstruction: `Register` has no sub-registers/partial merge).
- One-operand IMUL (`F7 /5`) refused (not required).
- Memory operands refused (access lanes' business).
- Generic immediate round trip OPEN (four pinned immediates only).
- No silicon/fault-delivery/priority/TSO/source/cost claims.

## Task remarks

Nothing in the task statement appears wrong. The
"compact-immediate/high-register/negative-division run ending in a
real RAM change" is delivered as the joint conjunction
`wd_zeuge_gemeinsam` (computed `-21` stored through `write64` with
an observed byte change plus `read64` round trip), not as a
multi-step sequential execution, since IMUL/DIV do not touch
memory and sequential-state chaining adds no semantic content
beyond the already-proved per-step equations plus the memory
transfer.
