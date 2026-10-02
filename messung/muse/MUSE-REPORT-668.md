# MUSE-REPORT-668: IEEE scalar operation and conversion byte rows

Lane 668, clone `/home/simon/Dokumente/gabbro-muse/a668`, branch `muse/668`.
Owned files only: `grammatik/Grammatik/X86/ScalarFloatHardwareForms.lean`
(new, 2203 lines, 73 defs, 148 theorems), `grammatik/Grammatik.lean`
(one additive import line), this report.

## 1. What was built

REX-aware canonical SSE2 binary64 byte rows for SUBSD / MULSD / DIVSD
(register and memory), UCOMISD (register and memory), CVTSI2SD and
CVTTSD2SI (REX.W = 1 register forms), MOVSD (register, load, store) and
ADDSD memory (ADDSD register low-only was lane 565; the REX register
form and the memory form are new here), over all sixteen XMM registers
and all sixteen GPRs. No new evaluator and no new IEEE arithmetic:
every execution fact is an accepted `fpSchritt` equation or an accepted
kernel witness (`Gleitprofil`, `FloatExceptions`, `FloatSourceObservations`,
`ScalarFloat` §4-§6).

- §1 encoders: `fpHwRex`, `fpHwArithOpcode`, `fpHwRexXX`, `fpHwRexXB`,
  `fpHwEncodeArithRR/RM`, `fpHwEncodeUcomiRR/RM`, `fpHwEncodeCvtsi`,
  `fpHwEncodeCvtt`, `fpHwEncodeMovsdRR/Lade/Speichere`, plus length
  facts (`fpHwLen_rr`, `fpHwLen_ucomiRR`, `fpHwLen_cvtsi`,
  `fpHwLen_cvtt`, `fpHwLen_movsdRR`, `fpHwLen5_ok`).
- §2 independent decoder over actual bytes: `fpHwArithVonOpcode`,
  `fpHwArithRR/RM`, `fpHwDecodeReg`, `fpHwDecodeMemForm`,
  `fpHwDecodeRest`, `fpHwRexBits`, `fpHwNach0F`, `fpHwDecode`.
- §3 round trips over the full register file, no `< 8` side conditions:
  `fpHwRoundtrip_arithRR`, `fpHwRoundtrip_ucomiRR`,
  `fpHwRoundtrip_cvtsi`, `fpHwRoundtrip_cvtt`,
  `fpHwRoundtrip_movsdRR`, `fpHwRoundtrip_addsdRM/subsdRM/mulsdRM/
  divsdRM`, `fpHwRoundtrip_ucomiRM/movsdLade/movsdSpeichere`.
- §4 explicit refusals: REX-before-prefix, F3, non-REX byte, X = 1,
  W = 0 / W = 1 mismatches, memory-source conversions, register
  store, COMISD, swapped prefixes, non-36 SIB, mod 00/01, truncations
  (`fpHwDecode_*_verweigert`, `fpHwDecode_abgeschnitten_*`), plus
  seven pilot-disjointness pins (`fpHwPilot_weist_*_zurueck`).
- §5 CVTTSD2SI domain adapter: `cvttTruncOf`, `cvttHwGueltig`,
  `cvttAdapter_gueltig`, `cvttHwGueltig_none/some/erfolg`, domain pins
  `cvttHwGueltig_unendlich/nan/42`. Silicon returns the indefinite
  integer off-domain while the accepted wrapper returns 0/saturated,
  so the byte row admits only the agreeing domain and refuses outside.
- §6 gated byte step from actual memory: `fpHwGeholt`,
  `fpHwFetchDekodiert`, `fpHwCvttZugelassen`, `fpHwByteschritt`,
  `fpHwFetchDekodiert_erfolg`, `fpHwByteschritt_schritt`,
  `fpHwByteschritt_cvttVerweigert`,
  `fpHwByteschritt_profil_verweigert`.
- §7 byte-level observations: `fpHwByteschritt_arithRR_rechnet/klasse/
  hoch` (generic over all four ops), `fpHwSchritt_ucomisdRR_ungeordnet/
  gleich`, `fpHwNan_nutzlast_klasse`, `fpHwNan_ungeordnet`,
  `fpHwSub_plusnull`.
- §8-§13 joint witnesses: W1 `fpHwW1_div_speichert` (fetched DIVSD
  `1.0/+0.0 = +∞` then store, memory change, readback),
  W2 `fpHwW2_cvtsi_speichert` (fetched REX.W conversion then store),
  W3 `fpHwW3_cvtt_gueltig` (`42.0 -> 42` in `rax`) and
  `fpHwW3_cvtt_verweigert` (same bytes, `+∞` source, fetch ok,
  step refuses), W4 `fpHwW4_ucomi_gleich` (equal row from bytes),
  W5 `fpHwW5_lade_verweigert` (fetch ok, unreadable data, refuses),
  W6 `fpHwW6_profil_verweigert` (FTZ-mutated word refuses),
  W7 `fpHwW7_hoch_ok` (fetched `xmm15 <- xmm8`, low moves, upper kept),
  W8 `fpHwW8_grenze_verweigert` (window truncates mid-form at the
  executable boundary).

## 2. Official provenance (local snapshot, no network)

`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`
(Intel SDM 325462-093US, September 2026): ADDSD F2 0F 58 /r
(Vol.2A 3-21); SUBSD F2 0F 5C /r (Vol.2B 4-692f, legacy upper
unmodified); MULSD F2 0F 59 /r (Vol.2B 4-147); DIVSD F2 0F 5E /r
(Vol.2A 3-273); UCOMISD 66 0F 2E /r with the UNORDERED/GREATER/LESS/
EQUAL flag table and OF/AF/SF := 0 (Vol.2B 4-733f, incl. the
COMISD/QNaN distinction that justifies modelling only UCOMISD);
CVTSI2SD F2 0F 2A /r and F2 REX.W 0F 2A /r with DEST[63:0] :=
convert, upper unchanged, MXCSR.RC rounding (Vol.2A 3-236);
CVTTSD2SI F2 0F 2C /r and F2 REX.W 0F 2C /r with truncation and the
masked indefinite values 80000000H / 80000000_00000000H (Vol.2A
3-253); MOVSD F2 0F 10 /r and F2 0F 11 /r with legacy DEST[63:0] :=
SRC, register form upper unmodified, load form upper zeroed (Vol.2B
4-104f, App.B Table B-26); REX Table 2-4 BITS 0100WRXB with the
mandatory prefix BEFORE REX (Vol.2A 2-7f, CVTDQ2PD example);
masked invalid/divide responses (Vol.1 App.D Tables D-1/D-13);
signed-zero and SNaN rules (Vol.1 11.4).

## 3. Verification

- `./lean-probe` on the module: `== 0 error(s)`, exit 0, zero
  warnings, after each increment (one probe needed a 50-minute
  window: the first attempt timed out on shared-slot contention,
  not on proofs -- no lean process was running; the retry passed).
- `./lean-bau` (whole project): `Build completed successfully
  (460 jobs).`
- `#print axioms` (50 prints): every main theorem depends only on
  subsets of `propext`, `Classical.choice`, `Quot.sound` -- the
  standard `gabbro_ziel` set; nothing new. No `sorry`, `admit`,
  `axiom`, `native_decide`, `unsafe` in the file.
- Rule 13: no theorem quantifies over `Vertrag`/`Stmt`/`Endblock`/
  `ErgExpr`/`Expr`/`Args`; joint non-degenerate evidence is W1 and
  W2 (reached fetched runs with real memory change) plus refusal
  witnesses W3-bad, W5, W6, W8.

## 4. Findings (evidence-backed, nothing weakened)

- **REX/prefix order.** The file emits mandatory-prefix-first
  (F2/REX/0F) per Vol.2A 2-7f. The accepted `VectorCodec` emits
  REX-first (`vectorRex` before `66`); per the same manual section a
  REX not immediately preceding the escape byte is ignored, so those
  bytes would execute as low-register forms on silicon. This is NOT
  a soundness bug in lane 597's proofs (their CUTS already restrict
  to self-consistency, never silicon correspondence), and the file is
  not owned by this lane and was not touched -- recorded here for
  the coordinator only.
- **Legacy MOVSD register form preserves the upper half.** Checked
  against the manual (Vol.2B 4-104f: `DEST[MAXVL-1:64]
  (Unmodified)`) rather than the mnemonic; the accepted model
  matches silicon here. Same for CVTSI2SD upper preservation.
- **Tooling quirks (no proof impact):** multi-line `{ s with f :=
  <newline> value }` updates failed to parse in three places;
  single-line form parses (used throughout). A decoder-produced
  `BitVec` dispenser literal prints as `0#32` and does not rewrite
  against stated `0`; bridged once via a definitional ascription
  (`hstep2` in W5). Closed-`decide` numeral forms (`-2^63` vs the
  literal) needed literal-statemented bounds in the adapter finale.

## 5. Producer API (lanes 660 / FP validator 658)

Encoders `fpHwEncode*`, decoder `fpHwDecode` (+ `fpHwRexBits`,
`fpHwNach0F`), round trips `fpHwRoundtrip_*`, byte step
`fpHwByteschritt` (+ `fpHwFetchDekodiert`,
`fpHwFetchDekodiert_erfolg`, `fpHwByteschritt_schritt`),
gate `fpHwCvttZugelassen` (+ `..._cvttVerweigert`), adapter
`cvttHwGueltig` (+ `..._erfolg`, `cvttAdapter_gueltig`), profile
`fpHwByteschritt_profil_verweigert`, pilot pins
`fpHwPilot_weist_*_zurueck`. `ExtendedExecution` was deliberately
not modified (not owned); integration owns the dispatch decision.

## 6. Open (honest cuts, see file CUTS)

No silicon correspondence (stated shapes, self-consistency only);
NaN payloads class-level; SNaN quieting/traps and sticky MXCSR
unmodelled; deliberate subset refusals (REX.W = 1 arithmetic, W = 0
and memory-source conversions, COMISD, VEX/EVEX/packed/x87/FMA);
no TSO/concurrency/cost/ABI/loader/entry/budget/whole-image claims;
no source/checker/emitter/goal connection. Missing essential FP
rows for a later lane: SQRTSD, CVTSD2SI (rounding, non-truncating),
f32/CVTSS2SD/CVTSD2SS widths, packed arithmetic beyond PXOR/PADDQ,
and the 660/658 consumer integration itself.
