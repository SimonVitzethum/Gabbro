# MUSE-REPORT-336: Reviewed organisation plan A2 — MulDiv

## What was done

New module `grammatik/Grammatik/X86/MulDiv.lean` (581 lines) plus one
additive import line at the end of `grammatik/Grammatik.lean`.
64-bit MUL/IMUL/DIV/IDIV as an extension of the one pilot semantics:
no duplicated evaluator of the 14 pilot `schritt` forms, no competing
word-level mul/div redefinition, no source/checker/Spec/goal change.

- Reused (not redefined): `Wort`/`Flags`/`Register`/`Zustand` (Typen),
  `mulLow`/`mulHighU`/`mulHighS`/`sVal`/`mulTragU`/`mulTragS`/`MulGueltigU`/`MulGueltigS`
  (Ganzzahl), `regSet`/`ripNach`/`laengeOk`/`zeugeFlags`/`zeugeZustand`
  (Ausfuehrung), `sint` (FlagBeweis), `read64`/`write64`/`writeBytes`/
  `writeBytesN_hit`/`addrOff_null`/`read64_nach_write64`/`zeugenSpeicher`
  (Speicher).
- New: `u128`/`s128` (128-bit RDX:RAX dividend, unsigned/signed),
  `divWeitU`/`divWeitS` (wide division with defined-when checks:
  divisor zero AND quotient overflow both give `none`; signed side
  truncates toward zero via `tdiv`/`tmod`, never SAR floor),
  `mulFlagsU`/`mulFlagsS` (snapshots pinning exactly CF/OF/AF and
  preserving incoming SF/ZF/PF as an explicit modelling choice, each
  proved against the `Ganzzahl` validity relation), `MulDivBefehl`
  (`mulRax`/`imul2`/`divRax`/`idivRax`), `MulDivDecodiert`,
  `MulDivErgebnis` (`ok`/`hardwareHalt`/`misslungen`), `mulDivSchritt`
  (new forms only; DIV/IDIV keep all flags, MUL/IMUL set CF/OF),
  `zugelassen` (decided validator guard mirroring the step check),
  `rein` (false for both trapping forms).
- Theorems: `divWeitU_verweigert_bei_null`,
  `divWeitU_verweigert_bei_ueberlauf`, `divWeitU_antwortet`,
  `divWeitS_verweigert_bei_null`, `divWeitS_verweigert_bei_unten`,
  `divWeitS_verweigert_bei_oben`, `mulFlagsU_gueltig`,
  `mulFlagsS_gueltig`, `md_mul_erfolg`, `md_imul_erfolg`,
  `md_div_erfolg`, `md_div_halt`, `md_idiv_erfolg`, `md_idiv_halt`,
  `md_laenge_misslungen`, `zugelassen_div_heisst`,
  `zugelassen_idiv_heisst`, `zugelassen_verweigert_nullteiler`,
  `verweigert_heisst_halt` (refused DIV image traps in the step),
  `falle_nie_rein`, `rein_ohne_halt_mul`.
- Probes (`decide`): `probe_mul_schritt` (6*7: RAX=42, RDX=0, CF
  clear), `probe_div_schritt` (17/5 through the step: RAX=3, RDX=2),
  `probe_div_halt_schritt`, `probe_guard_null`, `probe_div_weit`,
  `probe_div_weit_null`, `probe_div_weit_ueberlauf` (2^64/1 refused),
  `probe_idiv_rumpf` (-7/2 = -3 rem -1, pinning truncation vs floor),
  `probe_idiv_min` (INT_MIN/-1 refused).
- Joint memory witness `muldiv_speicher_sonde`: `divWeitU 0 17 5 =
  some (3, 2)` together with quotient stored at address 0 and remainder
  at address 8 through permission-checked `write64`, both read back
  through `read64`, quotient store observably changing memory.
- No theorem quantifies over source syntax, so HARD RULE 13 needs no
  `_zeuge`; the joint step/memory probes above are the non-degenerate
  witnesses (real `write64` memory change).

## Last build results

- `./lean-probe grammatik/Grammatik/X86/MulDiv.lean`: 0 errors; every
  `#print axioms` within `[propext, Quot.sound]` (subset of standard).
- `./lean-bau`: exit 0, 0 error lines, 386 jobs, completed successfully.
- `./lean-probe grammatik/Grammatik/Zielsatz/Beweis.lean`: 0 errors;
  goal side intact with exactly
  `[propext, Classical.choice, Quot.sound]`.
- `git status`: only `grammatik/Grammatik.lean` (one import line) and
  the new module plus this report. No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` in the new file.

## What remains open (CUTS, also in-file)

Wiring the four forms into `Befehl`/`schritt`/decoder/image (Typen
owner); DIV/IDIV-to-`hardware` guard/fault/channel/order correspondence
(bridge lane 277); source range transfer; cost/budget transfer;
TSO/GX bridge; silicon verification of all stated semantics.

## Task feedback

- The plan's Dep line (`Wort`, `Ausfuehrung`, `FlagBeweis`) omits
  `Ganzzahl.lean`, which already holds the single-width mul/div family
  including `INT_MIN/-1` refusal and both MUL validity relations. The
  genuine A2 gap was only the 128-bit dividend with quotient-overflow
  trap plus the register-step/guard/policy layer; this module is scoped
  to exactly that and reuses `Ganzzahl` throughout.
- `Int.tdiv`/`tmod` (truncating) exist in this toolchain and match the
  required IDIV direction; the SAR-floor mismatch is pinned by
  `probe_idiv_rumpf`, consistent with `StaerkeReduktion.sdiv_kein_shift`.
- Two toolchain facts cost time: struct updates allow no newline after
  a field comma (worked around, single-line updates), and `simp`
  normalises `-↑(2^63)` numerals so a negated-conjunction hypothesis
  misses the `if` condition — finished those goals with `omega` over
  opaque atoms instead.
