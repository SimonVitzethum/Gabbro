# MUSE-REPORT-749: Hardware completion — compact SUB with imm8

Lane 749, clone `/home/simon/Dokumente/gabbro-muse/a749`, branch `muse/749`.
Owned files only: `grammatik/Grammatik/X86/CompactImm8Sub.lean` (new),
`grammatik/Grammatik.lean` (one import line appended), this report.

## What was done

Covered exactly one row — **REX.W + 83 /5 ib, SUB r/m64, imm8,
register-direct (mod=3)** — reusing the accepted `IntegerHardwareForms`
immediate row (`encodeIntHwImm`, `decodeIntHwImm`, `stepIntHwImm`,
`fetchIntHwImm`, `intHwImmByteschritt`, `immWort`, `immPasst8`,
`imm8Erweitern`, `immDecLaenge`, `immDecBreiteOk`, `immBreiteOk`,
`stepImm_speicher`) and canonical `Wort.sub64`/`cfSub`/`afSub`,
`Zustand`/`Speicher`, pilot `schritt`, `NarrowOps.narrowTruncMod`,
`RelocatedExecution.bit31_equiv`. No new syntax, decoder, evaluator,
state type, diagnostic/gift/example/CLI number, or MARKE_EMIT change.
Manual ground (present in this clone): Intel SDM 325462-093US
(Sep 2026), Vol. 2B 4-685/4-686, heading SUB—Subtract, row
"REX.W + 83 /5 ib  SUB r/m64, imm8  MI  Valid  N.E.  Subtract
sign-extended imm8 from r/m64"; Operation DEST := (DEST − SRC);
immediates sign-extended to the destination width; flags OF SF ZF
AF PF CF set according to the result.

New definitions: `subkompaktProg`, `subkompaktBytes`,
`subkompaktExec`, `subkompaktDaten`, `subkompaktReg`,
`subkompaktStart`, `subkompaktRest`, `subkompaktMitte`,
`subkompaktKette`.

New theorems:
- Choice/fit: `kompakt_sub_feuert` (compact length 4 iff fits),
  `imm8Erweitern_passt` (every decoded imm8 byte fits; analytic
  proof over `n < 256` reusing `narrowTruncMod` + `bit31_equiv`).
- Pinned bytes/decodes: `pin_sub_kompakt` (`sub rax, 1`),
  `pin_sub_neg1` (`sub rax, -1`), `pin_sub_r9`, `pin_sub_weit`
  (`sub rax, 256` wide), `pin_sub_kompakt_dekode`,
  `pin_sub_neg1_dekode`, `pin_subkette_bytes`.
- Width/refusals: `subImm_breite_nur_b64`,
  `subkompakt_32_verweigert` (generic digit-5-at-b32 decoder
  refusal), `subkompakt_sbb_verweigert`, `subkompakt_adc_verweigert`,
  `subkompakt_ohne_rex_verweigert`, `subkompakt_rex_r_verweigert`,
  `subkompakt_w0_kompakt_verweigert`, `subkompakt_w0_weit_verweigert`,
  `subkompakt_kurz_verweigert`.
- Borrow identity: `probe_sub_borgt`, `subkompakt_schritt`
  (value, full `sub64` snapshot, CF borrow, DEFINED AF nibble
  borrow, RIP advance).
- TARGET `CompactImm8Sub_verbindung` (fetched compact SUB executes
  with borrow identity, RIP past 4 bytes, memory untouched) with
  companion `CompactImm8Sub_verbindung_zeuge`: joint concrete
  instantiation (fetch + fit + byte-step + all five conclusion
  equations via the TARGET itself), register change 5 to 4, reached
  store step changing the data cell from zero to 4, SBB/no-REX
  refusals.
- Chain pins: `subkompakt_holt`, `subkompakt_weiter` (by `rfl`),
  `subkompakt_mitte_wert`, `subkompakt_kette_speicher`,
  `subkompakt_kette_rip`.

## Verification

- `./lean-probe grammatik/Grammatik/X86/CompactImm8Sub.lean`:
  `== 0 error(s) ...; exit 0`. Every new theorem's axioms are
  subsets of `[propext, Classical.choice, Quot.sound]`.
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (483 jobs).` Two earlier `lean-bau`
  runs failed at the final aggregate step on a *missing, unrelated*
  `.olean` (first `ZielOrtInvGrundZeuge`, then
  `VectorIntegerHardwareForms`); both files were unmodified and
  their oleans existed on re-check — a transient parallel-build
  scheduling race, resolved by re-running. My file built cleanly
  in all runs.
- `./lean-probe grammatik/Grammatik/Zielsatz/BeweisAtomar.lean`:
  `== 0 error(s) ...; exit 0`, with `gabbro_ziel` on exactly
  `[propext, Classical.choice, Quot.sound]` (first attempt crashed
  with `failed to create thread`, a known machine resource
  ceiling; retry passed).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new
  file. Every premise of every new theorem is used by its proof.

## What remains open (also listed in the file's CUTS)

No hardware correspondence (stated canonical subset, self-consistency
only); no memory-operand form (only mod=3 covered); no 16/32-bit 83
rows, 81/80 rows, or LOCK prefix; no TSO/GX bridge (row emits no
memory access, proved); no source/ABI/image/entry/relocation/cost
claims; `ExtendedExecution` does not dispatch this family, so
dispatcher composition stays with its owner.

## Task feedback

Nothing in the task was wrong. Two toolchain notes: (1) `decide`
does not evaluate `∀ n : Fin 256, ...` here and `fin_cases` is
unavailable without mathlib — proved the fit lemma analytically
instead. (2) `· by decide` as a bullet misparsed in one proof
while `· decide` worked; harmless but odd.
