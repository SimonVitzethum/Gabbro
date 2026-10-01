# MUSE-REPORT-549: Independent exact-candidate review of 543 DecodeFault

## CANDIDATE

CANDIDATE: 543 ff34113dff87d2517b7f4a27bb657833c0891e00

## VERDICT

VERDICT: ACCEPT

Accepted scope is BOUNDED (see "Accepted claim" below). Full source/hardware/
compiler closure remains OPEN.

## What was checked

- Snapshot: `.tmp/review/SNAPSHOT.json` (author 543, base
  `3dce9fa2585d123c1ad546d520eaf8fe60f0125d`, files `MUSE-REPORT-543.md`,
  `grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/DecodeFault.lean`).
- Author task (N16 DecodeFault), author report, exact PATCH (364 lines:
  276-line new module + one additive umbrella import), and BUILD-EVIDENCE.json
  (includes one intermediate 4-error probe during drafting, final 0-error
  probe, `./lean-bau` 416 jobs green, commit `ff34113d`).
- Staged the exact candidate files in this clone (branch `muse/549`,
  HEAD `ebdec41dc6ef288c61f00601cbfe2be4b0ecd913`) and reproduced:
  `./lean-probe grammatik/Grammatik/X86/DecodeFault.lean` ->
  `== 0 error(s) in the COMPLETE output`, all `#print axioms` within
  `[propext, Quot.sound]` or fewer; `./lean-bau` ->
  `Build completed successfully (421 jobs).` Staged files removed afterwards;
  this commit is report-only (`git status --porcelain` clean before writing
  this report).
- Verified every reused name resolves to a real definition in the current
  tree (no plan-name hallucination): `divWeitU_verweigert_bei_null`,
  `divWeitU_verweigert_bei_ueberlauf`, `divWeitS_verweigert_bei_null`,
  `divWeitS_verweigert_bei_oben`, `md_div_halt`, `md_idiv_halt`,
  `md_laenge_misslungen` (`MulDiv.lean`); `cmovMemSchritt`,
  `cmovMem_feheler_bleibt`, `cmovAnwenden`, `witFalse`, `witDunkel`,
  `witTrue`, `witSpeicher`, `cmov_speicher_zeuge` (`ControlFlow.lean`);
  `narrowAdmitted`, `readBreite`, `probe_fallback_unaligned`
  (`NarrowOps.lean`/`Speicher.lean`); `mdZustandDiv`, `mdZustandNull`,
  `probe_div_schritt` (`17/5 = 3 r 2`), `probe_div_halt_schritt`,
  `muldiv_speicher_sonde`, `istHalt`, `okWerte`, `rein`, `zeugenSpeicher`,
  `zeugeFlags`. No new machine, decoder row, or semantics invented.
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the candidate
  (grep clean); no Prop-typed premise; every premise is used by its proof
  (each hypothesis feeds `md_div_halt`/`md_idiv_halt`/the reused lemma).
- No unsigned/signed/width/fault conflation: unsigned legs use `.toNat`
  with `u128`, signed legs use `sVal .b64` with `s128`/`.tdiv`, matching
  the `divWeitU`/`divWeitS` definitions. Validator refusal (`Bool`:
  `laengeOk`, `narrowAdmitted`) is kept distinct from architectural fault
  (step outcome `.hardwareHalt`/`.misslungen`) by construction.
- Witnesses are joint and non-degenerate: `mdZustandNull.speicher =
  zeugenSpeicher`, so each div-trap `_zeuge` proves the concrete trap on
  the same memory the `muldiv_speicher_sonde.2` run then changes
  observably (`zeugenSpeicher.bytes 0 != m1.bytes 0`); all `decide`
  side-conditions close on concrete values (non-vacuous). No OS/kernel
  trust, no ABI claim, no source Spec/checker/emitter or friend-reserved
  file touched.

## Accepted claim (bounded)

`grammatik/Grammatik/X86/DecodeFault.lean` proves, over the reused
canonical `MulDiv.mulDivSchritt` / `ControlFlow.cmovMemSchritt` /
`NarrowOps` effects:

- `fehler_div_null_haelt`, `fehler_div_ueberlauf_haelt`,
  `fehler_idiv_null_haelt`, `fehler_idiv_oben_haelt`: the four named
  divide-error shapes trap to `MulDivErgebnis.hardwareHalt`, each with a
  joint concrete witness plus the quotient/remainder memory run;
- `fehler_cmov_mem_untaken_haelt`: faulting CMOV-memory refuses on the
  untaken path (exact reuse of `cmovMem_feheler_bleibt`; statement and
  witness duplicate the existing `ControlFlow` lemma/shapes under a
  catalogue name -- thin but faithful);
- `bewegung_verweigert_fuer_falle`: trapping divisions are never `rein`
  (the N16 WITNESS- motion/DCE refusal, by `rfl` on the actual `rein`);
- `dekodierverweigerung_ist_kein_hardwarehalt`,
  `profilverweigerung_ist_kein_fehler`: decode/profile refusal is not an
  architectural fault;
- `bewegen_aendert_beobachtung`: same division halts under zero divisor
  and answers `17/5 = 3 r 2` under a defined one (hoisting across a
  divisor-defining store is observable).

## Precise CUTS (remain OPEN, not claimed)

1. Signed overflow BELOW the range is not catalogued: only `oben`
   (quotient `>= 2^63`, via `divWeitS_verweigert_bei_oben`) is proved;
   there is no `fehler_idiv_unten_haelt` over the existing
   `divWeitS_verweigert_bei_unten` (reachable, e.g. dividend `-2^64`
   over divisor `1`). The candidate CUTS bullet overgeneralizes this as
   "signed quotient overflow". Repair location if seeded: new theorem +
   `_zeuge` in `DecodeFault.lean` reusing
   `divWeitS_verweigert_bei_unten`, witness state RDX = -1 lanes analogue
   (e.g. RDX = all-ones, RAX = 0, RCX = 1). The classic `INT_MIN / -1`
   case IS covered (it traps via the `oben` leg).
2. No extended decoding (which bytes encode DIV/IDIV), no source
   stop-class (`hardware` in `FortschrittG`) guard/fault/channel/order
   transfer -- `hardwareHalt` only names the target stop class.
3. No TSO/concurrency bridge, no verification against silicon, no
   cost/time transfer.

## Last build result

- `./lean-probe grammatik/Grammatik/X86/DecodeFault.lean` (candidate
  staged): `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` (candidate staged): `Build completed successfully (421 jobs).`
- Staged files removed after verification; `git status --porcelain` clean.

## Believed-wrong items in the task

None material. The N16 WITNESS+ ("trapping division reaching the named
stop class") is met in the bounded target-side sense (concrete trap to
`hardwareHalt` paired with a memory-changing run); transfer of that stop
class to the source `hardware` stop stays with the bridge lane, as the
candidate CUTS state.
