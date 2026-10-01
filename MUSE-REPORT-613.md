# MUSE-REPORT-613: Independent overnight closure review of 601

CANDIDATE: 601 e3385ee72881d2fbd661ad4db25b8e4ada0a9995

VERDICT: ACCEPT

## Identity and scope

- Clone `/home/simon/Dokumente/gabbro-muse/a613`, branch `muse/613` verified.
- Snapshot `.tmp/review/SNAPSHOT.json`: author 601, head
  `e3385ee72881d2fbd661ad4db25b8e4ada0a9995`, base `0044c258`, files
  `MUSE-REPORT-601.md`, `grammatik/Grammatik.lean` (one umbrella import line),
  `grammatik/Grammatik/X86/FlagDependencies.lean` (new, 531 lines), clean true.
- PATCH.diff confirms exactly those three paths. No source checker, Spec,
  goal, friend-reserved optimiser, or OS-assumption edits. No other clones,
  config, credentials, network, model calls, or push used. Owned deliverable
  is this report only; no Lean imports added.

## What was checked

- Read the full candidate file, the owner task, the author report, PATCH.diff,
  and BUILD-EVIDENCE.json. Resolved every producer name against current
  master: `Wort.bedingung`, `Codec.decode`/`roundtrip_jumpIf32`,
  `Ausfuehrung.schritt` + `schritt_jumpIf32_genommen`/`_nicht` +
  `zeugeGleich`/`zeugeFlagsGleich`/`zeugeSpeicher`/`zeigeReg` +
  `schritt_laenge_verweigert`, `lauf`, `laengeOk`/`ripNach`/`dispWort`,
  ControlCodec `cmovSchrittBytes`/`setccSchrittBytes` +
  `setccSchrittBytes_wert`, ConditionalMove
  `cmovAnwenden_genommen_wert`/`_nicht_wert`, DecodingCoverage
  `decode_abdeckung`/`decktAb`. All resolve; nothing is duplicated or
  re-modelled.
- Read-set correctness: `liestFlag` matches `Wort.bedingung` arm-for-arm
  (o/no OF, b/ae CF, e/ne ZF, be/a CF+ZF, s/ns SF, p/np PF, l/ge SF+OF,
  le/g ZF+SF+OF; AF absent by construction since `Flags.af` is never read).
- Premise use: `jccSchritt_stabil` uses `hdec` (length 6, hence `laengeOk`),
  `hrip`, `hfl`, `hF`, `hG` on both taken/untaken branches;
  `cmovBytes_stabil`/`setccBytes_stabil` use all their premises;
  `decodeJumpIf_laenge` goes through accepted `decode_abdeckung` + `decktAb`
  (8-way shape case, 7 clashes + length), i.e. no second decoder inversion.
  No `Prop`-typed premise, no `intro _` / `have _ :=`, no conclusion-restated
  premise, no quantified-away contract, no fake semantics.
- Forbidden tactics: precise regex for `sorry`/`admit`/`axiom`/`native_decide`/
  `unsafe` over the candidate file finds zero (the one earlier `grep` hit is
  the English word "admits" in a comment). No `sorryAx` in the final axioms.
- Witnesses: `jccSchritt_stabil_zeuge` is joint — canonical `je +16` bytes
  decode at length 6, `zeugeGleich` (ZF set) vs `sAnder` (ZF set, every other
  flag flipped: cf/pf/sf/of differ, verified against `zeugeFlagsGleich`),
  both accepted steps run, successors agree via the main theorem, preceding
  `progVor` (movImm/store/sub) run stores 42 observably and sets ZF, truncated
  5-byte prefix refused. `mov_xor_wechsel_zeuge` is the required negative
  witness (MOV keeps ZF clear, fall-through 4105; XOR of equals sets ZF, taken
  4121). `jccLaenge_verweigert` (generic, via accepted length refusal) and
  `jccKurz_verweigert` (5-of-6 bytes, `decide`) are planted refusals.
  Inhabitation rule: no theorem quantifies over program syntax, so no
  mechanical `_zeuge` is required; joint machine witnesses are provided anyway.
- CUTS and axioms: file ends with an exact proved vs not-proved CUTS block
  plus `#print axioms` for every main theorem. Final evidence is
  `lean-probe 0 error(s)` and `lean-bau exit 0, 0 error lines, 440 jobs`,
  axioms `propext`/`Quot.sound` only (`bedingung_af_frei`: none). The
  intermediate `sorryAx`/33-error probes in BUILD-EVIDENCE are mid-draft
  states, honestly recorded and repaired before commit. CUTS explicitly denies
  hardware correspondence, liveness/optimiser, TSO/GX/concurrency/cost/time/
  termination, and source/checker/Spec/goal claims.
- No hidden simulation, timestamp reset, guessed ISA, weakening, or filler:
  every claim is a per-condition stability fact over the reused canonical
  definitions and accepted step equations.

## Minor note (not verdict-changing)

- The author report says InstructionSelection600 "does not exist yet"; current
  master has `grammatik/Grammatik/X86/InstructionSelection.lean` (imported in
  `Grammatik.lean`). This is a stale sentence against a newer master, not a
  proof defect; the consumer interface (`stimmtUebberein` + the three stability
  theorems, exact names) is still correctly named for its consumer.

## Bounded accepted scope

- New `grammatik/Grammatik/X86/FlagDependencies.lean` plus the one umbrella
  import line in `grammatik/Grammatik.lean`. Consumer interface:
  `stimmtUebberein`, `jccSchritt_stabil`, `cmovBytes_stabil`,
  `setccBytes_stabil` with read sets from `liestFlag`. No wider closure is
  granted: full byte-connected machine, TSO/GX bridge, source-to-final-bytes
  validation, and any hardware/liveness/optimiser claim remain OPEN.

## Useful next independent tasks (not started)

- InstructionSelection consumer: use `stimmtUebberein` as the
  flag-liveness/refinement check for select lowering (owner: whoever holds
  the selection lane; disjoint, needs no change here).
- `byteschritt`-level lifting of `jccSchritt_stabil` via
  `Byteschritt.fetchDekodiert` (fetch+decode+execute from memory; disjoint
  follow-up, exact ownership to the dispatcher).

## Build evidence (reviewer)

- Reviewer ran read-only checks only (no Lean build claimed, per reviewer
  rules): `grep` premise/forbidden-tactic resolution, `decktAb` shape read,
  `bedingung`/witness definition reads, PATCH/file-list inspection. Green
  build evidence is the author's committed BUILD-EVIDENCE final entries
  (`lean-probe 0 errors`, `lean-bau exit 0, 440 jobs`), not a reviewer rerun.
