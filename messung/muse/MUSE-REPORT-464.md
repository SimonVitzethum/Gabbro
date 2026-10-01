# MUSE-REPORT-464: Independent exact-candidate review of 416

Lane 464, clone `/home/simon/Dokumente/gabbro-muse/a464`, branch `muse/464` (verified).
Own file: only `MUSE-REPORT-464.md`. No other clone read.

## Review basis

Exact snapshot `.tmp/review/SNAPSHOT.json`: author 416, pinned HEAD
`ea0b8a3ce0e07ec2bb7b7c454eaa58c8880e9ac4`, base `0b3132b7...` (ancestor of
this clone's HEAD: yes). Files: `MUSE-REPORT-416.md`,
`grammatik/Grammatik.lean` (one additive import), new module
`grammatik/Grammatik/X86/EffectiveAddress.lean` (~500 lines).
The candidate commit object itself is not present in this clone
(`git cat-file` fails; `rev-parse` of a full SHA echoes without verifying),
so verification ran against the supplied exact files: staged them verbatim
(`diff` identical), probed, built, then restored (clone clean again).

## What the candidate claims (bounded)

Reusable facts about the ACTUAL pilot `effAddr`/`dispWort` of
`Ausfuehrung.lean`: signed-displacement pins, modular shifts, prestate
aliasing with non-injectivity, wrap-vs-admission separation, region
admission, consumption by the real `load64`/`store64` `schritt` steps with
`Zugriffe.zugriff` footprints, a future `skaliertAddr` helper with missing
native support recorded, a reached memory-changing run and a dark-memory
refusal. No hardware, TSO, source, ABI, cost or whole-image claim.

## Independent checks (measured in this clone)

- Forbidden tokens: no `sorry`/`admit` tactic/`axiom`/`native_decide`/`unsafe`
  (one comment line contains "admit" as an English word only). Imports are the
  six canonical X86 modules only. English only. CUTS block present and exact.
- `./lean-probe .../EffectiveAddress.lean`: `0 error(s)`, exit 0; all 31
  `#print axioms` lines match the report exactly (all `[propext, Quot.sound]`
  or fewer, except `effAddr_in_region` with the standard triple).
- `./lean-bau` with candidate staged: `exit 0; 0 error line(s)`,
  `Build completed successfully (407 jobs)` (393 in the author's older base;
  difference is master movement, not a defect).
- Semantic grounding verified against accepted definitions in this clone:
  `dispWort`/`effAddr` (`Ausfuehrung.lean` 26-30), `schritt_load64_erfolg`/
  `schritt_store64_erfolg`/refusals, `schritt_load64_speicher`,
  `erfolg_store64_im_fuss`, `zugriff_load64`/`zugriff_store64` (footprint
  equations match the candidate's conclusions constructor-for-constructor),
  `OhneUmbruch`/`ohneUmbruch_addrs`, `inRegion`, `lauf`/`zeugeZustand`/
  `zeugeProg`/`zeuge_speicher_aendert_sich` (rsp=8192, rbx=42, byte 0->42).
  Arithmetic pins rechecked: 8352 = 8192+20*8 (scaled divergence), alias
  16 = 0+16, wrap `0xFF..FF+1 = 0`. All premises of every theorem are used;
  no `Prop`-typed premise; no conclusion restates a premise.
- No duplication: `ControlFlow.lean` owns LEA/CMOV/branch-target address math
  with its own witnesses; the candidate's load/store-step consumption,
  displacement pins and region admission do not restate them. `skaliertAddr`
  is pure address math with no `Befehl`/codec/`schritt` consumer and says so;
  `dunkelSpeicher` is a `Speicher` value, not a second model. No new IR or
  executor. No Spec/checker/emitter/Rust file touched (PATCH names exactly
  the three owned files). No safety weakening; permissions kept separate;
  TSO/atomicity explicitly disclaimed.
- Witness quality: `effAddr_lauf_zeuge` reuses the real reached run
  (`zeuge_speicher_aendert_sich`: non-degenerate, memory-changing);
  dark-memory refusal is a genuine negative case (`decide` + real
  `schritt_load64_verweigert`); boundary cases pinned both directions plus
  top-of-space wrap refusal. The `_zeuge` companions go beyond strict HARD
  RULE 13 (no program-syntax premises, no `ZEUGE:` targets in the owner
  task) and follow X86 precedent; treating them as bonus, not as a gate.
- Build evidence in `BUILD-EVIDENCE.json` is honest (shows intermediate
  failures, OOM thread crashes, re-probes; never counts a crash as pass).

## Defects found

None. No repair direction needed. Minor note (not a defect): the pinned
commit object is not fetchable from this clone, so a byte-level HEAD
comparison was impossible; file-level identity (supplied files vs staged
probe) was verified instead.

## Verdict

ACCEPT of exactly the bounded claim above; no full-compiler closure implied.

CANDIDATE: 416 ea0b8a3ce0e07ec2bb7b7c454eaa58c8880e9ac4
VERDICT: ACCEPT
