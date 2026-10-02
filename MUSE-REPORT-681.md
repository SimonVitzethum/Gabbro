# MUSE-REPORT-681: Exact review of author 680 (indirect and compact control byte forms)

## CANDIDATE

CANDIDATE: 680 541207aeeb1c0e9b8cbe5025cd2c159e0a2ed2b1

## VERDICT

VERDICT: ACCEPT (bounded; see §6)

## 1. What was reviewed

- Author commit `541207ae` on `muse/680` (single commit over parent
  `eba01b90`), fetched read-only as `refs/revs/680-cand`; working tree
  untouched except a temporary probe (added, verified, fully reverted;
  `git status` clean afterwards).
- Author-owned change is exactly 3 paths: new module
  `grammatik/Grammatik/X86/IndirectControlHardwareForms.lean` (1581 lines),
  one additive import line in `grammatik/Grammatik.lean`, and
  `MUSE-REPORT-680.md`. The large `master..candidate` diff (deleted
  X86 modules, lane/report churn, DIRECT-COMPILER.md) is pure base
  staleness: eight merges (lanes 666-679, reviews, doc tracking) landed
  after the author branched. The author's own commit touches nothing else.
- Clone/branch verified: `/home/simon/Dokumente/gabbro-muse/a681`,
  branch `muse/681`. No network, no push, no other clone modified.

## 2. Method

- Read the full module (all 1581 lines) in sections.
- Grep for forbidden tactics/axioms with word boundaries: zero hits for
  `sorry`, `admit`, `axiom` (declaration), `native_decide`, `unsafe`,
  leading `axiom`/`unsafe`, `intro _`, `have _ :=`. All grep hits for
  `admit*` are English words ("admitted") inside doc comments.
- Cross-checked every external name against current master
  (`schrittCall`, `schrittRet`, `schritt_store64_erfolg`,
  `schritt_ret_erfolg`, `laengeOk`, `ripNach`, `read64`, `write64`,
  `write64_verweigert`, `effAddr`, `bedingung`, `condCode`, `codeCond`,
  `modrmReg`, `modrmMem`, `codeReg`, `regLow`, `regHigh`, `parseLe32`,
  `leBytes32`, `byteNat_natByte_of_lt`, `geholt`, `fetchDekodiert`,
  `byteschritt`, `byteschritt_weiter`, `ausfuehrbarN`, `zeugeZustand`,
  `zeugeFlags`, `witFlagsTrue/False`, pilot `encode`/`decode`): all exist.
- Verified `schrittCall s stk m oben ziel` arity matches the two call sites.
- Verified manual provenance against the clone-local snapshot
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`:
  `CALL r/m64`, `JMP r/m64`, `JMP rel8` rows, Jcc rel8 operation
  (`RIP = RIP + 8-bit` sign-extended), Vol.1 s.6.4.1 near CALL/RET,
  and the cited page tags `3-121`, `3-504`, `3-499`, `4-569` all present.
- Reproduced the build claim against CURRENT master (stronger than the
  author's stale-base build): staged the candidate file plus import line,
  ran `./lean-probe` → `0 error(s)`, exit 0; every `#print axioms` line
  is a subset of `[propext, Classical.choice, Quot.sound]` (checked by
  filtering the full output: no other axiom set appears). Then reverted
  both paths; tree verified clean.

## 3. Architecture findings

- Byte forms correct: `FF /2` call / `FF /4` jmp ModRM rows, mod=3
  register-direct, bare `FF` vs `REX.B` (`0x41`) by `regHigh`, memory
  `REX.W` (`0x48`/`0x49` = 72 + high bit) mod=2 base+disp32 with SIB
  `0x24` exactly when `regLow base = 4`; `EB cb`, `70+cond cb` with the
  `condCode` mapping (O=0..G=15) matching Intel, proved a section by
  generic round trips over all 16 `Bedingung` constructors.
- Closed pins verified by reading: `FF D3` = CALL rbx, `41 FF D1` =
  CALL r9, `48 FF A4 24 + disp32` = JMP [rsp+d32], `74 10` = je +16.
  Refusals land on the right bytes: `/3` (`FF D8`, far call), REX.R
  (`0x4C`), REX.W-on-register (`0x48 FF D3`), `E3` counter family,
  truncations, `mod=0`, empty input.
- Semantics reuse, no second interpreter: steps go through accepted
  `schrittCall`/`schrittRet`/`read64`/`write64`/`effAddr`/`bedingung`;
  return word is always `ripNach` of pre-state RIP; stack slot always
  pre-state `rsp - 8`; memory-indirect target is read from the PRE-state
  effective address BEFORE the return store, with the RSP-base case
  proved to read the pre-instruction top (`memS0_adresse`, manual [ESP]
  rule); faulting target reads refuse on all paths
  (`callMemSchritt_lesefehler`, `jmpMemSchritt_verweigert`).
- Jcc taken/untaken proved from the reused `bedingung` evaluator with
  both flag snapshots on identical bytes.
- Provenance-vs-fault separation is real, not wordplay:
  `zielOhneHerkunft_fuehrt_aus` (unadmitted target still steps),
  `daten_sprung_aber_fetch_verweigert` (step executes, next fetch
  refuses), guard/overlap negatives are execution-level (`none`, never
  silent fallthrough). `RET` stays pilot-owned (`unser_verweigert_ret`);
  pilot/indirect disjointness proved in both directions.
- Adapter `indAdapterDecode` is pilot-first over accepted producers only
  (`Codec.decode`, local `decodeIndirekt`); it imports no unmerged 660/670
  draft, consistent with the task's ownership rule.
- Witnesses are non-degenerate and reached from actual executable bytes:
  `indKette_zeuge` (fetched CALL rbx → pilot callee store → ret; stack
  cell 0→4098 word, data cell 0→42 with read-back, rsp restored, RIP
  4098, admitted target), `memCall_zeuge` (RSP-based call, pre-top read,
  return store with observed change), `kurz_zeuge` (taken 4114 /
  untaken 4098 divergence plus the memory chain beside it).
- CUTS is precise: no hardware correspondence claimed (self-consistency
  only), no `#GP`/`#PF` codes, no timing/caches/CET/TSO, far/`RET imm16`/
  `JCXZ`/LOCK/non-canonical-REX refused by construction with hardware
  acceptance beyond the profile marked OPEN, wider memory encodings
  (scaled SIB, RIP-relative, mod=0/1) OPEN for consumer 664, no
  source/checker/emitter/contract/goal claim. The profile narrowings
  (bare-FF mod=2 refused, `0x40`-`0x4F` except `0x41` refused, REX.W on
  register refused) refuse hardware-valid encodings loudly and are
  documented as selection, not silicon — sound direction for a validator.

## 4. Premise hygiene

- No Prop-typed premises; every theorem premise is consumed by its
  proof (equation lemmas rewrite with each hypothesis; fetch lemmas
  destructure the full conjunction). No conclusion restates a premise;
  no contract quantification issue (no source contracts involved);
  no new semantics over non-memory-changing steps (all steps go through
  `schrittCall`/`schrittRet`/RIP-update over `Zustand` with `Speicher`).

## 5. Defects found

None blocking. Two non-blocking notes for the integrator:
- The candidate predates eight master merges; integration needs the
  trivial import-block union in `grammatik/Grammatik.lean` (no semantic
  conflict: all eight dependency modules are byte-identical between the
  author's base and master, verified by empty `git diff` on them).
- `decodeIndRegNach`'s `ext` guard is dead at all call sites (callers
  pre-check `rg`); harmless redundancy, not a soundness issue.

## 6. Bounds of this ACCEPT

- Accepted: selected-profile indirect/compact byte admission, fetched
  execution, provenance separation, pilot-first adapter, witnesses and
  refusals exactly as cut in CUTS. Full source-to-final-bytes validation,
  TSO/GX bridging and wider memory encodings remain OPEN and are not
  granted by this verdict.
- Evidence: independent full read, name/arity/manual cross-checks, and
  a reproduced `./lean-probe` green (0 errors, standard axioms) against
  current master; temporary probe files reverted, final tree clean.
