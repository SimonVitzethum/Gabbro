# MUSE-REPORT-477: Independent exact-candidate review of 429

Lane 477, branch `muse/477`, clone `/home/simon/Dokumente/gabbro-muse/a477`.
Task: independently inspect the exact `.tmp/review/SNAPSHOT.json`, author-429
task, PATCH, code/doc and actual build evidence for material semantic
correctness against accepted models and trust boundaries.

## Candidate under review

- Snapshot: author 429, base `0b3132b7`, head
  `8528125ffb7f84e6d3360de36fd978074b981aa1`, clean true.
- Files: `MUSE-REPORT-429.md`, `grammatik/Grammatik.lean` (one additive
  import line), `grammatik/Grammatik/X86/CodeImmutability.lean` (new, ~300
  lines). PATCH.diff (424 lines) matches exactly these three files.
- Bounded claim: a successful `write64` whose 8-byte footprint is disjoint
  from the whole 15-byte fetch window at `rip` (`CodeFremd`) preserves the
  fetched bytes (`geholt`), the decode outcome (`fetchDekodiert`) and every
  fetched code byte; plus a memory-changing disjoint-store witness, an
  overlapping-store counterexample, and wrap/range correctness. Whole-source
  self-modifying-code refusal explicitly left separate (CUTS).

## What I did

1. Verified clone path and branch (`muse/477`); did not read any other clone.
2. Read OWNER-TASK-429, MUSE-REPORT-429, BUILD-EVIDENCE.json and the full
   PATCH.diff.
3. Checked every used dependency resolves to an accepted definition in my
   own clone's base: `addrOff`, `addrOff_null`, `write64`,
   `write64_erhaelt_berechtigungen`, `write64_rahmen` (Speicher.lean);
   `write64_trifft` (SpeicherKommutation.lean); `fetchCap`,
   `ausfuehrbarN`, `holeFetchAux`, `geholt`, `fetchDekodiert`,
   `geholt_laenge_le`, `ketteStart`, `ketteReg`, `witnessFlags`
   (Byteschritt.lean); `natByte` (Codec.lean). All present, all accepted.
4. Staged ONLY the supplied candidate module file into my clone (umbrella
   left untouched) and ran the queued `./lean-probe` on it. Result:
   `== 0 error(s) in the COMPLETE output; exit 0`, with `#print axioms`
   for all 11 names exactly as the report states (`propext` and/or
   `Quot.sound`; `umbruch_alias` axiom-free; no `sorryAx`). Removed the
   staged file afterwards; clone is clean again.
5. Textual hard-rule scan of the candidate file: no `sorry`, `admit`,
   `axiom` declaration, `native_decide`, `unsafe`, `intro _`, `have _ :=`,
   or contract-quantifier games (the only "axiom" substring hits are the
   11 `#print axioms` lines). Imports are the four accepted X86 modules
   only; friend-owned optimiser files, source checker, Spec, goal, Rust,
   emitter, Typen and Codec untouched.

## Semantic findings (all checked, none blocking)

- No circularity: `CodeFremd` is an address-disjointness premise on the
  particular store, not the desired preservation conclusion. The
  over-approximation (whole 15-byte cap instead of actual fetched length)
  is a slightly stronger premise, still satisfiable via `wFremd`; sound
  and disclosed.
- `fetchDekodiert` preservation correctly needs both the fetch rewrite and
  the `ausfuehrbarN` permission rewrite; the decoder itself is never
  re-trusted. The report's refusal to claim `byteschritt`-outcome
  preservation (successor may read data memory) is the correct boundary.
- `codeFremd_von_intervallen` states both no-wrap hypotheses and
  `umbruch_alias` (proved by `decide`) shows why they are needed. No wrap
  aliasing is assumed away.
- Both witnesses are joint and non-degenerate: the disjoint witness uses
  the accepted chain memory (`ketteStart`), a real `write64` of 42 at
  8192, foreignness, preserved fetch AND decode, and an observable data
  byte change 0 -> 42. The overlap witness uses a real store onto the
  `ret` byte, is provably not foreign, and changes both the code byte
  (195 -> 42) and `geholt` (both `decide`-evaluated, and the module probe
  above confirms they elaborate).
- Every theorem uses all its premises (checked by reading each proof
  against its binder list). No new IR, executor, semantics, or safety
  weakening. CUTS lists exactly what is not proved and matches the task's
  carve-outs. Only 64-bit `write64` covered; stated, mechanical follow-up.
- Build-evidence honesty: the evidence log shows the intermediate red
  probes (rewrite-shape errors, missing `write64_trifft` import with
  `sorryAx`) all resolved to the final green run, which I reproduced
  independently. The `./lean-bau` umbrella crash (`failed to create
  thread`, exit 134) with the stash control (crash recurs without the
  lane's edit) and the un-runnable `gabbro_ziel` check are reported
  plainly as environment limits, not as passes. Nothing is claimed that
  the evidence does not show.
- Base skew note (not a defect): my clone's `Grammatik.lean` carries five
  newer X86 imports (TableLayout, EntryState, NarrowOps, FenceDrain,
  CostSummary) absent from the candidate base, so the candidate's import
  line will land mid-file at merge; standard import-union resolution
  covers it. The merge gate still needs one working full-project build to
  confirm the umbrella import, as the author report itself states.

## Defects requiring repair

None. No repair direction to give.

## Scope of acceptance

ACCEPT covers precisely the delivered bounded claim above: fetch, decode
and code-byte preservation under disjoint `write64`, the two joint
witnesses/counterexample, and the interval/wrap bridge, with standard
axioms and the stated CUTS. It is not full compiler closure, not a
whole-source self-modifying-code refusal, not a byte-step outcome claim,
not concurrency/coherence, and not 1/2/4-byte stores.

CANDIDATE: 429 8528125ffb7f84e6d3360de36fd978074b981aa1
VERDICT: ACCEPT
