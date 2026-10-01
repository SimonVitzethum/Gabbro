# MUSE-REPORT-384: Independent exact-candidate C2 review of 346 GateStub

## Candidate under review

- Author lane 346, pinned HEAD `232765e464a2ad6e5e23ee72728d317d3da26820`, base
  `f737a6f04c22dfdd9499532e0535ad119cf2e56d` (base is an ancestor of this clone's
  HEAD; review run on branch `muse/384` at `b5267bd4`).
- Owned files per snapshot: `MUSE-REPORT-346.md`, `grammatik/Grammatik.lean`
  (one additive import), `grammatik/Grammatik/X86/GateStub.lean` (389 lines).
- Staged privately in this clone (file copy + appended import), probed, built,
  then fully restored (`git status` clean apart from this report). No other clone
  read, no network, no push.

## What was checked

1. `./lean-probe grammatik/Grammatik/X86/GateStub.lean`: **0 errors**. Axioms all
   within `[propext, Quot.sound]` (`torStub_zeuge`: `[propext, Quot.sound]`).
2. Full `./lean-bau` with candidate staged: **Build completed successfully (387 jobs).**
3. Goal probe: `'Gabbro.Grammatik.Zielsatz.gabbro_ziel'` on
   `[propext, Classical.choice, Quot.sound]` — unchanged.
4. Strict `grep -nwE "sorry|admit|axiom|native_decide|unsafe"`: single hit is the
   English noun in a CUTS comment ("never a hardware axiom", line 354), not a
   command. No `intro _` / `have _ :=` discards. No `Prop`-typed premises; every
   theorem is ground (`decide`/`rfl`/`refine` using all components).
5. Canonical reuse verified against this clone's sources: `Register` (16 GPR,
   `Typen.lean:13`), `Befehl` mov forms, `roundtrip_movReg64`
   (`Codec.lean:468`), `write_read_zeuge` (real nonzero write/read-back/byte
   change, `Speicher.lean:681`). No second IR, no `exec`/`schritt` duplicate,
   no trap semantics invented (`0F 05` literal shape only). CUTS + `#print axioms`
   present. English only.
6. Source fidelity read against actual code: N063/N064/N065/N066 in
   `crates/gabbro-check/src/syscall.rs:159-292` (positional-index encoding is an
   isomorphic bijection of the nominal binding — equivalent outcomes, fine);
   N067 in `fehlertabelle` (`syscall.rs:293-390`, empty-map edge matches);
   C186 in `emit.rs:9584` (faithful mirror); syscall.stub sentence
   (`saetze.rs:4360`) confirms the `-4095` fence and hardware-outcome decode.
7. Divergence probe (model side, queued): a stack gate with
   `ein={rdi,rsi,rdx}`, `clobber={rcx,r11,r12,r13,r14,r15}`, `aus=rax` gives
   `c187VerweigertB = false` with `freieRufbewahrt = [rbx, rbp]` — 0 errors.

## Findings (material, REPAIR)

- **F1 — C187 pool/occupancy mismatch vs `emit.rs::syscall_stumpf` (GateStub.lean
  lines 96-109).** (a) `rufbewahrt` includes `rbp`, but the emitter's free pool
  is exactly `["r12","r13","r14","r15","rbx"]` (`emit.rs:9949-9953`): `rbp` is
  never pinned (frame pointer). (b) `freieRufbewahrt` excludes only `ein` regs
  and `clobber`, while the emitter's `belegt` is `regs_in + regs_out + clobbers +
  fest_zerstoert` (`emit.rs:9942-9950`): the answer register is not excluded.
  Reproduced: the gate in §7 is admitted by the model yet refused with C187 by
  the emitter (`frei={rbx}`, 1 < 2). Repair: pool becomes
  `[r12,r13,r14,r15,rbx]`, filter also excludes `aus`; both existing witnesses
  (`torStapelOhneTrampolin` still fires, `torStapelZeuge` still clear) stay green
  by construction — author to re-probe.
- **F2 — M140 predicate is vacuous (lines 111-113, 209-217).**
  `m140VerweigertB istZahl benutztAlsZeiger := istZahl && benutztAlsZeiger`
  inspects no site and no type; `m140_geschmiedet` / `m140_echt_kein_fund` are
  `Bool.and` truth-table rows. It cannot refuse anything — the names carry the
  semantics, not the computation. Repair: drop the predicate and both theorems
  and record M140 detection as OPEN in CUTS (a gate-stub declaration mirror has
  no call-site type vocabulary; M140 lives in `m1.rs`), or add a minimal
  inspected site mirror inside the owned file.

## Observations (not repair-grade)

- **O1:** `linuxClobberB` demands declared `rcx`/`r11`, while the emitter
  auto-adds them (`emit.rs:9072,9820,9948`) and no checker rule refuses their
  absence. Task-ordered and matching corpus convention — recorded, not a defect.
- **O2/O3:** N065 positional encoding isomorphic (fine); N066 implicit by
  `Register` construction, openly stated (fine).
- **O4:** `fehlerOkB` matches source including the empty-map/dangling-channel
  edge (both admit; verified by reading `fehlertabelle`, not assumed).
- **O5:** `klassifiziere` range bounds `lo`/`hi` are free profile parameters;
  provenance from the answer-type range is unmodeled, correspondence OPEN as
  CUTS states.
- **O6 merge mechanics:** candidate branched before the SpillPrivate merge; both
  append one import at the end of `Grammatik.lean` — trivial import-union
  conflict, auto-resolvable per the merge script.

## Last build result lines

- Staged `./lean-probe`: `== 0 error(s) in the COMPLETE output`.
- Staged `./lean-bau`: `Build completed successfully (387 jobs).`
- Tree restored before this commit: `git status` clean except `MUSE-REPORT-384.md`.

CANDIDATE: 346 232765e464a2ad6e5e23ee72728d317d3da26820
VERDICT: REPAIR
