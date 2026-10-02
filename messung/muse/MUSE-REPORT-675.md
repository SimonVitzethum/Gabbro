# MUSE-REPORT-675: Exact review of author 674 (SIMD enabled-state gates)

CANDIDATE: 674 7916dce7f062f4c1379978e241645696c6249ff2
VERDICT: ACCEPT

## Scope and method (full-scope second pass)

Report-only exact review of the unchanged pinned candidate. After a
format gate and a completeness objection I re-read the FULL owner task
(`.tmp/review/author-674/OWNER-TASK.md`, all 24 lines; the long task
line is 2377 chars, read in three bounded ranges — the earlier
"truncated" remark was a 2000-char tool-output limit, not the task
length) and checked the candidate against EVERY requirement below.
I own only this report; no source file was added or modified. Clone
and branch verified first: `/home/simon/Dokumente/gabbro-muse/a675`,
branch `muse/675`. Snapshot: `.tmp/review/author-674/` (PATCH,
761-line `VectorHardwareProfile.lean`, author report, OWNER-TASK,
BUILD-EVIDENCE, SNAPSHOT). PATCH touches exactly the new module, one
additive `Grammatik.lean` import line, and the author report.

## Requirement-by-requirement mapping

1. Read design tiers, official encodings, CPUID/XCR0/OSXSAVE/CR0/CR4
   rules, current producers. The author lists producers as read; the
   manual file was absent in his clone at his check (his evidence
   shows `.tmp/` holding only `LANE.md`, `opencode`). I verified the
   load-bearing manual rows independently in my local verified SDM
   snapshot (325462-093US, Sept 2026): `66 0F EF /r` PXOR and
   `66 0F D4 /r` PADDQ (SSE2); legacy operation with
   `DEST[MAXVL-1:128]` unmodified; Flags None; Numeric None; Table 2-21
   Type 4 (#UD on CR0.EM=1, CR4.OSFXSR=0, CPUID 0, LOCK prefix;
   #NM on CR0.TS=1; #GP on misaligned legacy-SSE memory); MOVDQU needs
   no 16-byte alignment. The candidate cites no manual heading/page —
   openly, in CUTS — and claims no silicon correspondence. No false
   provenance claim exists to repair; the architecture I verify below
   stands on accepted producer theorems plus these rows.
2. Close enabled-state and actual byte-execution admission for the
   selected tier through canonical state and the accepted
   `ExtendedExecution` dispatcher. Done: `hwVektorBereit`,
   `vektorHwZugelassen`, `stepVectorHw`, `stepExt_vec_hw`,
   `vectorHw_fetch_bridge`. No interpreter duplicated (`skalarPaar*`
   are pure word functions over accepted `xorB`/`addB`, feeding no
   execution path).
3. Replace the bare `osXmm` Bool. Done as a safe refinement in the
   admission direction: `osXmm` stays one conjunct of four, and
   `vektorHw_verfeinert` proves the checked gate implies the old
   `vecEintritt`. Guarantees only strengthen.
4. Width/lane/upper-lane effects; alignment faults; per-access
   footprint/tearing; no auto-atomicity. Proved: `vektorBreite_spur`,
   PXOR lanes 0+1, PADDQ lane 1, rFLAGS preservation, `vektorGpFehler`
   classification, `vektorHw_fuss`, `vektorHw_teilt` (torn state
   restated, atomicity explicitly disclaimed). Partial by explicit
   enumeration: no PADDQ lane-0 restatement (follows from the accepted
   producer in ~3 lines via `stepVectorHw_gleich`; nothing claimed
   about it).
5. AVX2: exact CPU/XCR0 readiness bound to the admitted form, or
   refusal / proved scalar fallback with same observable outcomes.
   The 256-bit row always refuses (`stufe_avx256_verweigert`, rfl);
   `stufenCpuBereit`/`xcr0AvxBereit` exist as conservative scaffolding
   feeding no admission (verified by grep — only `avx_braucht_xcr0`
   uses them), and CR4.OSXSAVE is not consulted, which is safe exactly
   because the row refuses unconditionally. The xor fallback has full
   lane-by-lane equality (`skalarPaarXor_gleich`); the add fallback has
   only the two half projections (no `skalarPaarAdd_gleich`). The
   author's report enumerates half lemmas without claiming the add
   equality, so this is bounded incompleteness, not an overclaim, and
   nothing executes through either fallback.
6. Codec plus lanes is not silicon fidelity. Honored: round-trips are
   reused from the producer, never presented as hardware proof; CUTS
   keeps silicon correspondence OPEN.
7. Joint fetched vector memory-changing run; CPU/XCR0/control/
   alignment/alias negatives; true template obligations named. The
   joint witness decodes pinned canonical PXOR bytes with consumed
   length, admits the gate, runs the gated step and the unified
   dispatcher to the same successor, and closes a real byte change
   (`decide`) through a chained existing MOVSD store — explicit in the
   theorem, required because the admitted register forms correctly
   touch no memory. Seven negatives cover missing CPU, XCR0, controls,
   OS bit, misalignment, alias overlap, unknown opcode. The module
   creates no templates or Schablonen entries (verified: zero
   mentions), so there are no created template obligations to name;
   the reused `vecZeuge*` chain belongs to the producer.
8. Adapter export for 660/validator consumers. Done:
   `vektorValidatorZugelassen` with both projections plus the fetch
   bridge. Consumer acceptance is that lane's business.
9. Unimplemented AVX2/VEX/raw-bit/fault/context rows stated, not
   marked done. CUTS lists: register-forms only (no vector memory
   opcode, no packed-FP lane, no VEX/AVX encoding, no other SSE2 row);
   execute permission as adapter conjunct, no constructed loaded
   image; no TSO/GX/source/budget/progress/call-log; `simdFreigabe`
   untouched (single mention, in CUTS); OS configuration and
   context preservation declared user logic in the §1 docstring.
10. Priority clauses: canonical-state reuse yes; only checked inputs
    assumed (silicon correspondence OPEN); admitted bytes run through
    the common dispatcher (bridge theorems are proved identities, all
    premises used, no assumed simulation); unsupported encodings refuse
    explicitly; producer `.b32`/`.b64` label tension stated side by
    side, never redefined; own-files-only honored; no forbidden
    tactics (precise grep clean), no `Prop`-typed premises, no
    discarded premises; axioms within the standard set per final green
    evidence (intermediate `sorryAx` states were repaired before the
    final commit); `gabbro_ziel` untouched (leaf import only).
11. No producer drift: all six producer files are byte-identical
    between the candidate base `1d08711` and my HEAD; the only
    `Grammatik.lean` delta is the unrelated merged
    `FloatValidatorAdmission` line (standard import-union at merge).

## XCR0 reframing (conservative admission restriction)

The XCR0 x87&&SSE conjunct is NOT an architectural SSE requirement —
Table 2-21 imposes XCR0 only on VEX rows, and pre-XSAVE silicon has
no XCR0 at all. I treat and record the gate as a conservative compiler
admission restriction: it refuses a superset of what hardware refuses,
so every admission is sound while some hardware-valid executions
(pre-XSAVE machines, XCR0-unset states) are refused by the gate. That
incompleteness, like the REX-required decoding strictness inherited
from the accepted producer, is safe-direction and stays OPEN. The
candidate text never claims hardware faults without XCR0 (its refusal
theorems speak of the gate), so no material false architectural claim
exists here.

## No inferred execution

`vektorSchreibZugelassen` feeds no step (verified: used only by its
two lemmas and one negative); `stufenCpuBereit` feeds no admission;
no vector memory opcode, context switch, or AVX2 execution is
constructed anywhere — declarations and gate helpers stay
declarations and gate helpers. Memory-fault delivery, context
preservation, and AVX2 execution remain unimplemented and are stated
as such.

## Reproduction note

No case survived static verification at the suspicion threshold:
every bridge is a proved identity over producer theorems, every
negative is `decide`/`rfl`/exact-reuse, the joint byte change is
`decide`-closed, and the manual rows above were re-checked against
the local snapshot. I deliberately did not burn the shared Lean slot
on a redundant rebuild: `grammatik/.lake` holds no warm X86 oleans
here, the producers are byte-identical to the candidate base, and the
evidence log already records the full green build (460 jobs) with
standard axioms at the pinned commit. Re-deriving it would add no
information.

## Exact accepted partial scope

Admitted: two 128-bit legacy-SSE register forms (PXOR `66 0F EF /r`,
PADDQ `66 0F D4 /r`, REX-canonical only) under silicon-SSE2 + XCR0 +
control + OS-bit admission, executed through the unified dispatcher.
Explicitly not done: every other SSE2 row, packed-FP lanes, vector
memory opcodes, VEX/AVX/EVEX, YMM state, loaded-image construction,
TSO/GX refinement, source correspondence, budgets, progress,
call logs, `simdFreigabe`, manual provenance. Full hardware-model
closure is neither achieved nor claimed.
