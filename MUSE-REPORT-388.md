# MUSE-REPORT-388: Independent exact-candidate C6 review of 350 AtomicPayload

Lane 388, branch `muse/388`. Owns ONLY this report. Candidate snapshot:
author 350 files `MUSE-REPORT-350.md`, `grammatik/Grammatik.lean` (additive
import), `grammatik/Grammatik/X86/AtomicPayload.lean` (354 lines, namespace
`Gabbro.Grammatik.X86.AtomicPayload`). Candidate HEAD hash
`67dd9fd1e6e00d9435a61a868308ef0f5192b156` is NOT in this clone (base drift:
my clone ends at `AccessList`, snapshot base ends at `Byteschritt`); review
was done against the exact snapshot files under `.tmp/review/author-350`,
staged privately (owned module + additive umbrella import), then fully
restored before this commit. Working tree is clean except this report.

## What was checked

- Staged the exact snapshot file + additive `import Grammatik.X86.AtomicPayload`
  at END of `grammatik/Grammatik.lean`; `./lean-probe` on the module:
  **0 errors**; `#print axioms` output identical to the author's BUILD-EVIDENCE
  (all 8 main theorems subsets of `[propext, Classical.choice, Quot.sound]`).
- Full `./lean-bau` with candidate staged: **green, `Build completed
  successfully (393 jobs)`** (393 vs author's 386 is base drift in my clone,
  not candidate content). Staged files removed afterwards; umbrella restored
  byte-identical (`tail` ends at `AccessList`).
- Banned-token scan: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`,
  no `intro _` / `have _ :=` (only comment-text false positives of "admit"
  inside "admitted"). No premise typed `Prop` itself.
- Premise use (all 8 main theorems): every premise is consumed by its proof
  (`hvoll` via `vertragsFreiB_ok`, `hsep` in the `GeteiltV` triple, `h` in each
  refusal, `hA`/`havocA_mono` in the audits, `hp`/`hnatom` in the payload
  theorem). No conclusion-as-premise, no quantified-away contracts, no
  memory-free "semantics" (the only run claim is the real `RufErreichbarW` run).
- Semantic grounding against this clone's actual canonical definitions:
  `GeteiltV = GeteiltA ∧ VertragsFrei` (`Spec.lean`), so the duty audit
  narrowing `GeteiltA -> GeteiltV` via `koerperGutSA_mono`/`invGutSA_mono` with
  `(fun _ hc => hc.1)` is the correct direction; `PaarungAusgenommen` /
  `AtomarAusgenommen` shapes match the `pD` witness exactly;
  `n1_logikA (T)` is universal over `T`, so instantiation at `GeteiltA` is
  legitimate; `vertrag_atomar_echt` confirms the `kern`-ensures witness.
  No source admission tightened, no canonical file touched, no second IR.
- Witnesses: run-carrying witnesses use the real memory-changing W run
  (`konfig` 0 -> 3, `hauptA` writes `tabA`). The pure checker-side refusals
  (`vertrag_*` on `vP`, `nutzlast_*` on `pD`) carry the written-table leg and
  honestly document the run leg at `nP` — acceptable, no fake empty witness.
- Scope honesty: no TSO/LOCK/multi-byte-atomicity/hardware-latency claim; the
  refusal Bool is admission, never a hardware fault; CUTS list the TSO bridge,
  atomic duty construction, and payload residue proof as OPEN.

## Minor notes (not defects, no repair demanded)

- File header comment names the payload theorem `nutzlast_nicht_aufgenommen`;
  actual theorem is `nutzlast_braucht_restbeweis`. Stale doc name only.
- Report says "~360 lines"; file is 354 lines. Trivial.

## Verdict

CANDIDATE: 350 67dd9fd1e6e00d9435a61a868308ef0f5192b156
VERDICT: ACCEPT

ACCEPT covers only the precise bounded delivered obligations (decided
footprint-membership check + admission, contract/payload refusals, duty-side
audit with joint non-degenerate witnesses), not the full compiler/validator.
Changed author hash -> fresh review.
