HARD RULES (all agents of the AArch64 direction; read them, they bind you)
1. Work only inside your own clone (your current directory). The Sail sources are readable at
   `/home/simon/Dokumente/gabbro-arm/src/sail-arm` and `/home/simon/Dokumente/gabbro-arm/src/sail` (READ ONLY, outside your clone).
   No network, no `git push/fetch/pull/remote`, no `ssh`, no `curl`/`wget`, no package installs, nothing in `/tmp` (your scratch is `./.tmp`).
2. Check Lean ONLY through the wrappers: Arm agents `./arm-bau` (builds `arm/`) and `./arm-probe <file.lean>`; GabbroV agents `./lean-bau` and `./lean-probe <file.lean>`.
   Their first line is the error count of the COMPLETE output. Never call `lake`, `lean` or `cargo` directly.
3. No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`. No premise whose type is `Prop` itself. Every premise of every theorem must be used by its proof.
   Every theorem with a universally quantified premise needs a witness (`_zeuge`) on a NON-DEGENERATE fixture; a theorem that holds because its premises are unsatisfiable is a finding, not a result.
4. TOOLCHAIN: Lean 4.33.1, NO mathlib. Use only tactics and lemmas that exist here: `split` (never `split_ifs`), `omega`, `decide`, `simp`, `rfl`, `rw`, `cases`, `induction`.
   `norm_num` and `ring_nf` do not exist. Every `BitVec.*` or helper name is grepped from the toolchain sources or the tree BEFORE you use it; `unknown identifier` means a wrong name, not a missing feature.
5. WORK IN SMALL PIECES. First a skeleton of at most 60 lines, check it, commit when green. Then ONE definition or lemma at a time, check, commit. Never write a file of hundreds of lines and check it once.
6. DO NOT END YOUR TURN while work is pending. After every tool result go on with the next step. If you are stuck, commit the green partial, write the report with the precise blocker, and stop only then.
7. SILICON FIRST. Semantics must match the Arm specification as written in the Sail source: every semantic definition carries a comment citing the Sail file and line it translates (path relative to `sail-arm/arm-v9.4-a/src`).
   Behaviour that Arm calls UNPREDICTABLE, CONSTRAINED UNPREDICTABLE, IMPLEMENTATION DEFINED or UNKNOWN stays FREE: model all allowed outcomes, never one observed value. Never invent behaviour; where the source is unclear say so in the report.
8. REUSE, DO NOT DUPLICATE. Shared vocabulary is `arm/Arm/Basic.lean` (FROZEN, do not edit; propose changes in your report). Edit only the files of your own task. Other agents' work reaches you only when the coordinator merges it.
9. Every Lean file ends with a comment block `CUTS:` listing exactly what is not proved or not covered, plus `#print axioms` for each main theorem (standard axioms only: propext, Classical.choice, Quot.sound).
10. English only in code, comments, documents and commit messages.
11. COMMIT on your branch: write the message to `arbeitsprotokoll/.commitmsg` (`mkdir -p arbeitsprotokoll` first), `git add` the files, run `./commit.sh`. End the message with the line `Co-Authored-By: opencode muse-spark-1.3-contributor`. Commit after every green step.
12. REPORT: keep `REPORT-<your number>.md` in the repository root current and committed: what you did, exact names of new definitions and theorems, the last build result line, what is open, and an honest CUTS section. Update and commit it at the end of every substantial step, not only at the end.
13. HONESTY. Claim nothing bigger than the proof. Measured and assessed are different words. Never weaken a statement to make it check; if it does not check, record the obstruction.
14. A statement that needs a premise you cannot prove is recorded as an open obstruction in the report, never assumed silently.

16. (2026-10-07) You may edit `crates/*` (the checker) as well as `grammatik/*`; build and test the checker only with `./cargo-pruef-check` (never the workspace-wide suite). New refusal codes come only from AGENTS.md section 7, each with its sentence in `saetze.rs` and a poison probe. The emitted C backend is deprecated: add nothing to it. After the hardware model the compiler stage follows (ARM-PLAN.md): performance goal min. 80 %, target 110 % of GCC -O3, invariant analysis mandatory.

17. (2026-10-08) Mathlib is allowed everywhere, including `grammatik/` (pinned to v4.33.1; `import Mathlib.Tactic.Ring`, `Mathlib.Tactic.NormNum`, `Mathlib.Order...` work; `ring`, `norm_num`, `positivity`, `linarith` are available in modules that import them). Do not add the dependency to a lakefile yourself; `gabbro_ziel` axioms must stay exactly propext, Classical.choice, Quot.sound.

18. (2026-10-08) BUILDS: Lean builds now run ONE worker at a time inside an 8 GB memory cap (5 GB Lean heap). A build takes several minutes: wait for it, never start a second build in parallel, never kill a waiting build call. If a build died of memory (exit 137, "oom", "excessive memory consumption"), that was the apparatus: rerun it once; if the SAME single module dies again, do not ask for a bigger cap: split the module or narrow its Mathlib imports (never `import Mathlib` as a whole) and say so in your report. A "staged/unverified" result caused by such a death must be rerun and verified before you report it.
