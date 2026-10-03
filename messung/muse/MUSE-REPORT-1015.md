# MUSE-REPORT-1015: Exact review of author 865 (dead-code rule)

Lane 1015, clone `/home/simon/Dokumente/gabbro-muse/a1015`, branch `muse/865`? No:
`muse/1015`, verified at session start (`git rev-parse --show-toplevel` +
`git branch --show-current` returned this clone and `muse/1015`; HEAD
`b040b155`, the recorded base). Owns ONLY this file. No source file was
touched; no network, no other clones, no keys.

CANDIDATE: 865 b48e3f02c78ea13131aa7618a570e9d92f84a00e

VERDICT: ACCEPT

Bounded scope of this ACCEPT: semantic/architectural acceptance of the exact
pinned snapshot as delivered under `.tmp/review/author-865/`; build
greenness per the author's recorded queued-wrapper evidence below; the
merge gate re-runs the build mechanically before integration.

## What was reviewed

- `OWNER-TASK.md` (task text), `MUSE-REPORT-865.md` (author report),
  `BUILD-EVIDENCE.json` (22 queued-wrapper records), `PATCH.diff`
  (902 lines), `SNAPSHOT.json`
  (`author 865, head b48e3f0…, base b040b155, clean true`),
  and the exact snapshot file
  `.tmp/review/author-865/grammatik/Grammatik/X86/OptDceDead.lean`
  (773 lines, read in full).
- Canonical sources in my own clone at the same base `b040b155`:
  `Semantik.lean` (`Expr.orte`, `eval`, `World.lese`, `execStmt`,
  `execBlock`, `gleitLit` arm), `KostenG.lean` (`kostenStmt`,
  `kostenBlock`), `CFormenI.lean` (`Var.idx`, `Var.idx_inj`,
  `Env.get_set_other`), `ReferenzB.lean` (witness fixtures),
  `Syntax.lean` (`vertragVon`), `Maschine.lean` (`keinRuf`).
- Official local reference registry
  `.tmp/HARDWARE-REFERENCES/REFERENCES.json`: Intel SDM combined
  volumes 1-4, edition 325462-093US (Sept 2026), Intel-profile only,
  no AMD snapshot. The candidate adds no x86 byte form, so no SDM
  instruction semantics is exercised; the applicable review surface is
  the interaction with canonical execution, verified below.

## Scope check (PATCH contents)

Exactly three files: new `MUSE-REPORT-865.md`, one added import line
`import Grammatik.X86.OptDceDead` in `grammatik/Grammatik.lean`
(after `ComposeImageFetch`), new
`grammatik/Grammatik/X86/OptDceDead.lean`. No diagnostic/gift/example/
CLI numbers, no MARKE changes, no source/checker/Spec/goal/emitter
edits, no friend-reserved optimiser files. Scope is clean.

## Findings (each checked against canonical definitions)

1. Purity premise is sound. `hRein : e1.orte = []` genuinely means "no
   shared read": canonical `Expr.orte` (`Semantik.lean:160-175`) lists
   `.glob`/`.altGlob` as `[.inr g]` and every table-reading form
   (`.slot`, `.durch`, `.altSlot`, `.leseBytes`, `.forallSlots`,
   `.existsSlots`, `.reaches`) with its `.inl t`. `execStmt assignVar`
   (`Semantik.lean:712-714`) reads exactly `σ.lese Λ e.orte`, and
   `lese_nil` (proved by `simp [World.lese, World.merke]`) makes the
   empty read a no-op on worlds AND traces (`World.lese` appends one
   `Ereignis` per Ort, `Semantik.lean:89-92`). So the removed write
   appends no trace event: the spin-load failure case is really
   refused, and `dceSpin_beobachtet` exhibits the positive direction
   (one shared read = exactly one event).
2. Deadness premise is load-bearing and handled. The author correctly
   notes the purity-only statement is FALSE (`e2 = .var x`
   counterexample); `hTot : liest e2 x = false` plus the `eval_set_frisch`
   frame lemma (induction over `Expr.rec`, all constructors covered --
   the file compiled, so the match is exhaustive) discharge it.
   `liest (.var y) x = decide (y.idx = x.idx)` is sound via canonical
   `Var.idx_inj`/`Env.get_set_other` (`CFormenI.lean:99-131`).
3. The one suspicious proof step resolves in the author's favour. In
   `eval_set_frisch` the `.durch` case rewrites only the index
   hypothesis, never the pointer-operand hypothesis. This is sound
   because canonical `eval` IGNORES the pointer operand
   (`.durch _ t _ f i _, σ, ρ => σ.slots t (eval … i …).n f`,
   `Semantik.lean:221`); `liest` still descends into `p`, i.e. the
   analysis over-approximates in the sound direction. Same for `orte`
   (`p.orte ++ …`), which can only cause extra refusals, never an
   unsound removal.
4. Fault preservation holds. Canonical `eval` is TOTAL into `Wert`
   (division carries proof arguments, `.div h0 h1 a b`); `execStmt
   assignVar` always returns `.ok` and never faults. The main theorem
   proves `execBlock` OUTCOME equality, which therefore covers value,
   fault class, successor worlds/envs, downstream contract reads at
   their place, and call logs (the window holds no call). IEEE is
   covered by refusal, not by rewriting: trap-capable float ops live
   only at `Block` level, the rule fires only on `Stmt.assignVar`, and
   `dceVerweigert_gleit` exhibits the faulting `gleitLit`
   (`gleitPasst … = none` by `decide`, matching the canonical
   `gleitLit` arm at `Semantik.lean:865-866`).
5. No guarantee weakened, no desired simulation assumed. Nothing
   derives `ensures`; refusals stay refusals (`dceVerweigert_orte/_tot`
   decide to `false`; no warning path); no faulting form is speculated
   above its guard; quantified bodies conservatively answer `true`.
   Budget is a proved inequality (`kostenStmt assignVar = 1 +
   kostenExpr e`, `kostenBlock (cons…)` additive, closed by `omega`);
   exhaustion timing stays OPEN and is said so.
6. Witnesses are joint and non-degenerate. `OptDceDead_verbindung_zeuge`
   instantiates ALL premises (`x = 5` overwritten by `x = 7` before
   `nil`) AND the non-degeneracy conjuncts (`refEin_schreibt`,
   `refB_erreicht`, `refB_schreibt` -- all present in `ReferenzB.lean`).
   Same pattern for `eval_set_frisch_zeuge`, `dceKosten_faellt_zeuge`,
   `dceVerweigert_gleit_zeuge`. Every premise of every theorem is used;
   no `Prop`-typed premise; no conclusion-restates-premise; no
   discarded premise.
7. Hygiene. The snapshot file contains no `sorry`/`admit`/`axiom`/
   `native_decide`/`unsafe`/`intro _`/`have _ :=` (only prose matches
   for "admits"/"Probe:"). CUTS block plus `#print axioms` for every
   main theorem are present (lines 734-771). Minor note, not a repair:
   the three `probe_` decide-lemmas have no `#print axioms` line; they
   are auxiliary and closed by `decide`.

## Build evidence (author-recorded, not re-run by me)

- Final `./lean-probe grammatik/Grammatik/X86/OptDceDead.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`, with every new
  theorem on subsets of `propext, Classical.choice, Quot.sound`
  (the `gabbro_ziel` standard; full per-theorem list in evidence).
- Final `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE
  output`, `Build completed successfully (511 jobs)`.
- The evidence also shows the honest path there (intermediate 32-,
  26-, 5-, 4-, 3-, 1-error states, all repaired in-file).

## What remains open (carried from the author's CUTS, agreed)

Non-overwrite deadness (whole-block liveness), block-window float
rewrites, `budget_simulation` exhaustion timing (lane 278), and the
full target chain (silicon correspondence, TSO/GX bridge, ABI/loader)
-- all explicitly not claimed. The hardware checklist of my task
(REX/width/flags/operands/TSO/MXCSR/interrupts) has no review surface
here beyond the canonical-execution interaction: the file adds no
`Befehl` evaluation and reuses `Ausfuehrung.schritt` untouched.

## Task notes / anything believed wrong

Nothing in the owner task is believed wrong. One clarification for
future hardware lanes: the my-task hardware checklist (byte forms,
REX, flags, TSO, MXCSR, interrupts) is largely inapplicable to a
source-level optimiser rule; I applied its "interaction with canonical
execution" leg fully and recorded the boundary instead of inventing
hardware findings.

## Process status (updated after first commit)

The `bash` tool was refused once by the permission classifier mid-session
(on a read-only inspection command) but worked again afterwards. The
report was committed as `d1dfa06e` on `muse/1015` via `./commit.sh`
(`git status` showed only `?? MUSE-REPORT-1015.md` before staging, so no
stray files were committed). This section supersedes the original
blocker note below, which is kept for audit.

Original note: build greenness could not be re-run from this lane
(`./lean-probe`/`./lean-bau` need the shell, which was momentarily
refused); the verdict rests on full-snapshot inspection plus the
author's recorded queued-wrapper evidence, and the merge gate's
mechanical build check remains the binding greenness proof.
