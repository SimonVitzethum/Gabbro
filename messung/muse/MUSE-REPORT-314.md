# MUSE-REPORT-314: Independent review of candidate 310 (X86/AufrufOpt)

Lane 314, branch `muse/314`, model opencode-go/muse-spark-1.3-contributor.
Independent from author 310. Reviewed ONLY the pinned snapshot in
`.tmp/review/` and its tool-result build evidence. No other clone read,
no candidate code mutated. Own deliverable: this report only.

Pinned snapshot (SNAPSHOT.json): author 310,
head `6bb39c813af1b70f24d5f8bdabeae3e45339c30e`,
base `345627a46732923a03a5f792ff4050b7e3b7c837`, clean true.
Files: `MUSE-REPORT-310.md`, `grammatik/Grammatik.lean`
(one additive import), `grammatik/Grammatik/X86/AufrufOpt.lean` (new, 288 lines).
PATCH.diff confirms exactly these three paths; no Spec/goal/source/Rust/
counter changes.

Owner task read: lane 310 (`OWNER-TASK.md`), plus `AGENTS.md`,
`dokumente/x86/LEAN-ZUERST.md`, `dokumente/x86/IR-VALIDIERUNG.md` section 3.4.

## What was checked

Actual snapshot file read in full (288 lines). Definitions, statements
AND proofs inspected against the real model files in this clone
(`Folge.lean`, `RufMaschineF.lean` RufEreignisF, `RufMaschineG.lean`
RufSchrittG, `Semantik.lean` rufAt, `FolgeZeuge.lean` Phi50/folge lemmas,
`ZielOrtEinfadenZeuge.lean` eP fixture). Report claims cross-checked
against BUILD-EVIDENCE.json and an independent `./lean-probe` run below.

Candidate contents (namespace `Gabbro.Grammatik.X86`, generic over `{D}`):

- `GeistAntwort D g` (ok v s1 | grund r s1), `geistPaar g rho s0`
  (return over entry, both channels, newest first).
- `InlinePflicht P caller g Lambda` (hp RufPasst, hr gruende=0, actual
  rho/s0/s1/val, vorOk/nachOk with exact rufAt eval shapes).
- `geistPaar_laenge`, `geistRekon_folge` (value channel),
  `geistRekon_folge_grund` (reason channel), `rufSchrittG_logSchritt`
  (per-step log classification over real RufSchrittG),
  `rufAt_ok_vorOk` (entry-duty extraction from successful rufAt),
  `geistRekon_zeuge` (joint witness on eP).
- `CUTS` block plus `#print axioms` for each main theorem.

## Findings (all gates hold)

1. Build/proof evidence reproduces. Independent run
   `./lean-probe` on a scratch copy of the snapshot file:
   `== 0 error(s) in the COMPLETE output`, axiom lines identical to
   the report: first three theorems `[propext]`, remaining three
   `[propext, Classical.choice, Quot.sound]` (standard goal set).
   BUILD-EVIDENCE.json final entries agree (`lean-probe` 0 errors with
   all six axiom prints; `./lean-bau` 372 jobs green; final commit
   `6bb39c81` matches the pinned HEAD). Intermediate red probes in the
   evidence are development trace, not the delivered state.
2. No forbidden tactics/axioms. Snapshot grep: no `sorry`, `admit`,
   `native_decide`, `unsafe`, no `axiom` declaration, no `intro _` /
   `have _ :=` discard. Every theorem premise is used by its proof
   (geistRekon pair: conclusion `⟨hord2, hord1, hrest⟩` consumes all
   three; rufSchrittG: `cases h` over the real step relation;
   rufAt_ok_vorOk: `cases n`, `simp [rufAt] at h`, decided entry check).
   No premise typed `Prop` itself.
3. No assumed desired result. `geistRekon_folge*` premises are computed
   `Bool`s (`Pflichtig`/`Armiert`) plus physical `FolgeLog rest`; no
   trace equality is assumed. `rufSchrittG_logSchritt` is case analysis
   over the real step relation (0-error compile covers every
   constructor, silent vs single-push with actual values);
   `rufAt_ok_vorOk` derives the entry check from the `rufAt` equation.
4. Contracts at their place. `InlinePflicht` stores actual rho/s0/s1/val;
   vorOk/nachOk use actual values with the exact `rufAt` read shapes
   (Signatur.anfang/requires Orte at entry, vertragVon ende/ensures Orte
   at return, ergEnv). Nothing quantifies parameters/results away. The
   return half (`nachOk`) is STATED only and honestly marked OPEN in
   CUTS; no inferred ensures is claimed proved.
5. No fake model, no scope overreach. All events are `RufEreignisF`
   with actual values; order is real `FolgeLog`; no new syntax, no Spec
   change, no x86 bytes/TSO/cost/hardware claims. Indirect calls,
   duty discharge (hp/hr carried, not discharged), body-splice
   simulation (correctly noted to need phase-B QUELLBRUECKE lowering),
   bounds/budget and SCFG/target bridge are explicitly OPEN in CUTS
   and in the author report. IR-VALIDIERUNG section 3.4 asks for direct
   AND indirect ghost forms plus maps/duties/recursion guards; the
   candidate delivers the direct-call source-side checked
   reconstruction and labels the rest OPEN, which is exactly the
   fallback the owner task permits. Honestly labelled cuts are not bugs.
6. Generic, no name-specific rule. Definitions/theorems quantify over
   arbitrary `D`, `g`, actual values; `eP`/`eSetze`/`ePruefe`/Phi50
   appear ONLY in `geistRekon_zeuge`. No per-program rule.
7. Joint non-degenerate witness holds. `geistRekon_zeuge` reaches M5
   (start + call setze + assignSlot write + return + call pruefe +
   return), shows `konto` written by setze (schreibt true by rfl),
   start slot 0 by rfl, entry world slot 5 via the certified contract
   leg (`eP_zertifiziert` + `of_decide_eq_true`), real log
   `rueck pruefe :: eintritt pruefe :: rueck setze :: rest`,
   `geistPaar` equality by rfl, `Pflichtig`/`Armiert` true by rfl,
   `FolgeLog` by `folgeG_erreichbar`. Memory-changing step present;
   not decorative, not an empty run or table-less declaration.
8. Report accuracy. Owned-files claim, theorem-name list, build lines,
   axiom sets, and OPEN list all match the snapshot file and the
   reproduced probe output. Nothing in the owner task appears wrong;
   the fallback path was taken as written.

No material defect found. No counterexample to reproduce (no finding).
The bounded claim -- source-side ghost-event obligation plus generic
step/entry lemmas with a jointly inhabited table-write witness -- is
true. This does NOT close IR-VALIDIERUNG section 3.4, the SCFG bridge,
or any source-to-binary chain; those remain OPEN as stated.

CANDIDATE: 310 6bb39c813af1b70f24d5f8bdabeae3e45339c30e
VERDICT: ACCEPT
