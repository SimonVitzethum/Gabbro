# MUSE-REPORT-1386: Exact re-review of candidate 1385 (repair turn)

Lane 1386, clone `/home/simon/Dokumente/gabbro-muse/a1386`, branch `muse/1386`
(verified `.git/HEAD`; `git status` clean apart from this report at review
time). No push (lane rule). No other agent/model calls.

Reviewed candidate: author lane 1385, new pinned HEAD
`cb313f75cbbf8b9d42e9203d78accba4012eee0c`
(read from the NEW `.tmp/review/SNAPSHOT.json`; the stale `e6dade7f` snapshot
is not approved here). Author clone never touched. Delivered files reviewed:
`PATCH.diff` (exactly 3 files: `MUSE-REPORT-1385.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/GvAtomRely.lean`),
`OWNER-TASK.md`, `BUILD-EVIDENCE.json` (now with green runs),
`MUSE-REPORT-1385.md` (repair turn, claims GREEN).

CANDIDATE: 1385 cb313f75cbbf8b9d42e9203d78accba4012eee0c

VERDICT: ACCEPT

## 1. Disposition of the previous REPAIR findings (all closed)

1. **Green measurement — CLOSED and independently reproduced.** Author
   evidence (BUILD-EVIDENCE, complete-output first lines): `./lean-probe` →
   `== 0 error(s)`, exit 0, with all seven `#print axioms` outputs
   (five theorems on exactly `propext, Classical.choice, Quot.sound`, two
   `decide` helpers on `propext` only); `./lean-bau` → `== exit 0;
   0 error line(s)`, `Build completed successfully (718 jobs)`. Reviewer
   independently ran `./lean-probe` on the exact delivered candidate file in
   the reviewer clone: `== 0 error(s) in the COMPLETE output; exit 0` with
   byte-identical axiom lists. Reviewer baseline `./lean-bau` on the clean
   tree: `Build completed successfully (717 jobs)`.
2. **Witness gap (rule 13) — CLOSED.** The 104 witness now carries an
   explicit `TraegerSchreibt (D := G104_referenz_oblig.gD)
   g_einzahlen (.inl GTab.Konto) = true` conjunct, factored into two
   standalone proved helpers: `gv_104_ohne_atomar` (`fun g => nomatch g`,
   `propext`) and `gv_104_einzahlen_schreibt` (`by decide`, `propext`).
3. **Elaboration risks — RESOLVED, and measurement caught a real bug static
   review missed.** Bare `hP` resolved to `Gabbro.Grammatik.hP`
   (`RufMaschineG.lean`, over `rufDF`), not the atomic fixture: 9 of the 12
   first-measurement errors. Fixed by fully qualifying every fixture name
   (`AtomarXZeuge.*`, `NIZeuge.*`, `SchwachZeuge.nS`) and shrinking the
   `open` line; `(D := nD)`-style annotations applied throughout. The
   104-witness tuple cascade (`by decide` inside the anonymous constructor)
   was fixed by the same two helpers. The remaining risks from the last
   review (constructor definitional unfolding, `.logik.1` projection) now
   elaborate green, confirmed by the reviewer's own probe run.

## 2. Fresh checks on the new snapshot

- **Forbidden tactics:** text scan over the delivered `grammatik/` files for
  `sorry`/`admit`/`native_decide`/`unsafe`/added-`axiom`/`sorryAx` → no
  match. PASS.
- **Existing files:** `PATCH.diff` touches exactly one existing file,
  `grammatik/Grammatik.lean`, with exactly one added line
  (`import Grammatik.X86.GvAtomRely`); the hunk context matches the
  reviewer's tree tail (the doubled `BeweisAtomar` import above it is
  pre-existing). PASS.
- **Axioms:** standard on all seven theorems, independently reproduced
  (see §1). PASS.
- **Premises, claim vs proof, two-model scope:** unchanged from the prior
  review and still good — every premise used, CUTS honest about what stays
  open (`bruecke/` duty construction, TSO refinement, payload hand-off),
  the obstruction theorem pins atomic-freedom as necessary with the
  required branch-steering body. No desired-correctness premise, no weakened
  guarantee, no fake closure. PASS.
- **Nits (non-blocking, recorded for the merger):** the file's CUTS item 3
  still says "Green measurement itself remains OPEN", stale after this
  turn's green runs on both sides; the author report prose says "five
  `#print axioms` lines" while the file now carries seven. Neither touches
  any proof claim.

## 3. Commit state

- `MUSE-REPORT-1386.md`: this file (only file owned, only file written).
- Own tree otherwise untouched: no candidate file staged, no
  `Grammatik.lean` edit. Last `./lean-bau` result line (clean-tree
  baseline): `Build completed successfully (717 jobs).`
