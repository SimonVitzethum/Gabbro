# MUSE-REPORT-16 (lane 16, draft A)

## What I did
Wrote `dokumente/SATZKARTE-A.md` (English, no Lean changes): a theorem map for
`Gabbro.Grammatik.ziel_nutzer_last_aus_pc_Q` (`grammatik/Grammatik/Ziel.lean:2324`).
One plain-English sentence per conjunct of the 12-way conclusion (C1–C12), with the
exact discharging lemma for each leg read off the proof term (`Ziel.lean:2417-2428`);
one table row per premise with name, one-sentence meaning, class
(OWN-LOGIC / NAMED-HW / GABBRO-DUTY / OPEN / DATA), and the exact Lean theorem that
discharges it or "none". Every claim verified by reading the Lean, cited as file:line.
Flagged 10 premises/legs whose meaning makes the theorem inapplicable to ordinary
programs (strongest: `hSeedAll` demands `Post` at entry; `hForm` restricts contracts to
invariant form; `hJw`/`hJsf` wiring closable only for single-thread runs while C12
needs two threads).

## New definitions/theorems
None. No Lean files touched (`git status` shows only `dokumente/SATZKARTE-A.md` and
this report as new files).

## Last `./lean-bau` result line
`Build completed successfully (29 jobs).` (run after writing the doc; tree unchanged)

## What remains open
Nothing in this lane: the draft is complete as specified. The substantive open items
it records (chain-to-machine wiring for two threads, write-fragment `hBlattAll`,
global watch, per-use `deadlineSpacing`, `hSeedAll` Post-at-entry) belong to other lanes.

## What I believe is wrong in the task
Nothing wrong. One note: the task says "section 13" for the Q theorem, but in the
current tree it stands under the `## 13` header comment at `Ziel.lean:2283` with the
theorem itself at `:2324` — same object, just confirming the reference.
