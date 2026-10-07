# MUSE-REPORT-1352: exact review of candidate 1351 (MOV/TEST/LEA/PUSH/POP/NOP/frame)

Reviewer lane 1352, clone /home/simon/Dokumente/gabbro-muse/a1352, branch muse/1352
(verified). This is a re-review: the previous finding (ACCEPT at c120e731)
is stale after the author repair commit. Under review now is the NEW pinned
head 0a1906c59dfe527aee8d6214bbde2f248f81fe16 (machine-readable lines in the
verdict section below).
Delivered files reviewed: `.tmp/review/SNAPSHOT.json` (new head above, same
base b7b96da86bff9c5966bc0356ec07c6ed0ee21cba, same 3 files, clean),
`.tmp/review/author-1351/PATCH.diff` (2221 lines),
`.tmp/review/author-1351/grammatik/Grammatik/X86/IntMovTest.lean` (1993 lines),
`.tmp/review/author-1351/grammatik/Grammatik.lean` (712 lines),
`.tmp/review/author-1351/OWNER-TASK.md`, `BUILD-EVIDENCE.json` (332 lines),
`MUSE-REPORT-1351.md` (207 lines). No `git show/log/diff` on any pinned hash
was used.

## What the repair changed (re-review delta)

- The repair commit (`0a1906c5`, "integration repair analysis, gate blocker
  recorded", tree CLEAN per evidence) adds exactly one report section
  ("Integration repair analysis", +58 PATCH lines, report 149 -> 207 lines).
  No Lean file changed: `IntMovTest.lean` is still 1993 lines with identical
  header/imports (16 `Grammatik.X86.*` imports, lines 13-28), identical CUTS
  block (lines 1908-1948), identical 42 `#print axioms` lines (1950-1991),
  and no forbidden token (full-file grep for `sorry|native_decide|unsafe`,
  `^axiom `, `admit ` finds only the two long-standing English-prose "admit
  no event" lines 1387/1933). PATCH still touches exactly the same 3 files.
- Every previous finding was re-inspected against the new delivery and stands:
  one appended import line in `Grammatik.lean`; accepted evaluators lifted,
  never redefined; ownership exclusions map to real in-tree decoders
  (`decodeSx90/86/87`, `decodeCoreLea`, `decodeLea`, `decodeC`/`decodeCore`/
  `decodeNarrow` arms of `kapDecode`); universal old-first chain agreement;
  `decide`-closed pins and planted refusals; non-degenerate joint `mt_zeuge`;
  honest CUTS with no hardware-correspondence or W/GX claim.

## Assessment of the author repair analysis (gate failure)

- Lane-checkable parts are consistent: the new file's sole namespace is
  `Gabbro.Grammatik.X86` (line 30) with zero occurrences of `GBits`,
  `Gleitkomma`, or `instRepr`; all 16 imports are `Grammatik.X86.*`. Nothing
  in the 3 owned files can define, import, or resurrect a
  `Grammatik.Gleitkomma` module. In my own clone the `GBits` home is likewise
  the Bausteine file (`Bausteine/Gleitkomma/Gleitkomma.lean:40`), matching the
  quoted gate error naming that module as the duplicate home. So the claim
  "no repair within the owned files addresses this" holds: the candidate
  cannot be the source of the duplicate.
- The remaining half of the diagnosis (stale `Gleitkomma.lean` file vs
  poisoned `.lake` olean in the coordinator merge workspace) is outside this
  lane's reach by HARD RULE 1 and is reported here as author-stated, not
  independently verified. It is in no case a candidate defect, and it changes
  nothing about the findings above; the coordinator-side checks the author
  names (`git status`/`git ls-files`, cache replacement) are the right next
  step, owned by the coordinator.
- The author claims no source/binary-chain acceptance in the repair section;
  the candidate still stands exactly as reviewed. No unproved claim is
  approved here.

## Carried-over checks and residuals

- Axioms per evidence remain standard (`[propext]` / `[propext, Quot.sound]`,
  incl. `mt_zeuge`, no `sorryAx`); every premise used; `intro c f _` matches
  the accepted canonical pattern; silicon spot-checks unchanged (ENDBR64,
  INT3, UD2, LEAVE, RET-imm, PUSH/POP widths, TEST sext, forced-REX, AF via
  accepted `andW`).
- Residuals unchanged and still not repair-grade: 90H/86/87 and general
  REX.W/66H LEA unconnected (refusal is the correct call for implicit-LOCK
  XCHG on a no-LOCK machine; disclosed in CUTS); layout rule-36 conflict
  documented for the merge gate; my base newer than the pinned base, so the
  one-line append needs its trivial rebase at merge.

## Build status (honest)

- No new independent green run: `./lean-probe` (>600 s) and `./lean-bau`
  (>3600 s) exceed their timeouts on the cold shared slot, as before. The
  shared evidence now also records author-side timeouts of the same class
  (3600 s bau, 1500 s probe entries), so this is environment-wide, not
  candidate-specific.
- Author evidence: final `./lean-bau` exit 0, 0 error lines,
  `Build completed successfully (709 jobs).`; `./lean-probe` 0 errors; the
  gate's own lean output quoted in the repair section is likewise exit 0
  (718 jobs). The finding below rests on the complete static re-verification
  above plus that evidence; the merge gate rebuilds `grammatik/` locally
  before committing.

## Machine-readable verdict

CANDIDATE: 1351 0a1906c59dfe527aee8d6214bbde2f248f81fe16
VERDICT: ACCEPT

The accepted state carries no unsupported desired-correctness premise, no
weakened guarantee, no fake closure, and no stale snapshot is approved: this
finding binds only the new head above. New definitions/theorems added by this
reviewer: none (report-only review; no Lean changes made, working tree left
clean except this report).
