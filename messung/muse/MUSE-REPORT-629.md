# MUSE-REPORT-629: Independent review of lane 628 (SourceAssignmentLowering)

CANDIDATE: 628 eb3a81c477f63a1de3b9e6d935c67feef6155090
VERDICT: ACCEPT

## Scope and method

Reviewed the exact pinned candidate from `.tmp/review/author-628/`:
`SNAPSHOT.json` (head `eb3a81c4…`, base `eb68896b`, files
`MUSE-REPORT-628.md`, `grammatik/Grammatik.lean`,
`grammatik/Grammatik/X86/SourceAssignmentLowering.lean`, clean true),
`OWNER-TASK.md`, `PATCH.diff`, the full new module (645 lines), and
`BUILD-EVIDENCE.json`. No source/Spec/checker/emitter/optimiser edits;
no other clone read; no tree edits made (this lane owns only this report).
Verified real producer/consumer interfaces in this clone
(`SourceMemory.lean`, `ExpressionLowering.lean`, `Byteschritt.lean`,
`Ausfuehrung.lean`, `Syntax.lean`) by grep, and the candidate text by
exact-token grep. Did not re-apply the patch (prohibited); build trust
rests on the candidate's own queued-wrapper evidence chain below, which
is coherent (red intermediates repaired before the final green commit).

## What the candidate delivers

New module `grammatik/Grammatik/X86/SourceAssignmentLowering.lean` plus
one additive umbrella import. Definitions: `senkAssign` (599 `senkFrag`
fragment code ++ one `store64 base dst disp`; `none` = explicit
unsupported-expression refusal). Theorems: `intWort_zahlWort` (value
bridge), `senkAssign_ok` (shape), `evalTrans`/`paarCancel` (transport
helpers, fully variable type sides so `cases` applies),
`senkAssign_korrekt` (main statement-level correspondence),
`senkAssign_verweigert_mul`/`senkAssign_verweigert_tief`
(unsupported expression/nesting), `assignRepOk_negativ_verweigert`
(negative range), `assignCodeAlias_verweigert` (code-alias region),
`witByteFaelschung628` (forged-opcode fetched refusal, `byteschritt =
none` by `decide`), `witRegionGetrennt628` (code/data separation
positive), witness vocabulary `witD628`/`witV628`/`witO628`/`witR628`/
`witCtx628`/`witI628`/`witE628`/`witEnv628`/`witSigma628`/`witSL628`/
`witAbb628`/`witReg628`/`witProg628`/`witBytes628`/`witMem628`/
`witStart628`/`witA628`/`witM628'` plus premise facts, fetched-byte
`decide` witnesses `witBytesWert628` (`rax = 42` after 4 fetched steps),
`witBytesSpeicher628` (data cell `0 -> 42`), `witLaufAendert628`
(memory-changing run), and joint witness `senkAssign_korrekt_zeuge`.

## Checks performed

- **Real semantics, no invented IR/executor.** Main theorem consumes one
  existing typed source semantics (`execStmt`/`eval` from
  `Grammatik.Semantik`, statement `Stmt.assignSlot` with real `hw`/`hL`)
  and the canonical target executors (`lauf` over `Decodiert` with
  `(encode b).length` from `Ausfuehrung`/`Codec`; fetched-byte
  `laufBytes`/`byteschritt`/`ausgangReg`/`ausgangByte`/`ausgangRip` from
  `Byteschritt`, all confirmed present in-tree). No new interpreter, no
  persistent SSA IR, no friend-reserved optimiser import. Target
  sequence is generated from the admitted statement (`hsenk :
  senkFrag abb e dst tmp = some prog`, then `prog ++ [store64]`),
  encoded and executed — not a hand-picked equal register state.
- **Producer interfaces match.** `senkung_korrekt` (599) takes
  `e : Expr D Γ Λ (.int lo hi)` and yields register `intWort` of the
  actual evaluation plus preserved memory — the candidate passes its
  `e` there and uses the postulates exactly as stated. `rep_schritt_bleibt`
  (570) takes the statement-level `e : Expr D Γ Λ (D.typ t f)` with
  `hv : cast … = v` — the candidate supplies the cast expression and
  derives `hv` from `heval` via `evalTrans`/`paarCancel`, mirroring 570's
  own `hk`/`hv` naming pattern. `repOk_klingt`, `schritt_store64_erfolg`,
  `lauf_anhang`/`lauf_einzeln_gleich`, `effAddr_null`, `laengeOk_encode`
  uses are consistent with in-tree signatures.
- **No desired-correctness premise.** `heval : (eval σL e σL ρ).n = v.n`
  names the evaluated source value (same role as 570's `hk`/`hv`); the
  register/memory correspondence is derived through `senkung_korrekt` +
  `intWort_zahlWort` bridge, and `hTgt`/`hRd` are the same target-write
  shape 570 itself takes. No `Prop`-typed premise, no Bool-disguised
  correctness claim beyond the accepted `repOk` admission.
- **Every premise used.** `hOk` (via `hOkI`/`repOk_klingt`), `hLese`,
  `hk`, `heval`, `hFr`, `hrsp`, `hBasis`, `hBaseR`, `hdisp`, `ha`,
  `hTgt`, `hRd`, `hsenk`, `hrenv`, `hExec` all occur in the proof body.
  `evalTrans`/`paarCancel` use all their premises (`cases g` + applied
  arguments).
- **No conflation.** `intWort_zahlWort` uses both bounds (`hLo`, `hHi`)
  for the modulo identity; negative ranges are refused by `decide`
  (`assignRepOk_negativ_verweigert`); no FP/signed/fault claim; no
  atomicity claim (word `write64`/`read64` plus byte-level
  `writeBytesN_hit` inequality, no TSO/concurrency/validator/hardware
  claim). `disp` is pinned to 0 by an explicit `hdisp` premise with
  non-zero displacements in CUTS — a scoping restriction, honestly cut,
  not a hidden assumption.
- **Joint non-degenerate witness.** `senkAssign_korrekt_zeuge`
  instantiates every premise jointly on `witD628` (one table; function
  writes it via `schreibt`), with source slot `12 -> 42`
  (`hBefore`/`hAfter`), mapped target bytes changing (`hBytes` via
  `writeBytesN_hit`), and a fetched run that observably changes memory
  (`witLaufAendert628`). Both source and bytes change memory — not an
  empty/table-less run.
- **Planted refusals real.** `mul`/`tief` rewrite through the actual
  producer refusals `senkFrag_verweigert_mul`/`_tief` (confirmed present
  in `ExpressionLowering.lean`); range/alias refusals are
  `decide`-closed `repOk = false` / `regionDisjunkt = false`;
  forged-opcode refusal is `byteschritt = none` by `decide`. Positive
  separation (`witRegionGetrennt628 = true`) included.
- **Hygiene.** Exact-token grep of the candidate file: no `sorry`,
  `admit`, `axiom` declaration, `native_decide`, `unsafe`, `intro _`,
  or `have _ :=`. File ends with a `CUTS:` block and `#print axioms`
  for every main theorem. English only. Patch touches exactly the three
  owned files (report, new module, one additive import line); snapshot
  reports clean.
- **Build evidence coherent.** `BUILD-EVIDENCE.json` shows a red path
  (7-error draft, one intermediate with `sorryAx` in the main theorem's
  axiom set) repaired stepwise to final `== 0 error(s)` on
  `lean-probe` with standard axioms
  (`senkAssign_korrekt`, `senkAssign_korrekt_zeuge` on
  `propext, Classical.choice, Quot.sound`; shape/refusal lemmas on
  subsets) and `./lean-bau` `Build completed successfully (449 jobs)`.
  The intermediate `sorry` was removed before the final commit — the
  final file verified above contains none.

## Known limitation (accepted as bounded, honestly cut)

The generic correspondence is over `lauf` (decoded instructions with
canonical encoded lengths); fetched-byte (`laufBytes`) agreement for an
ARBITRARY generated sequence is OPEN and stated as such in CUTS, with
single steps covered by accepted `kanonisch_schritt_ueberein` and the
concrete generated bytes covered by `decide` witnesses. This is a real
bounded gap, not a silent one, and the candidate still delivers a new
consumed connection (599 expression run + store composition + 570
source step with `RepSlot` read-back), not a restatement of one
producer theorem. Pilot integer fragment only; sums/FP/locks/calls/
loops/globals/pointers/non-zero displacements explicitly outside.

## Result

`./lean-bau` result line: not re-run by this lane (report-only review;
no tree edits, so no build state of mine to report — candidate's own
final evidence is `./lean-bau`: `Build completed successfully
(449 jobs)` with `lean-probe` `== 0 error(s)`).

No task defect found. Nothing left open for this review.
