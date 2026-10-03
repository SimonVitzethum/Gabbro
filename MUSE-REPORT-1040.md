# MUSE-REPORT-1040: Exact review of author 890 (SETcc selection rule)

## CANDIDATE

CANDIDATE: 890 f5a0499e23faa89060418b9be9fb1780303617a4

## VERDICT

VERDICT: ACCEPT (bounded, as cut in the file's own CUTS)

## What was reviewed

- Exact pinned snapshot in `.tmp/review/author-890/`: `PATCH.diff` (3 files:
  `MUSE-REPORT-890.md`, `grammatik/Grammatik.lean` one import line,
  `grammatik/Grammatik/X86/OptSetccSel.lean` new, 401 lines),
  `OWNER-TASK.md`, `MUSE-REPORT-890.md`, `BUILD-EVIDENCE.json`,
  `SNAPSHOT.json` (base `b040b155`, which equals this clone's HEAD).
- The full new Lean file, read in the snapshot copy and cross-checked line by
  line against `PATCH.diff` (identical).
- Every reused canonical name verified present in this tree: `bedingung`
  (`X86/Wort.lean`), `setCCByte`/`setCCAnwenden`/`setLowByte_tief`/
  `setLowByte_hoch`/`witTrue`/`witFalse` (`X86/ControlFlow.lean`),
  `setccSchrittBytes`/`setccSchrittBytes_wert`/`setccSchrittBytes_rahmen`
  (`X86/ControlCodec.lean`), `laengeOk`/`ripNach` (`X86/Ausfuehrung.lean`),
  `refD`/`refEin_schreibt`/`refB_erreicht`/`refB_schreibt`/`keinRuf`/
  `vertragVon` (`ReferenzB.lean`, `Maschine.lean`, `Syntax.lean`),
  `Expr.weiter`/`Endblock.bind`/`Endblock.leave` (`Syntax.lean`),
  `gleitRechne`/`gleitPasst` (`Semantik.lean`).
- DESIGN citations verified in `DIRECT-COMPILER-DESIGN.md`: §3 SETcc row
  (line 313, byte result 0/1 exact, no flag leak), §3A (line 343, measured
  suitable never by default), §4 float row (line 379, UCOMISD + SETcc/Jcc
  with JP row, NaN unordered false), §7 flags-aware peepholes (line 523,
  rule in register, flag-liveness, no token op in pure window). The author's
  note that no SETcc-specific §7 row exists is correct.
- Official local reference: Intel SDM 325462-093US (matches
  `.tmp/HARDWARE-REFERENCES/REFERENCES.json`), SETcc entry Vol. 2B 4-623–4-625
  (`intel-instruction-reference.txt` lines 94202–94331).

## Architecture findings (byte forms, semantics, faults)

1. Byte value exact: `setccByte_wahl`/`setccByte_nat` prove the byte IS the
   0/1 of `bedingung c f` over arbitrary conditions and flag snapshots.
   Matches SDM Operation (`IF condition THEN DEST := 1 ELSE DEST := 0`).
2. Flags unaffected: the window theorem inherits flag/memory preservation
   from the accepted `setccSchrittBytes_rahmen` (proved `rfl` over the
   accepted `setCCAnwenden`), matching SDM "Flags Affected: None". Nothing
   invented; AF (modelled `Option`, never read by `bedingung`) untouched.
3. Memory destination: SDM form is `r/m8` (register OR memory, ModRM:r/m
   write, #GP/#SS/#PF on memory operands, #UD on LOCK). The canonical
   `setccSchrittBytes` models the register destination only; the candidate
   refuses memory destinations at certificate level (`nurRegister`,
   `setccVerweigert_speicher`) and CUTS the memory form to the concurrency
   lane. Sound: refused, never modelled, no fault-freedom speculated.
4. Upper bits / REX: low-byte update with upper bits preserved reuses the
   accepted `setLowByte` lemmas; consistent with fixed 8-bit operand size.
   The REX high-byte-register aliasing (AH vs SPL) is decoder/register
   naming below this rule's level and rightly unclaimed.
5. Complement selection (`setccKomplement_wahl`, `b` vs `!b` with swapped
   constants) matches the SDM alternate-mnemonic structure without claiming
   opcode aliasing. Bounded and correct.
6. Float: `setccGleit_behält` is value-level `gleitPasst` congruence under
   the validator's recomputed kernel equation plus the JP/unordered row
   (`fpBereinigt`), same conditional-equation shape as the accepted
   `foldGleit_behält` in `OptFoldConst.lean`. UCOMISD byte correspondence
   is CUT to the lowering lane. No ordered-compare NaN swap reaches the
   equation (refused in §1). Bounded and disclosed.
7. Source/target connection (`OptSetccSel_verbindung`): complementary
   literal materialisations agree in value and `execEnd` outcome at an
   arbitrary `Endblock.bind` window with arbitrary continuation, and the
   admitted target byte equals that 0/1 via the validator's flag-production
   premise (`hSel` takes `hz`). No lowering correspondence
   (`Stmt.ite` to CMP+SETcc bytes) is claimed; CUTS assigns it to the
   lowering lane. The claimed concurrency/call-log/budget coverage rests on
   the `execEnd` equality over literal bindings (no shared access added,
   same block shape); that reading is stated in the doc comment and stays
   inside the proved equality. No `ensures` derived, no refusal weakened.

## Rule-compliance checks

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the new file
  (regex word-boundary grep over the snapshot: zero hits; "admitted" prose
  substrings only). No `intro _` / `have _ :=` discards; the witness's
  underscore binders are existential components all supplied with concrete
  terms (`true`, all-true cert, `.e`, `witTrue.flags`, `decide`s, `leave`,
  `refSp0.welt []`, `Env.nil`) and every supplied conjunct is used
  (`hV.1`, `hV.2.1`, `hV.2.2`, `refEin_schreibt`, `refB_erreicht`,
  `refB_schreibt`).
- Every premise of every new theorem is used (refusals via `simp` with the
  named hypothesis; value/window lemmas via the cited accepted equations;
  connection via `hSel hz` and the `weiter` range evidence carried in the
  terms). No `Prop`-typed premise. Conclusion is never a premise renamed:
  the float congruence is a genuine (one-step) consequence, same pattern as
  the accepted fold lane.
- Inhabitation: `OptSetccSel_verbindung_zeuge` instantiates ALL premises
  jointly on non-degenerate `refD` (table-writing `refEin_schreibt`) beside
  the reached memory-changing F-run (`refB_erreicht`, `refB_schreibt`,
  slot 0 -> 100). Meets the non-degenerate reached-run bar.
- Axioms: BUILD-EVIDENCE prints connection + witness on exactly
  `[propext, Classical.choice, Quot.sound]` (subsets elsewhere, three probes
  axiom-free); `gabbro_ziel` re-verified standard after integration.
- Scope hygiene: no new diagnostic/gift/example/CLI numbers, no MARKE
  changes, no source/checker/Spec/goal/emitter edits, no friend-reserved
  optimiser files (PATCH file list is exactly the 3 files). CUTS block and
  `#print axioms` for every main theorem present.
- Minor note (not a defect): the identifier `setccGleit_behält` carries an
  umlaut, same as the accepted `foldGleit_behält` precedent; English-only
  prose is otherwise kept.

## Independently executed evidence

- `./lean-probe grammatik/Grammatik/X86/ControlCodec.lean`: 0 errors; the two
  reused lemmas `setccSchrittBytes_wert` / `setccSchrittBytes_rahmen` check
  green on `[propext]` in this tree.
- Candidate build evidence vouched by `BUILD-EVIDENCE.json` (author-clone
  runs): `lean-probe` on the new file 0 errors with the axiom table above,
  `lean-bau` "Build completed successfully (511 jobs)", goal axioms
  standard. I did not re-run the candidate's own build (report-only review;
  source owned by author 890, untouched by this lane).

## Open (as cut, not as objection)

No lowering correspondence, no formal machine-work transfer, no
memory-destination SETcc, no UCOMISD byte correspondence, no new `Befehl`
evaluation, no silicon/ABI/loader claim. All stated in CUTS.

## Task notes

The owner task's "invariant/effect exports" phrasing is imprecise as the
author reports (no such modules; `InvariantenOpt`/`TableLayout`/
`CostSummary` read instead). Nothing else in the task looks wrong; the ZEUGE
names match exactly what was delivered.
