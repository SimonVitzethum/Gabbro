# MUSE-REPORT-162 (lane 162, T3 part 5: generic lowering, PARTIAL)

## What was built

New file `grammatik/Grammatik/Parser/UebersetzeAllg.lean` (~650 lines),
registered in `grammatik/Grammatik.lean` as `Grammatik.Parser.UebersetzeAllg`.
It is the first half of the task: the declaration built from the `UProg`
itself instead of the 104 universe, plus the generic lowering of indices,
sides and `ensures`. Statement lowering, `lowerAllg` and all pins are NOT
in this report's tree; they remain open (see below).

New definitions (namespace `Gabbro.Grammatik.Parser.UebersetzeAllg`):

- Data lookup: `tabAt`, `lockAt`, `fnAt` (by `Fin` index), `fieldCount`,
  `tabIdx`, `lockIdx`, `fnIdx` (structural name-to-`Fin`), `fieldPos`,
  `fieldAtPos`, `fieldRangeO`, `typAt`, `needsAt` (guards), `heldAt`,
  `writesAt`, `mkSig`, `dummySig`, `sigAt`.
- Declaration: `declOf : UProg -> Deklaration` with `Tab := Fin
  tabs.length`, `Lock := Fin locks.length`, `Feld := fun t => Fin
  (fieldCount u t)`, `Fn := Fin fns.length`, `Glob/Marke/Inv/Ax/Reg :=
  Empty`, `Annahme := Unit`.
- Lowering: `FieldHit`, `fieldHit`, `lowVar`, `paramPos`, `lowIdx`,
  `LowSide`, `lowBasisTab`, `lowParamSide`, `durchTerm`, `slotTerm`,
  `altTerm`, `lowDurch`, `lowTabRead`, `lowAltRead`, `lowSideVal`,
  `lowSideEns`, `lowCmp`, `lowEns`, `lowEnsList`.

New theorems (all proved, no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` at the file end; heaviest footprint is
`[propext, Classical.choice, Quot.sound]`, same as the rest of the tree):

- `notEmpty_ne_nil`, `sigAt_get`, `sigAt_params`, `sigAt_erg`,
  `sigAt_haelt`, `sigAt_konsumiert`, `sigAt_produziert`, `params_eq`,
  `erg_eq`, `haelt_eq`, `ende_eq`, `rangeO_some`, `typAt_of`,
  `tabNr_some`, `fieldPos_lt`, `fieldAtPos_get`.
- None of them has a premise universally quantified over program syntax
  (`Vertrag`/`Stmt`/`Endblock`/`ErgExpr`/`Expr`/`Args`), so rule 13
  requires no `_zeuge` companions. Every theorem premise is used.

## What was measured (probes, not committed)

- Lexer on the REAL `beispiele/104-referenz.gab` text (with `--`
  comments): `lex src104real = .ok tt104` (`tt104` is lane 160's
  comment-free token literal) holds at `maxHeartbeats 12000000`.
  No lexer change was needed; comment handling (`ueberKommentar` in
  `Lexer.lean`) already covers the real file. The pin itself is not
  committed (the pipeline stage that consumes it, `lowerAllg`, is open).
- Decidability probes (scratch, under `.tmp/`, not committed):
  bounded `forall`-over-list, `List.Perm`, and `forall` over `Fin`
  all have instances, so guard/held-set/perm obligations can be
  harvested with `if h : ... then ... else .error`. `Decidable
  (darf D t L)` does NOT synthesize (stuck projection); the unfolded
  `forall w ∈ D.braucht t, ...` form does.

## What remains open (CUTS)

1. Statement lowering (`UStmt.assign`/`assignTab`/`call` to
   `Stmt.assignDurch`/`assignSlot`/`Stmt.call`), call arguments
   (`var`/`freshPtr`/`wert`), `RufPasst` assembly (fields `hw`/`hh`
   by harvest, `hg` by `nomatch` on `Empty`, `hk` from
   `sigAt_konsumiert`), bodies/`Endblock`s, program assembly, and
   `lowerAllg : (u : UProg) -> Except String
   (Programm (declOf u) x List (declOf u).Fn)`.
2. The 104/108 `programmImFragmentG`/`fussOrtGB` pins by `decide`,
   the data agreement against `G104_referenz.gD`/`r4D` and
   `G108_disjoint_start_locks.gD`, the real-text lex pin, and the
   chaining theorem (`lex -> parseTopTief -> elabU -> lowerAllg ->
   checks` for 104).
3. Nothing in the task looks wrong. Two warnings for the lane that
   continues: (a) 108 needs preprocessing before `elabU` -- its
   `concurrent { read_a, read_c }` item (`.nebenT`) is refused by
   `uRestFehler`, and its bare `u32` field/result types are refused
   by `uFeldTyp`/`uErgBereich` (lane 160 deliberately has no
   full-range rule; the exporter maps bare `u32` to
   `.int 0 4294967295` per `Export108.lean` CUTS); strip/normalize in
   the new file, never by editing `Uebersetze.lean`. (b) Elaboration
   rules learned the hard way, also in the file's CUTS block: pin `D`
   explicitly on every constructor over the Fin carriers
   (`Expr.slot (D := declOf u)`), keep struct literals single-line,
   never start a term continuation line with `(`.

## Build state

Last `./lean-bau` result line: `Build completed successfully (149 jobs).`
No Rust touched (`./cargo-pruef` not applicable). No codes, gifts or
examples used. Files touched: only the new
`grammatik/Grammatik/Parser/UebersetzeAllg.lean` plus the one import
line in `grammatik/Grammatik.lean`.

Commits on `muse/162`: `c6c4deba` (declaration + bridges),
`47d0f7f8` (sides/ensures lowering), `8d811802` (import + CUTS).
