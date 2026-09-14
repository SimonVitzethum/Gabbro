# MUSE-REPORT-171 (lane 171, T3 part 6: generic lowering, SECOND HALF)

## What was built

New file `grammatik/Grammatik/Parser/UebersetzeAllg2.lean` (~1180 lines),
registered in `grammatik/Grammatik.lean` next to lane 162's
`Parser.UebersetzeAllg`. It finishes the generic lowering: statement
lowering, `lowerAllg`, the 104 pins, the real-text lex pin, the chaining
theorem, and 108 end to end.

New definitions (namespace `Gabbro.Grammatik.Parser.UebersetzeAllg2`):

- Context: `ctxOf`/`resOf`/`verOf` (body context, held resources,
  contract of a function index).
- Bridges: `sigSchreibt_eq`, `vSchreibt_eq`, `sigKonsumiert_nil`,
  `sigProduziert_nil`, `sigBoden_none`, `vBoden_none`,
  `sigGruende_zero`, `vErg_eq`, `nach_eq`, `ctxParams_eq`,
  `anfangRes_eq`, `endeRes_eq`, `ensCtx_eq`.
- Lowering: `lowWertAt`, `assignDurchStmt`, `assignSlotStmt`,
  `lowAssignDurch`, `lowAssignTab`, `uIdxOfSide`, `lowCallArgOne`,
  `lowCallArgsAux`, `rufHk_ok`, `rufHb_ok`, `heldLocksD`,
  `castNachStmt`, `lowCall`, `lowStmt`, `endPerm_ok`, `lowEnd`,
  `lowBody`, `EnsTy`, `RumpTy`, `lowerFnAt`, `lowerEach`,
  `lowerAtPair`, `progOfFn`,
  `lowerAllg : (u : UProg) -> Except String
  (Programm (declOf u) x List (declOf u).Fn)`.
- 108 preprocessing: `u32Voll`, `normTypU32`, `normFeldU32`,
  `normTabTeilU32`, `normSigU32`, `stripTopNeben`, `normU32Item`,
  `normTopU32`, `pre108`.
- Literals and pins: `src104real`, `lex104real`, `lowerAllg104fragment`,
  `lowerAllg104fuss`, `lowerAllg104data`, `kette104`, `src108`,
  `toks108`, `lex108`, `items108`, `parse108`, `uExp108`, `elab108`,
  `lowerAllg108fragment`, `lowerAllg108fuss`, `lowerAllg108data`,
  `kette108`.

New theorems: the bridges, `heldLocksD_mem`, `endPerm_ok`,
`lowerEach_all_ok`, and all pins above. No `sorry`/`admit`/`axiom`/
`native_decide`; `#print axioms` at the file end, heaviest footprint
`[propext, Classical.choice, Quot.sound]`, same as the rest of the tree.
Every theorem premise is used.

`RufPasst` assembly is harvest-shaped per the task: `hw` over the
write flags, `hh` over the callee held list, `hx` over the listed
held locks (vacuous past the exact held set, every floor is `none`),
`hb` from the `none` floors, `hg` by cases on `Empty`, `hk` from the
empty consume list, `hr` from `gruende = 0`. Guard proofs use the
unfolded `forall w ∈ D.braucht t, ...` form. `hh` is the new SUBSET
condition, `hx`/`hb` the floor fields against default `none`.

## What was measured

- `lowerAllg uExp104` fragment and footprint hold `by decide`
  (default budget), data agrees with `G104_referenz.gD` `by decide`
  (counts, ranges, ranks, guards, held sets, writes).
- `lex src104real = .ok tt104` holds at `maxHeartbeats 12000000`
  (plus `maxRecDepth 100000`, as in `Uebersetze.lean`); the string
  is the `beispiele/104-referenz.gab` bytes verbatim (script-quoted,
  no `"`/`\`/non-ASCII in the file).
- `kette104` chains lex, `parseTopTief`, `elabU`, `lowerAllg` and both
  checks in one theorem, reusing `u104parse`/`u104elab`.
- 108: `toks108`/`items108`/`uExp108` are probe-generated literals
  (`#eval` + `Repr`, then pinned). `lex108` at 12000000 heartbeats;
  `parse108`, fragment, footprint, data and `kette108` at default;
  `elab108` at 12000000 (budget used; minimum not measured).
  Fragment, footprint and data agree with `G108_disjoint_start_locks`
  (`export108_data` side untouched).

## Bugs and findings (measured, not guessed)

1. Lane 162's ensures lowering is off by one when a result is
   present: `lowDurch`/`lowTabRead`/`lowAltRead`/`lowParamSide`/`lowIdx`
   used parameter positions in the result-first `ErgCtx`, so
   `lowerAllg` failed on `lies`. Fixed in `UebersetzeAllg.lean` with
   a `sh` shift (`0` in bodies, `1` in `ensures` with a result);
   bodies are unchanged. This is a bugfix to the merged first half,
   not a fork: the alternative duplicates ~150 lines.
2. `Ty.index` is an abbrev (`.int 0 (n-1)`), never a pattern. The
   index-argument arm matches `.int lo hi` plus harvested
   equalities instead.
3. `RufPasst` is a `Prop` and cannot ride `Except`; the call
   harvests inside `lowCall` and the floor/consume parts live as
   standalone theorems (`rufHk_ok`, `rufHb_ok`).
4. Decidability across the `Fin`/carrier line does not synthesize:
   `L ∈ S.haelt` with `L : Fin _` has no instance (probed); the
   harvests quantify at `D.Lock` (`heldLocksD`), and list literals
   compared against carrier lists need an explicit
   `List (declOf u).Lock` ascription (probed).
5. Nested-subterm recursion (recurse into a module body inside the
   same `match`) compiles but is kernel-opaque: even a 15-item
   `decide` gets stuck at any heartbeat budget (probed down to a
   one-item case). `pre108` therefore follows `elabU`'s own
   one-level `uMembers` unwrap with single-recursion passes only;
   no generality is lost (`uRestFehler` refuses deeper nesting
   loudly anyway).
6. Struct-literal parsing rules, all hit and worked around:
   single-line literals, no trailing comma at end of line, and no
   multi-element list spanning lines inside a struct field (a
   two-record list as a field value misparses; as a def body it is
   fine). `uExp108` is single-line for this reason.

## Build state

`./lean-bau`: `Build completed successfully (175 jobs).`
No Rust touched. No codes, gifts or examples used. Probe scratch
lives uncommitted under `.tmp/` (ignored).

Commits on `muse/171`: `bdeebd4f` (1: lowering + `lowerAllg`),
`0cb64e13` (2: shift fix + 104 pins), `e36fb572` (3: lex pin),
`a3f0ff96` (4: `kette104` + CUTS), `6eec9bb7` (5: 108).

## Open (CUTS in the file)

- `beq` soundness for nothing new; stage pins reused from lane 160.
- `RufPasst` harvest is exactness in disguise (`hh` + `hx` with
  `none` floors); floor-bearing declarations would need computed
  rank checks.
- `elab108`'s 12M budget is used, not minimised.

(End of file.)
