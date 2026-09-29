# GabbroV bridge -- report (running; `dokumente/AUFTRAG-GABBROV-VERIFIKATION.md`)

**Where it stands (2026-09-29, after S3):** the simulation theorem is PROVED generically for the
Lean parser's whole fragment, and **2 of 146 corpus programs (104, 108) have a CLOSED bridge**:
premise (b) of the goal theorem (`NutzerPflicht`) follows in Lean from GabbroV's own duty proofs
(`./instrumente/zaehle-bruecke.py`). Both are exactly the programs the Lean parser accepts; the
population is bounded by the parser, not by the bridge (S0).

## S0 -- the two projects meet, and the overlap (2026-09-29, measured)

**One project sees both models.** `bruecke/` (new Lake project, MATHLIB-FREE, toolchain
`grammatik`'s v4.33.1) requires `grammatik` by path and compiles `programmlogik/Gabbro/Body.lean`
in place (`srcDir = "../programmlogik"`, root `Gabbro.Body`; nothing copied). The reason no
toolchain unification is needed: `Body.lean` and every generated `Duty/`+`Proofs/` file import
nothing but `Gabbro.Body` (`grep -h '^import' programmlogik/{Proofs,Duty}/*.lean | sort | uniq -c`:
207x `Gabbro.Body`, 4 duty-chain imports; `Gabbro.Sicherheit`, `KompositionBeweis` and `Coverage` are
imported by the root `programmlogik/Gabbro.lean` only, never by a duty or a proof -- and only
`Sicherheit/Ausdruck` and `KompositionBeweis` import Mathlib). `programmlogik/`
stays on its Mathlib pin (v4.33.0); the same SOURCE is compiled under v4.33.1 in `bruecke/`.
Measured: `cd bruecke && LEAN_NUM_THREADS=4 lake build` -> `Build completed successfully (360
jobs)`, `Gabbro.Body` built in 19 s with no error under v4.33.1, and
`#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel` (in `Bruecke/Zusammen.lean`) ->
`[propext, Classical.choice, Quot.sound]`.
What this costs: a person's proofs against `Body` must stay Mathlib-free to be re-checked in
`bruecke/` (no corpus duty or proof imports anything else; `grep -l` above).

**The overlap** (`./instrumente/miss-bruecke-ueberlappung.py --out messung/BRUECKE-UEBERLAPPUNG.md`,
full constructor table there): of 146 `beispiele/*.gab`, **22 export as a G term**
(`gabbro lean-g` exit 0; the other 124 refuse: LG001 74, LG002 31, LG003 3, LG004 11, LG005 5),
and all 146 have a duty file, so the **bridge population is 22 units** -- of which only 6 carry
duty goals (`goals > 0`: 104, 109, 124, 157, 166, 59; list in the table file). The
population is bounded by the G EXPORTER, not by GabbroV. Body is the wider language (options,
`tagged`, tables, `forall`, loops with invariants); G is the typed, elaborated core:
Body ctors used by the corpus but with NO G counterpart of the same shape: `loop`, `locked`
(G: `locks` with a rank proof), `onReason`, `retCall`, `exit`, `exchangeWith`/`awaitLoad`
(G has `exchange`/`awaits`, but the duty exporter refuses them).

**Consequence for the plan.** `zuBody : Programm G -> Body` maps G's typed `Stmt`/`Block` into
untyped `Stmt` with string names; S2's fragment starts at what the 22 units use:
`ret`, `call`, `ite`, `onTag`, `locks`, `assignSlot`/`assignDurch`, `publish`, `bind`.

**The bound is the Lean parser, not GabbroV** (`LEAN_NUM_THREADS=4 python3 instrumente/zaehle-kette.py
--lean`, 13 s): sieve (a) -- `uebersetzeAllg` accepts the source -- passes **2 of 146** programs
(104, 108); 104 fail at elab or parse. The bridge is anchored at the Lean parser as the assignment
demands, so **the bridge population today is exactly those two units**, whatever `lean-g` (22 units)
or `gabbro prove` (146) reach. Widening the population = widening `uebersetzeAllg`'s fragment
(shared with the translation-validation work; every constructor added there is a constructor
`zuBody` must learn) -- or anchoring a second population at the Rust exporter's G terms
(`lean_g.rs`, unverified: that would leave G1 open for the G side; NOT done).

## S1 + S2 -- statements and body computed in Lean (2026-09-29, measured)

`bruecke/Bruecke/Pflichten.lean` computes, from `UProg` (the parser's elaborated output): `zuBody`
(the body as `Body.Stmt`), `preExpr`, `shapeOfU`, `postU` (well-formedness, answer range, every
`ensures` clause with its `old#i`/`result` binders), `calleesOf`, `hyps` (callee contract + frame in
front of the turnstile), `meetsU` (the statement a person proves). Fragment = exactly `UStmt`
(slot writes through a pointer / at a table, direct calls), the trailing `return`, `ensures`
comparisons `== < <=` and `and`/`or`/`not`/`true`/`false`; anything else is `none`/`False`
(never a weaker statement: an unsupported clause makes `meetsU` FALSE, not vacuous).

Per unit (`Instanz104.lean`, `Instanz108.lean`, both anchored at the source text by
`Kette104.uebersetzt4` / `Kette108.uebersetzt8` through a `verankert` theorem): `rfl` between the
Lean computation and every printed definition -- body, `_pre`, `_writes`, `_post`, `_requires`,
`_meets_statement`; the typing of the world (`shapeOf`) by `funext` + case split. Measured:
`cd bruecke && lake build` green (365 jobs).
`gabbro pflichten --lean beispiele/104-referenz.gab | diff - programmlogik/Duty/Duty104Referenz.lean`
and the same for 108: no difference (the check binds what the printer writes now).

**Planted defects** (`./instrumente/mutiere-bruecke.py`, 36 s): 13 printer defects -- dropped
`ensures` conjunct, `<=` printed as `<`, callee precondition widened, call-site precondition
wrong, body constant changed, call to the wrong callee, dropped `Held` requirement, slot range
widened (the `funext` half), result range widened / dropped, frame dropped, callee frame
hypothesis dropped, read index changed -- **13 of 13 caught, in the `Instanz` file** (proofs of
the duty file are stripped to `sorry` first, so the check is shown independent of them; baseline
green). The defects are planted in the printed TEXT, which is what a wrong `lean.rs` produces; a
real `lean.rs` mutation adds nothing but a cargo build.

**The counter** (`./instrumente/zaehle-bruecke.py`, 7 s): `BRIDGE COUNT: 2 of 146 programs have
their duty statements checked ...; 0 of 146 have a CLOSED bridge`. An instance counts only when the
pinned source is the file byte for byte, the printer's duty file is byte-identical to the committed
one, and `lake build` of the instance is green; a closed bridge needs a `BRIDGE-CLOSED` marker
(none yet -- S3).

## S4, the start half (2026-09-29, measured)

`bruecke/Bruecke/Start.lean`: `lowerAllg_requires` (the parser's lowering writes `requires := .wahr`
for every function it accepts -- `progOfFn`) and `startPflicht_wahr` (`S` with every lock invariant
true at `sp0` and `requires = .wahr` give `StartPflicht E`). Instantiated on the chains' units:
`Instanz104.start : StartPflicht Kette104.E4`, `Instanz108.start : StartPflicht Kette108.E8`
(`cd bruecke && lake build`, 366 jobs green). What this is NOT: a duty at an initial memory. It
is the statement that for a unit the parser elaborates, `StartPflicht` is decided by the shape of
the lowering (no user-written `requires`, no lock invariant), which is why the duty files' assumed
`Initially` needs no separate duty for those units. A unit that writes a `requires` on a start or a
lock invariant needs a generated duty at the initial memory; no such unit is inside the parser's
fragment yet, so that duty has no population and is NOT built. The atomic rely
(`NutzerPflichtA`) is not started: it needs S3's semantics first.

## S3 -- the simulation theorem (2026-09-29, measured; Opus session)

**The statement** (`bruecke/Bruecke/Simulation.lean`):

```
theorem bruecke_nutzer
    (hlow : lowerAllg u = .ok (P, fs))          -- the parser's program of the source text
    (S : Stimmig u)                             -- name conditions, decided per unit (`stimmigB`)
    (rk : String → Nat) (hR : Rang u rk)        -- the call graph has a rank (`rangB`, `rangAuto`)
    (hZ : ∀ c, ∃ body, zuBody u (fnAt u c) = some body ∧
                       meetsU u (wfU u) (fnAt u c) body)   -- EVERY GabbroV duty, as computed in Lean
    (E : Einheit (declOf u)) (hP : E.P = P) (hS : E.S = SperrInv.leer _) (hQ : E.Q = axWahr _) :
    NutzerPflicht E
```

with the generic pieces `bruecke_koerperGutR` (every function meets `KoerperGutR` at every
budget), `bruecke_keineLogik` (every `logik` outcome of a body is a callee's answer, so
`KeineLogik`), `bruecke_logik` (`LogikPflicht` with the empty lock family and the trivial axiom
ensures: `koerperGutS_leer`, `invGutS_leer`, no reason exists) and the S4 start half
(`startPflicht_wahr`). `#print axioms` of every theorem: `[propext, Classical.choice, Quot.sound]`;
no `sorry`, `admit`, `native_decide` or new `axiom` (`grep` over `bruecke/Bruecke/*.lean`: none).
`Zielsatz/Spec.lean` is NOT changed; `meetsU` is NOT weakened (it is the S1 definition, checked
`rfl` against the printed duty files). `gabbro_ziel`'s axioms unchanged (`Bruecke/Zusammen.lean`).

**Instances -- the closed bridges** (`Instanz104.lean`, `Instanz108.lean`): `nutzer_bruecke :
NutzerPflicht Kette104.E4` and `... Kette108.E8`, from `einzahlen_meets`/`lies_meets` and
`read_a_meets`/`read_c_meets` -- the proofs GabbroV's gate calls GREEN, in
`programmlogik/Duty/Duty104Referenz.lean` and `Duty108DisjointStartLocks.lean`, compiled in
place. `stimmigB` and `rangB … (rangAuto …)` close by `decide`. The chains with the bridged
premise: `kette_104_bruecke : Kette src104real` and `kette_108_bruecke : Kette src108` (the closed
chains of the closing theorem with `nutzer := nutzer_bruecke` instead of the hand proofs
`nutzer4`/`nutzer8`). Witness of the theorem (rule 13): `I104.bruecke_zeuge` -- all premises
jointly, on a program with a call.

**Measured:**
- `cd bruecke && LEAN_NUM_THREADS=4 lake build` -> `Build completed successfully (194 jobs)`.
- `python3 instrumente/zaehle-bruecke.py` -> `2 of 146 ... statements checked (S1+S2); 2 of 146 have
  a CLOSED bridge (S3)`. A closed bridge now REQUIRES the build output line `'…nutzer_bruecke'
  depends on axioms: [propext, Classical.choice, Quot.sound]` (before this session the counter's
  docstring claimed an axioms check the code did not make).
- `python3 instrumente/mutiere-bruecke.py --s3` -> **5 of 5** planted S3 defects caught by the
  closed-bridge count: a duty proof replaced by `sorry` (`sorryAx` in the axioms line), the
  instance's duty replaced by `sorry`, the `#print axioms` removed (not measured), the marker
  naming an unapplied theorem, and **the ghost counter not bumped** (`Lauf.lean`: the proof no
  longer builds -- the ghost is load-bearing, see F1).
- `python3 instrumente/mutiere-bruecke.py` (S1/S2, re-run after the instance files changed) ->
  13 of 13 caught, baseline green.

**How it is proved** (3 555 lines, `Bruecke/{Kodierung,Ausdruck,Anweisung,Nachbedingung,Lauf,
Realisierung,Simulation,Pruefung}.lean`):
1. *Reading a G state as a Body state* (`Kodierung`): `valOf` (a number is `.int n`, a pointer
   `.absent`), the world relation `WRel` and the binding relation `LRel` go through THE LOOKUPS
   THE LOWERING USES (`tabIdx`, `fieldHit`, `paramPos`), so a duplicate name is read as the
   lowering reads it. Every type transport of the lowering (`rw …; exact`) is handled once by
   `HEq` (`mpr_heq`, `eval_heq`, `execStmt_heq`, `execEnd_heq`).
2. *Expressions* (`Ausdruck`): index, value side, `ensures` side (`old` reads as the numbered
   `old#i` binders, `result`), comparison, `and`/`or`/`not`; one clause (`clause_iff`) and the
   conjunction (`ensList_iff`) -- both directions.
3. *Statements* (`Anweisung`): slot write through a pointer / at a table (the relation survives
   `storeSlot`/`store`, `wrel_store`), the call (arguments, the callee's Body entry state
   `bindAll`, its precondition `preExpr_wahr`), the trailing return (`Nachbedingung.lowEnd_sim`).
4. *The promise* (`post_iff`): over related states the duty file's `postU` IS `EnsAmRueck`.
5. *The run* (`Lauf.lauf`) with an ANSWER TABLE, and *the environment* (`Realisierung.realisiert`,
   `Simulation.tabEnv`): see F1, F2.

**Findings.**
- **F1 -- the lock trace.** G's call handler `R` sees the whole G world, which carries the
  thread's lock TRACE; a Body environment sees only the Body state. So `R` may answer two calls
  of one callee from the same Body state differently, and no single `ρ : Body.Env` reproduces it.
  Closed without weakening anything: for a callee that writes nothing the difference is
  invisible (its frame fixes the world, `.call` drops the value); for a writer each call point
  bumps a GHOST counter `.field w "#"` of the callee's first written carrier `w` -- a place no
  pass, body or promise reads, which the callee may write exactly because it writes `w`
  (`Frame`) -- so the entry states of two calls of a writer differ and the table is a function
  (`Schluessel`). Measured load-bearing (mutation `ghost-counter-not-bumped`). NOT exercised by a
  corpus instance: neither 104 nor 108 calls a writer.
- **F2 -- a cycle in the call graph breaks the bridge, and the rank premise is necessary.**
  `meetsU` assumes the callees' contracts for EVERY entry state (`Contract`), G's `KoerperGutR`
  only at the call actually made. With a cycle, a contract nothing can keep makes the duties true
  by vacuity. Formalized (`Bruecke/GiftZyklus.lean`): `h() ensures false { h(); }`,
  `g() ensures T.slots[0].v == 7 { h(); }`, `f() ensures T.slots[1].v == 5 { g(); }` -- all in the
  parser's fragment: **`alle_pflichten`** (every duty GabbroV states holds) and
  **`nicht_koerperGutR : ¬ KoerperGutR PZ 0 fI`** (a contract-respecting handler answers `g`
  where slot 0 is 7; `f` returns with slot 1 at 0), both on the standard axioms; `rang_faellt`
  (`rangB` refuses it) and `kein_rang` (no rank exists). The theorem therefore takes `Rang` as a
  premise; `realisiert` builds, rank by rank, an environment keeping every contract. This is a
  statement about GabbroV's duties, not about the proof: a GREEN gate on a recursive unit
  without a measure says nothing about premise (b). (GabbroV's own wiring for recursion,
  `contract_of_duty_rec`, needs a `decreases` measure; the parser's fragment has none.)
- **F3 -- the `old#` names stop at nine.** `Pflichten.oldName` names the `old` reads `old#1` …
  `old#9` and gives every later one `old#9`, while `lean.rs` prints `old#10`, … A clause with more
  than nine `old` reads is outside the S1 `rfl` check and outside the bridge (`OldsKurz`, decided).
- **F4 -- the name conditions** the Body reading needs, each decided per unit by `stimmigB`
  (a unit failing one is outside the bridge, never wrongly inside): table names unique
  (`TabEindeutig`: two tables of one name are one Body carrier); parameter names distinct
  (`bindAll` binds the LAST of a name, `paramPos` finds the FIRST); no parameter called `result`
  or `old#…` (the clause binders would shadow it); the elaborator's two parameter lists agree on
  pointer targets (`ArtStimmt`); every declared write names a table (`schreibt`); every clause is
  in the Body fragment (`PostDef`).
- **F5 -- `!=`, `>`, `>=`** are lowered by the parser (to `nicht`/swapped `lt`/`le`) but refused
  by `Pflichten.opOf`: such a unit has no promise in the bridge (`PostDef` fails). Widening is one
  line in `opOf` plus the `lowCmp_sim` case -- but it must follow what `lean.rs` prints (S1).

**Coverage, "widened constructor by constructor as far as it goes".** The theorem covers every
constructor the Lean parser elaborates: `UStmt` 3 of 3 (write through a pointer, write at a
table, direct call), `URet` 2 of 2, `USide` 6 of 6, `UArg` 3 of 3, `UIdx` 2 of 2, `UEns` 6 of 6
with the comparisons `== < <=` (F5). There is no constructor left to widen on the bridge side; the
next widening is the PARSER (`uebersetzeAllg`: `if`, `let`, loops, locks, reasons are not
elaborated), which is shared with the translation-validation work and bounds the population at 2
of 146 (S0). That is the critical path for the bridge count.

**Not claimed.** Nothing about units the parser does not elaborate; nothing about the atomic rely
(`NutzerPflichtA`, S4); the ghost path of F1 is proved generically but has no corpus instance.
Isabelle is not installed on this machine; `abnahme.py --voll` was NOT run. Nothing under
`crates/` changed.
