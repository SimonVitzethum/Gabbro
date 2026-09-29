# GabbroV bridge -- report (running; `dokumente/AUFTRAG-GABBROV-VERIFIKATION.md`)

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
