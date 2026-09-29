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
