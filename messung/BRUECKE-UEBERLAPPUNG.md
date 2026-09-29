# Bridge overlap (S0) -- `instrumente/miss-bruecke-ueberlappung.py`

corpus units (`beispiele/*.gab`): 146
units with a duty file (Body side): 146
units that export as a G term (`gabbro lean-g` exit 0): 22
**units on BOTH sides (the bridge population): 22**
`lean-g` refusals by code: LG001 74, LG002 31, LG003 3, LG004 11, LG005 5

## Stmt constructors (units using each; textual, shared names over-count)

| ctor | Body units | G units | in Body | in G |
|---|---|---|---|---|
| advances | 0 | 0 |  | yes |
| assign | 42 | 0 | yes |  |
| assignDurch | 0 | 5 |  | yes |
| assignField | 3 | 0 | yes |  |
| assignGlob | 0 | 0 |  | yes |
| assignGlobal | 20 | 0 | yes |  |
| assignSlot | 0 | 5 |  | yes |
| assignVar | 0 | 0 |  | yes |
| awaitLoad | 4 | 0 | yes |  |
| awaits | 0 | 0 |  | yes |
| axiomCall | 0 | 0 |  | yes |
| bind | 0 | 2 |  | yes |
| bindAxiom | 0 | 0 |  | yes |
| bindCall | 14 | 0 | yes | yes |
| bindCallElse | 7 | 0 | yes | yes |
| bindCallInd | 0 | 0 |  | yes |
| bindName | 19 | 0 | yes |  |
| breaking | 2 | 0 | yes | yes |
| call | 28 | 6 | yes | yes |
| callInd | 0 | 0 |  | yes |
| cons | 0 | 15 |  | yes |
| exchange | 0 | 0 |  | yes |
| exchangeWith | 0 | 0 | yes |  |
| exit | 2 | 0 | yes |  |
| forever | 0 | 0 |  | yes |
| gleit | 0 | 0 |  | yes |
| gleitLit | 0 | 0 |  | yes |
| gleitNarrow | 0 | 0 |  | yes |
| gleitVon | 0 | 0 |  | yes |
| ite | 33 | 1 | yes | yes |
| leave | 5 | 0 | yes | yes |
| locked | 25 | 0 | yes |  |
| locks | 0 | 6 |  | yes |
| loop | 14 | 0 | yes |  |
| narrow | 0 | 0 |  | yes |
| next | 0 | 0 |  | yes |
| nil | 0 | 22 |  | yes |
| onGrund | 0 | 0 |  | yes |
| onOption | 4 | 0 | yes | yes |
| onReason | 3 | 0 | yes |  |
| onTag | 8 | 3 | yes | yes |
| pruefung | 0 | 0 |  | yes |
| publish | 9 | 2 | yes | yes |
| regLies | 0 | 0 |  | yes |
| regLiesElse | 0 | 0 |  | yes |
| regSchreib | 0 | 0 |  | yes |
| ret | 76 | 22 | yes | yes |
| retCall | 9 | 0 | yes |  |
| retGrund | 0 | 0 |  | yes |
| retires | 0 | 0 |  | yes |
| retry | 0 | 0 |  | yes |
| schreibBytes | 0 | 0 |  | yes |
| transition | 0 | 0 |  | yes |
| traverse | 0 | 0 |  | yes |
| uebergang | 0 | 0 |  | yes |

## Expr constructors (units using each; textual, shared names over-count)

| ctor | Body units | G units | in Body | in G |
|---|---|---|---|---|
| add | 0 | 2 |  | yes |
| altGlob | 0 | 0 |  | yes |
| altSlot | 0 | 0 |  | yes |
| band | 0 | 0 |  | yes |
| bin | 89 | 0 | yes |  |
| bor | 0 | 1 |  | yes |
| bxor | 0 | 1 |  | yes |
| chainFrom | 1 | 0 | yes |  |
| div | 0 | 0 |  | yes |
| durch | 0 | 0 |  | yes |
| eq | 0 | 4 |  | yes |
| existsSlots | 0 | 0 | yes | yes |
| fall | 0 | 1 |  | yes |
| falsch | 0 | 0 |  | yes |
| fieldOf | 6 | 0 | yes |  |
| flle | 0 | 0 |  | yes |
| fllt | 0 | 0 |  | yes |
| fnref | 0 | 0 |  | yes |
| forallSlots | 10 | 0 | yes | yes |
| glob | 0 | 0 |  | yes |
| global | 37 | 0 | yes |  |
| grund | 0 | 0 |  | yes |
| hasShape | 102 | 0 | yes |  |
| istSome | 0 | 0 |  | yes |
| le | 0 | 2 |  | yes |
| leseBytes | 0 | 0 |  | yes |
| lit | 119 | 16 | yes | yes |
| lt | 0 | 0 |  | yes |
| mul | 0 | 0 |  | yes |
| name | 99 | 0 | yes |  |
| neg | 0 | 0 |  | yes |
| nicht | 0 | 0 |  | yes |
| none | 0 | 0 |  | yes |
| oder | 0 | 0 |  | yes |
| place | 43 | 0 | yes |  |
| ptrOf | 0 | 1 |  | yes |
| reaches | 2 | 0 | yes | yes |
| rem | 0 | 0 |  | yes |
| sdiv | 0 | 0 |  | yes |
| shl | 0 | 0 |  | yes |
| shr | 0 | 0 |  | yes |
| slot | 0 | 0 |  | yes |
| some | 0 | 0 |  | yes |
| someOf | 9 | 0 | yes |  |
| srem | 0 | 0 |  | yes |
| sub | 0 | 1 |  | yes |
| tagOf | 1 | 0 | yes |  |
| un | 9 | 0 | yes |  |
| und | 0 | 2 |  | yes |
| var | 0 | 19 |  | yes |
| wahr | 0 | 22 |  | yes |
| weiter | 0 | 16 |  | yes |
| wrapTo | 4 | 0 | yes |  |

## The bridge population

- beispiele/104-referenz.gab (duty goals 3, refused 0)
- beispiele/108-disjoint-start-locks.gab (duty goals 0, refused 0)
- beispiele/109-lockfree-entry-roots.gab (duty goals 2, refused 0)
- beispiele/116-payload-free-counter.gab (duty goals 0, refused 0)
- beispiele/118-sperrinvariante-erhaltung.gab (duty goals 0, refused 1)
- beispiele/119-sperrinvariante-bloecke.gab (duty goals 0, refused 1)
- beispiele/120-tagged-construction.gab (duty goals 0, refused 0)
- beispiele/121-tagged-static-init.gab (duty goals 0, refused 0)
- beispiele/124-two-threads-private.gab (duty goals 8, refused 1)
- beispiele/130-derived-contract-pure.gab (duty goals 0, refused 0)
- beispiele/15-own-traegt-beide-rechte.gab (duty goals 0, refused 0)
- beispiele/157-worker-pool.gab (duty goals 3, refused 1)
- beispiele/16-by-ops-am-feld.gab (duty goals 0, refused 0)
- beispiele/162-geteilte-flagge.gab (duty goals 0, refused 0)
- beispiele/165-gp-eintritt.gab (duty goals 0, refused 0)
- beispiele/166-eintritt-irq-maskiert.gab (duty goals 1, refused 0)
- beispiele/34-markierter-wert.gab (duty goals 0, refused 0)
- beispiele/59-eintritt-nimmt-maskierte-sperre.gab (duty goals 2, refused 0)
- beispiele/62-grenzwort-im-ausdruck.gab (duty goals 0, refused 0)
- beispiele/69-integer-conversion.gab (duty goals 0, refused 0)
- beispiele/73-sugar-widths.gab (duty goals 0, refused 0)
- beispiele/93-const-scalars.gab (duty goals 0, refused 0)
