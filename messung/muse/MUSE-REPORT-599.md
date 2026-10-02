# MUSE-REPORT-599: Direct typed-source expression to pilot machine code

Lane 599, clone `/home/simon/Dokumente/gabbro-muse/a599`, branch `muse/599`.
Owned files only: `grammatik/Grammatik/X86/ExpressionLowering.lean` (new, 1208
lines), `grammatik/Grammatik.lean` (one import line appended),
`MUSE-REPORT-599.md` (this file).

## What was done

Generic direct lowering of the actual typed source AST to canonical pilot
`Befehl` lists, with no second SSA IR and no new source interpreter. Reused:
`Syntax.Expr`/`Var`/`Ty`/`Zahl`, `Semantik.eval`/`Env`/`World` (the single
source model), `Codec.encode`, `Ausfuehrung.schritt`/`lauf` plus its step and
frame lemmas, `Byteschritt` fetch/`laufBytes`/memory layout vocabulary,
`FlagBeweis.sint`/`add64_of_iff`/`sub64_of_iff`, `ScalarFloat.intWort`.

Covered fragment: integer literals, integer variables, and exactly one
bounded ADD/SUB level over atomic operands. Everything else refuses with
`none` (two planted lowering refusals, one planted fetched-byte refusal).

Definitions: `EnvRepr` (every int variable reads the modular word of its
actual source value in the pre-state register file), `Frisch` (no source
variable in the two working registers; the two differ), `senkAtom`,
`senkFrag`, `IstAtom`, `IstFrag` (shape-only relations whose inversion
substitutes, so stuck carrier projections never appear as proof
obligations), `lauf_einzeln_gleich`, `lauf_anhang`, `laengeOk_encode`.

Theorems: `senkFrag_lit/var/add/sub` (shapes), `senkFrag_verweigert_mul`
(mul refuses), `senkFrag_verweigert_tief` (nested add refuses),
`intWort_add/sub` (modular homomorphism), `intWort_sint` (signed-64
roundtrip), `senkAtom_korrekt_lit/var`, `istAtom_von_senkAtom`,
`senkAtom_korrekt`, `senkung_add/sub` (value = `intWort` of the exact source
value; memory untouched; foreign registers and `rsp` kept; architectural
add/sub flags), `istFrag_von_senkFrag`, `senkung_korrekt` (generic dispatch:
value, memory, registers, `rsp`), `senkung_ohne_ueberlauf_add/sub`
(in-range operand/result ranges give exact signed reading and clear
overflow flag).

Witness package: `ZeugeD` (one int table written by its single function),
`ZeugeCtx/AtomA/AtomB/Ausdruck` (`x + 12` at `12 .. 112`),
`ZeugeUmgebung` (`x = 30`), `ZeugeWelt`, `ZeugeAbb` (`r10`), `ZeugeReg`,
`ZeugeProg/Bytes/Speicher/Start` (lowered bytes at executable 4096, data
cell at 8192). `zeuge_auswertung` (`30 + 12 = 42`, `rfl`), `zeuge_senkung`
(low
...[truncated 3074 chars]
