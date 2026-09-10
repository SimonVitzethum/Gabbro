# SYNTAX parser-mapping draft — production to constructor (open item 16.2-8)

*Design only, 2026-09-10, lane-96. This file is the DRAFT for the parser
item of SYNTAX.md section 16.2 item 8 (the map from the token grammar to
the tree, PLAN-GRAMMATIK.md section 4); it does NOT edit SYNTAX.md.
Sources read, read-only: the EBNF sections of dokumente/SYNTAX.md (161
defined rules, counted with the guardian expression) and the constructors
of grammatik/Grammatik/Syntax.lean. No Rust code changes and no parser
verification happen in this lane.*

## How to read the table

Each row maps one EBNF production (name quoted inline) to its Lean
carrier plus the attribute side the parser must attach or check. Kind is
one of three: core (the parser builds the term directly), SUGAR (the
parser emits the desugared definition, so there is nothing to translate),
LESESTELLE (surface syntax with no constructor; the gap name points to
the list below). Bold type never carries a count in this file; every
number stands plain.

The parser this draft specifies turns a derivation of the surface grammar
into a term of Syntax.lean. Everything the grammar calls an attribute —
the range at a number, the bound at an index, the held witness at a
guarded place, the write right at an assignment, the consumed mark at a
call, the stage at a phase mark, the class at a register access, the
pairing at a publication — arrives as a constructor argument, so the
parser must either check it (core) or produce the definition that carries
it (SUGAR). Where there is no constructor, the row says so and names the
gap instead of inventing a mapping.

## Lexis — tokens and names (18 productions)

| production | Lean carrier | attribute side | kind |
|---|---|---|---|
| `ident` | none as a term; feeds Var indices and declaration names | position of the binder or declaration | LESESTELLE G-LEX |
| `letter` | none | character class of the lexer | LESESTELLE G-LEX |
| `digit` | none | character class of the lexer | LESESTELLE G-LEX |
| `hexdigit` | none | character class of the lexer | LESESTELLE G-LEX |
| `int` | none as a term; literal value feeds Expr.lit bounds | value becomes both bounds n..n | LESESTELLE G-LEX |
| `dec` | none | decimal spelling, one spelling only | LESESTELLE G-LEX |
| `hex` | none | hexadecimal spelling | LESESTELLE G-LEX |
| `bin` | none | binary spelling | LESESTELLE G-LEX |
| `float` | none as a term; feeds Ty.fl bounds and gleitLit | exactness decides whether rounded is owed | LESESTELLE G-LEX |
| `string` | none | content of claim, reason, assume, section, asm strings | LESESTELLE G-LEX |
| `char` | none | character class of the lexer | LESESTELLE G-LEX |
| `quote` | none | delimiter of the lexer | LESESTELLE G-LEX |
| `newline` | none | end of line and of comment | LESESTELLE G-LEX |
| `comment` | none | discarded before parsing | LESESTELLE G-LEX |
| `path` | none as a term; qualified name argument of declarations, calls, fnref | resolves to a declared Fn, Tab, or generated op | LESESTELLE G-NAME |
| `pathseg` | none as a term; segment of path | word or opname segment | LESESTELLE G-NAME |
| `identlist` | none as a term; name list argument | maintains, preserves, clobbers, measures lists | LESESTELLE G-NAME |
| `regbind` | none as a term; register binding pair | regs in and regs out of entry and entrust | LESESTELLE G-NAME |

## Section 1 — program, modules, constants (14 productions)

| production | Lean carrier | attribute side | kind |
|---|---|---|---|
| `program` | Programm over Deklaration (requires, ensures, rumpf per Fn) | world fixed before the first body | core |
| `item` | dispatch to the declaration forms | one row per declaration | core |
| `buildgate` | none | filter on the item list; theorem about items present | LESESTELLE G-FILTER |
| `bootdecl` | D.Ax | foreign body with dispatch contract | core |
| `bootstep` | D.Ax content | call arguments or name-literal binding | core |
| `entrydecl` | D.Ax | regs in, regs out, preserves, clobbers, dispatch | core |
| `entrustdecl` | D.Ax | entry contract with compulsory falsifiable assume | core |
| `entryextra` | D.Ax attributes | stack, per-cpu, ist, nested bound | core |
| `accdecl` | D.Glob plus Stmt.assignGlob | generated merge assignment | SUGAR |
| `moduledecl` | Deklaration namespace | static names, no run-time content | core |
| `usedecl` | Deklaration namespace | static names | core |
| `constdecl` | Expr.lit | literal at every use | SUGAR |
| `constexpr` | Expr | translation-time evaluable; no effectful call, no mut place | core |
| `staticdecl` | D.Glob, D.gtyp, D.gbraucht | guards, shared flag, section string | core |

## Section 2 — types (23 productions)

| production | Lean carrier | attribute side | kind |
|---|---|---|---|
| `typedecl` | Ty, D.Marke with D.stufen, D.Tab for compounds | linearity, ghost, tagged, order stages | core |
| `markorder` | D.stufen | stage count of the mark | core |
| `typeexpr` | Ty dispatch | selects the value family | core |
| `indexty` | Ty.index, Ty.opt | count of the named table; option adds None | core |
| `nevertype` | Ty.never | empty value family; no return derivable | core |
| `intty` | Ty.int | range proof; bare width widens to the full width range | core, bare-width arm SUGAR |
| `floatty` | Ty.fl | finite in-range by type; bare width widest finite range | core, bare-width arm SUGAR |
| `frange` | Ty.fl bounds | lower and upper bound expressions | core |
| `fexpr` | Ty.fl bound | literal with rounded where inexact, ident, int | core |
| `boolty` | Ty.bool | none | core |
| `range` | indices of Ty.int, args of Block.narrow | lower and upper bound expressions | core |
| `array` | D.Tab with count N | element index as index type | SUGAR |
| `structty` | D.Tab with count one | fields as slot fields | SUGAR |
| `field` | D.Feld with D.typ | where clause becomes Block.pruefung at the read | core |
| `fieldty` | D.typ | embeds arm desugars to a byte view | core, embeds arm SUGAR |
| `bitpos` | none | layout is the emitter's concern | LESESTELLE G-LAYOUT |
| `variants` | Ty.sum | case index by shape with payload | core |
| `fnptr` | Ty.fnptr | signature promise carried at the type | core |
| `fncontract` | Signatur | requires, ensures, effects, costs at the type | core |
| `typelist` | List Ty | positional type arguments | core |
| `params` | Signatur.params | names bind the context | core |
| `fnptrparams` | Signatur.params | positional parameters | core |
| `fnptrparam` | Signatur.params element | name optional | core |

## Section 3 — pointers and spaces (4 productions)

| production | Lean carrier | attribute side | kind |
|---|---|---|---|
| `ptrty` | Ty.ptr | carrier number with rw flag | core |
| `space` | none | barrier follows from space; emitter declaration fact | LESESTELLE G-SPACE |
| `rights` | rw flag of Ty.ptr | combination of rights | core |
| `right` | rw flag; own arm desugars to an owner-mark borrow | mark borrowed for the call and returned | core, own arm SUGAR |

## Section 4 — expressions (22 productions)

| production | Lean carrier | attribute side | kind |
|---|---|---|---|
| `expr` | Expr dispatch | result range carried in the type index | core |
| `orexpr` | Expr.oder | boolean operands | core |
| `andexpr` | Expr.und | boolean operands | core |
| `cmpexpr` | Expr.lt, Expr.le, Expr.eq; remaining arms by nicht with swapped operands | boolean result | core, derived arms as in Zucker.lean |
| `bitexpr` | Expr.band, bor, bxor, shl, shr | nonneg ranges with width proofs | core |
| `addexpr` | Expr.add, Expr.sub | corner ranges of the operands | core |
| `mulexpr` | Expr.mul, div, rem, sdiv, srem | denominator proofs with sign bounds | core |
| `unary` | Expr.nicht, Expr.neg; tilde arm desugars to xor with the full-width mask | unsigned operand with declared width | core, tilde arm SUGAR |
| `fnvalue` | Expr.fnref, Expr.ptrOf | exact signature; declared carrier number | core |
| `primary` | Expr dispatch; result names the ErgCtx head variable in ensures | guards and payload per arm | core |
| `countexpr` | Block.bindCall | generated count function with requires; one table only | SUGAR |
| `reasonval` | Expr.grund | ground of the same declaration | core |
| `optionexpr` | Expr.some, Expr.none | index payload | core |
| `paren` | identity | grouping only, dropped by the parser | SUGAR |
| `call` | Stmt.call, Stmt.callInd, Block.bindCall family | RufPasst with the gruende discipline | core |
| `arglist` | Args | positional arguments | core |
| `arg` | Args.cons | labelled arm is the record constructor | core, labelled arm SUGAR |
| `builtin` | Expr.lit | translation-time number | SUGAR |
| `oldexpr` | Expr.altGlob, Expr.altSlot | entry world under the place guards; ensures only | core |
| `place` | Expr.var, glob, slot, durch dispatch | guards in context, write rights at the use | core |
| `placesuffix` | place step | field, index, or dereference step | core |
| `placelist` | List of places | payload and effect lists | core |

## Section 5 — predicates (11 productions)

| production | Lean carrier | attribute side | kind |
|---|---|---|---|
| `pred` | Expr of type bool dispatch | contract-position restriction is surface-level | core |
| `orpred` | Expr.oder | boolean operands | core |
| `andpred` | Expr.und | boolean operands | core |
| `notpred` | Expr.nicht; implication arm desugars to or with negated head | boolean operands | core, implication arm SUGAR |
| `atompred` | dispatch | per-arm carrier | core |
| `heldpred` | none as a term | witness Res.held in context; shared second kind | LESESTELLE G-HELD |
| `quant` | Expr.forallSlots, Expr.existsSlots | index binder with guards in context | core |
| `domain` | binder of the quantifier | slots, elems, and queue direct; descendants, ancestors, chain, threads, and mappings desugared | core, named arms SUGAR |
| `member` | desugared exists with equality | domain of the enclosing quantifier | SUGAR |
| `reach` | Expr.reaches | option-index field with count-step fuel | core |
| `predlist` | List of boolean Expr | contract clause lists | core |

## Section 6 — functions and contracts (9 productions)

| production | Lean carrier | attribute side | kind |
|---|---|---|---|
| `fndecl` | Signatur with Programm.requires, ensures, rumpf | contract, exact Held set, decreases fuel | core; spec-fn, const-fn, refines, maintains, and by-induction arms SUGAR or none |
| `asmrumpf` | D.Ax | in, out, and clobbers strings | core |
| `asmops` | D.Ax arguments | register bindings | core |
| `asmop` | D.Ax argument | name and result bindings | core |
| `inductlist` | none | names the schemes, no term | LESESTELLE G-SCHEME |
| `induct` | none | names one scheme, no proof step | LESESTELLE G-SCHEME |
| `efflist` | Signatur and Vertrag fields | footprint of the body | core |
| `eff` | schreibt, gschreibt, haelt, konsumiert, produziert | exact Held set with linear consume and alloc | core |
| `breakstmt` | Stmt.breaking | restoration owed at return through schuldet | core |

## Section 7 — statements (18 productions)

| production | Lean carrier | attribute side | kind |
|---|---|---|---|
| `block` | Block | fall-off outcome ok | core |
| `endblock` | Endblock | no fall-off; closing brace sugar for return where typeless | core |
| `endstmt` | Endblock.ret, retGrund, leave, next | context equals allocs at return | core |
| `stmt` | Stmt and Block dispatch | context threading | core |
| `leavestmt` | Stmt.leave | under a loop | core |
| `nextstmt` | Stmt.next | under a loop | core |
| `advstmt` | Stmt.advances | mark at stage a, next stage below the count | core |
| `awaitload` | Block.awaits | payload equals the declared set | core |
| `exchstmt` | Block.exchange | read, compute, and write as one statement | core |
| `xform` | Block.exchange arms | bounded and on-exceeded as at retry | core |
| `letstmt` | Block.bind, bindCall, bindCallInd, bindCallElse, bindAxiom | mut is a surface flag; else branch is an endblock | core |
| `assign` | Stmt.assignVar, assignSlot, assignDurch, assignGlob | index type, guards, write rights; op arms desugar | core, op arms SUGAR |
| `stateassign` | Stmt.uebergang | declared pair; pre-state is writer logic | core |
| `exprstmt` | Stmt.call, Stmt.axiomCall | call in statement position | core |
| `ifstmt` | Stmt.ite | boolean condition | core |
| `matchstmt` | Stmt.onTag, onOption, onGrund | exhaustiveness by shape of the arm list | core |
| `matcharm` | Arms, GrundArms | declaration order with payload binder | core |
| `narrowstmt` | Block.narrow, Block.gleitNarrow | else branch is an endblock | core |

## Section 8 — loops (4 productions)

| production | Lean carrier | attribute side | kind |
|---|---|---|---|
| `loopform` | dispatch | per-form carrier | core |
| `traverse` | Stmt.traverse | finite index set; consuming removal is generated | core |
| `retry` | Stmt.retry | numeric bound with named overrun; ident overrun desugars | core, ident-overrun arm SUGAR |
| `forever` | Stmt.forever | compulsory progress assumption with per-pass bound | core |

## Section 9 — tables, traversals, formats (15 productions)

| production | Lean carrier | attribute side | kind |
|---|---|---|---|
| `table` | D.Tab, count, Feld, typ, braucht, geteilt, eigner | guards, sharing, owner mark | core |
| `treedecl` | side condition of Expr.reaches | edge declared once | core |
| `kante` | edge name | parent, child, or sibling field | core |
| `occdecl` | side condition of the generated requires | occupancy field | core |
| `opdecl` | generated Fn with Signatur | requires with writes on the carrier | SUGAR |
| `opname` | generated operation name | insert and remove are callable; relabel has no body | core, relabel arm gap G-RELABEL |
| `walkdecl` | D.Tab per level with nested Stmt.traverse | constant level count | SUGAR |
| `slotdecl` | D.Feld collection | field declarations | core |
| `slotfeld` | D.Feld with D.typ | by-ops restriction through writes sets | core |
| `slottype` | D.typ | wrapping arm desugars to rem | core, wrapping arm SUGAR |
| `invariant` | D.Inv with Programm.invariante | owed through schuldet with locks of all carriers | core |
| `costexpr` | none | cost class annotation | LESESTELLE G-COST |
| `format` | D.Tab with count one, leseBytes view, pruefung | offset bound, endian order, where check | core; bitfeld, embeds, and endian-big arms SUGAR |
| `reason` | Ty.grund | declared grounds | core |
| `state` | D.erlaubt | declared transition pairs | core |

## Section 10 — devices (11 productions)

| production | Lean carrier | attribute side | kind |
|---|---|---|---|
| `device` | D.Reg, rtyp, rklasse, spiegel, rzusage | outside the world; oracle answers | core |
| `mirrors` | D.spiegel | declaration fact read by transition | core |
| `bank` | D.Reg per index | index of index-into-bank type | core |
| `regdecl` | D.Reg with rtyp, rklasse, rzusage | class, promise, fallible else form | core |
| `regklasse` | Regklasse | readable and writable projections | core |
| `regphasen` | D.rklasse per stage | stage of the order mark in context | core |
| `regfeld` | D.Reg per field | field with its own class | SUGAR |
| `transition` | Stmt.transition | writable target with readable mirror, mask with bits | core |
| `transset` | Stmt.transition arms | several places in one move | core |
| `placeshift` | transition and state arm | place bounds per arm | core |
| `shiftplace` | restricted place | no dereference-suffix form | core |

## Section 11 — concurrency (9 productions)

| production | Lean carrier | attribute side | kind |
|---|---|---|---|
| `atomicdecl` | D.Glob with nutzlast and atomar | pairing; order is the memory-model assumption | core |
| `publishstmt` | Stmt.publish | payload equals declared; writes right | core |
| `nutzlast` | payload list argument | equality proof against the declaration | core |
| `lockdecl` | D.Lock, rang, maskiert with braucht | rank, protects set, cost bounds emitter-side | core |
| `lockstmt` | Stmt.locks | rank above everything held; shared second kind | core, shared arm SUGAR |
| `rcudecl` | D.Lock of rank zero with braucht | grace period is an assume | core |
| `observestmt` | Stmt.locks on the RCU lock | no rank comparison inside | SUGAR |
| `gruppedecl` | D.Inv over several carriers | owed by writers of either carrier | core |
| `concurrentdecl` | none in Syntax.lean | declared set wired by Extraktion and Wettlauf | LESESTELLE G-CONC |

## Sections 12 and 13 — assumptions, axioms, checks (3 productions)

| production | Lean carrier | attribute side | kind |
|---|---|---|---|
| `assume` | D.Annahme | named assumption with falsifier or reason | core |
| `axiom` | D.Ax | foreign body; requires arm desugars to a pruefung | core, requires arm SUGAR |
| `check` | D.Marke Duty | generated allocs with consumes at gates | core |

## Reading points — gaps named

Every LESESTELLE above carries one of these gap names. A gap is a
deliberate absence: the parser handles the surface (lexing, filtering,
name resolution, or wiring outside Syntax.lean) and there is no term to
translate.

- G-LEX: the lexer tokens. Fourteen rules (ident, letter, digit,
  hexdigit, int, dec, hex, bin, float, string, char, quote, newline,
  comment) have no constructor by design; SYNTAX.md states the lexis has
  none and the token-to-tree map is the parser itself.
- G-NAME: the name combinators. Four rules (path, pathseg, identlist,
  regbind) never stand alone; they arrive as name, list, and pair
  arguments inside declaration and call constructors.
- G-FILTER: buildgate. The gate filters the item list before the theorem;
  present items carry no trace of it.
- G-LAYOUT: bitpos. Layout positions are the emitter's; the value read
  has the field type and nothing else reaches the tree.
- G-SPACE: space. The address space is a declaration attribute feeding the
  barrier choice; only the retires-from-space use names it in a term.
- G-SCHEME: induct and inductlist. They name the compiler-generated
  induction scheme; no lemma and no proof step enter the term.
- G-HELD: heldpred. Held is not a value but a fact about the derivation;
  its carrier is the context index of every Expr and Stmt.
- G-COST: costexpr. The asymptotic class annotates the invariant
  declaration; checking it against the declaration is not a term.
- G-CONC: concurrentdecl. The declared-concurrent set has no Syntax.lean
  constructor; its carrier is the Nebeneinander premise with the
  Extraktion wiring that computes footprints, edges, and pairs.
- G-RELABEL: the relabel arm of opname. Insert and remove name generated
  functions; relabel gets no call form because it gets no body.

## Coverage

Productions mapped: all 161 defined rules appear in the tables above
(lexis 18, section 1 with 14, section 2 with 23, section 3 with 4,
section 4 with 22, section 5 with 11, section 6 with 9, section 7 with
18, section 8 with 4, section 9 with 15, section 10 with 11, section 11
with 9, sections 12 and 13 with 3). Of these, 12 rows are SUGAR (parser
emits definitions: accdecl, constdecl, array, structty, countexpr,
builtin, paren, member, opdecl, walkdecl, regfeld, observestmt), 25 rows
are LESESTELLE under the ten gap names above, and the remaining 124 rows
are core. No production is left without a row; mixed rows name their
sugar arms in the attribute cell (bare-width types, own pointers, tilde,
implication, quantifier domains, spec and const functions, refines,
maintains, op assignment, ident overrun, wrapping, format views, shared
locks, axiom requires).

## What this draft does NOT move

- No change to SYNTAX.md; the file stays the grammar source.
- No change to Syntax.lean or any other Lean file.
- No change to crates; no checker or emitter behaviour is specified here.
- No verification: whether a parser implements this map is the open
  measurement of section 16.2 item 8, not a claim of this draft.
- No builds were run for this draft; both sources were read read-only.
