# Source bridge for direct x86-64 validation (lane 277)

*Owner: lane 277. Scope: audit only — no model, goal, parser, checker,
emitter, or ledger edits. The coordinator integrates central imports and
status. Companion wave contract: `dokumente/x86/WELLE-A.md`. Canonical
machine vocabulary: `grammatik/Grammatik/X86/Typen.lean`
(`Gabbro.Grammatik.X86`). Active plan:
`dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §§0–5; §§6–7 are the dated
C-backend record and are not evidence for x86 bytes.*

## 0. What this document is

The direct-x86 chain must close over **every source text and every final
image** the validator accepts, with no function name, example number, or
handwritten per-program model on the trust path. This document audits the
existing source-computed interfaces — parser/elaborator output, the unit,
the layout, the duties, and the hypotheses of the goal and closing
theorems — and states exactly which pieces feed final-byte validation
directly, which gaps block generic coverage, and what the generic closing
schema for phase B looks like. Nothing here changes the language or the
proofs; open items name their file and theorem, not a new rule.

Reading guide: §1 lists the precise interfaces with their defining
files. §2 says what each contributes to the x86 chain. §3 lists the
blocking gaps by semantic family. §4 gives the generic closing schema.
§5 lists the per-example and per-name artefacts that must stay off the
trust path. §6 separates the three certificate kinds. §7 proposes minimal
adapter ownership for phase B.

## 1. Source-computed interfaces (exact names)

All names below are the Lean definitions, not Rust prints. A Rust
printer of any of them is an untrusted hint checked by `decide` or `rfl`
against the computed form; it never enters a premise.

### 1.1 Front end: text to program

- `uebersetzeAllg : String → Except String (Σ u : UProg, Programm
  (declOf u) × List (declOf u).Fn)` (`grammatik/Grammatik/Schlusssatz.lean`):
  lex (`lex` / `lexL`), deep parse (`parseTopTief`), preprocessing
  (`pre108`: `concurrent` items stripped, bare `u32` as its full range),
  elaboration (`elabU`), generic lowering (`lowerAllg`).
- `declOf : UProg → Deklaration`
  (`grammatik/Grammatik/Parser/UebersetzeAllg.lean`): the declaration
  built from the source itself — index carriers (`Fin n`) for tables,
  locks, fields, functions. Lookups: `tabAt`, `lockAt`, `fnAt`,
  `fieldCount`, `tabIdx`, `lockIdx`, `fnIdx`, `fieldRangeO`,
  `boolFeldAt`, `typAt`, `needsAt`, `heldAt`.
- `lowerAllg : (u : UProg) → Except String (Programm (declOf u) × List
  (declOf u).Fn)` (`grammatik/Grammatik/Parser/UebersetzeAllg2.lean`):
  the last front-end stage; lowers every elaborated unit onto its own
  declaration.
- `elabU : List SItemTief → Except String UProg`, `pre108`
  (`grammatik/Grammatik/Parser/Uebersetze.lean`,
  `UebersetzeAllg2.lean`): elaboration and preprocessing.
- Parse-fidelity lemma `uebersetzeAllg_von_zeichen`
  (`Schlusssatz.lean`): the four stage equations imply the pipeline on
  `String.ofList l` without running the UTF-8 decoder in the kernel
  (OFFEN O13, closed 2026-09-15). Chain instances use this lemma.
- `uOf : String → Option UProg` (`bruecke/Bruecke/Quelle.lean`): `some u`
  iff `uebersetzeAllg src = .ok ⟨u, _, _⟩`. Fixes the program a witness
  may name: a witness `u` with `uOf src = some u` can only be the front
  end's own output.

### 1.2 The unit (goal-theorem shape, computed from the source)

`Zielsatz.Einheit (D : Deklaration)` (`grammatik/Grammatik/Zielsatz/Spec.lean`):
`P : Programm D`, `S : SperrInv D`, `Q : AxEns D`, `starts : List (Σ w :
D.Fn, Env D (D.params w))`, `sp0 : Speicher D`, `gestartet` (default `[]`).
`Einheit.ws` is `starts ++ gestartet ++ gestartet` mapped to functions.

The source-computed unit is `einheitAllg (u : UProg) (P : Programm
(declOf u)) (h : nullB u = true) : Zielsatz.Einheit (declOf u)`
(`bruecke/Bruecke/Quelle.lean`):

- `P := P` — the parser's program, nothing else.
- `S := SperrInv.leer (declOf u)` — no lock invariant.
- `Q := axWahr (declOf u)` — the trivial axiom ensures.
- `starts := startsAllg u` — dispatch targets of the unit's `entry`
  items, each parameterless (the front end refuses any other shape),
  started with the empty environment; unknown names filtered out via
  `fnIdx`.
- `sp0 := nullSp u h` — the zero memory (the C's statics are
  zero-initialised): `false` at bool fields, `⟨0, _, _⟩` at ranged
  fields.

`nullB (u : UProg) : Bool` decides that every declared field range
contains `0`; `null_bereich` is its soundness against `fieldRangeO`.
A field whose range excludes `0` has no zero memory and is refused by
name; no theorem here claims anything about such a unit.

Enumerations (needed by premise (a)): `aufzFn` (all functions),
`aufzLock` (all locks), `aufzTraegerLeer` (no carriers — only valid
with `ht : u.tabellen = []`) (`bruecke/Bruecke/Quelle.lean`).

### 1.3 Shape and rank checks (Bools, decided)

- `stimmigB (u : UProg) : Bool` and `stimmig_of : stimmigB u = true →
  Stimmig u` (`bruecke/Bruecke/Pruefung.lean`): the name conditions
  (no bool field/result in the fragment, exactly one pointer parameter
  per table where required, and related well-formedness).
- `rangAuto (u : UProg) : String → Nat` (`tiefe u (u.fns.length + 1)`)
  and `rangB u rk : Bool` with `rang_of : rangB u rk = true → Rang u rk`
  (`bruecke/Bruecke/Pruefung.lean`): the recursion-rank condition over
  the computed call graph. `Pflichten` uses `rangAuto` directly, so the
  rank is computed, not supplied.

### 1.4 The duties (the statement, computed)

`Pflichten (src : String) : Prop` (`bruecke/Bruecke/Quelle.lean`):

```
∃ u : UProg, uOf src = some u ∧ nullB u = true ∧ stimmigB u = true ∧
  rangB u (rangAuto u) = true ∧
  ∀ c : Fin u.fns.length, ∃ body, zuBody u (fnAt u c) = some body ∧
    meetsU u (wfU u) (fnAt u c) body
```

Component computed forms (`bruecke/Bruecke/Pflichten.lean`):

- `zuBody (u) (f) : Option (List Stmt)` — the body of `f` as
  `Gabbro.Body` sees it; `none` = outside the fragment (never a weaker
  body). Covered: slot writes through a pointer or at a table, direct
  calls, trailing `return`, `sideExpr` operands (literals, parameters,
  slot reads, `add`/`sub`/`mul`, widening conversions read as their
  operand, `band`/`bor`/`bxor`). Refused by name (`none`): `assignB`,
  `assignTabB`, lock open/close statements, `alt`/`erg` outside
  `ensures`, bool returns, arithmetic inside an `ensures` side, bool
  slot reads, unknown operators.
- `preExpr (f) : Expr` — `requires`: parameter shapes as `hasShape`
  conjunctions plus one `true` per held lock (held locks are the
  caller's duty via the lock rule, not a value obligation).
- `postU (u) (wf) (f) (s s') (r) : Option Prop` — the promise: `wf s' ∧
  answer-range ∧ clause₁ ∧ …`, right-nested via `chain`; `none` when any
  `ensures` clause leaves the fragment. Clause form `ensClause`:
  `old(..)` reads numbered to `old#i` binders over the entry state,
  `result` bound to the answer, term evaluated at the exit world
  (`clauseAux`/`clauseProp`). `resultClause`: the declared answer range.
- `meetsU (u) (wf) (f) (body) : Prop` — what a person proves: for every
  environment `ρ` and entry state `s` with `wf s` and `preExpr` true,
  under the callee hypotheses `hyps u wf ρ (calleesOf f)` (contract +
  frame of every callee, sorted/deduped by name), the execution
  `exec ρ body s` ends in `s'` with `(postU …).getD False`.
- `shapeOfU`, `slotShape`, `shapeConjuncts`, `conjE`, `calleesOf`,
  `hyps`, `preProp`, `andAll`, `chain`, `ensList` — the wiring; all
  computed from `UProg`.

Bridge theorems (`bruecke/Bruecke/Quelle.lean`, over
`bruecke/Bruecke/Simulation.lean`'s `bruecke_nutzer`/`bruecke_nutzerA`):

- `nutzer_aus_quelle {src} (hp : Pflichten src) {u P fs}
  (h : uebersetzeAllg src = .ok ⟨u, P, fs⟩) :
  ∃ hn : nullB u = true, Zielsatz.NutzerPflicht (einheitAllg u P hn)` —
  premise (b) without the rely, for EVERY accepted source, from the
  computed duties.
- `nutzerA_aus_quelle` — the same with the atomic rely
  (`NutzerPflichtA`), via `nutzerPflichtA_ohne_atomar` over
  `declOf_kein_atomar` (a bridged unit has no shared atomic, so the rely
  is empty there).
- `pflichten_null`, `lower_of_uebersetze`, `uOf_eq` — the plumbing.

### 1.5 Premise (a): the checker Bool and its soundness

- `AkzeptiertSpec (P) (S) (fs ws)` (`Zielsatz/Spec.lean`): `frag`,
  `abg`, `fuss`, `stufen`, `sperrOrte`, `wurzeln`, `einzeln`
  (pool-safety since fix lane F10), `renn`, `antworten` (W1), `masken`
  (handler discipline `H102`, Opus agent H).
- `AkzeptiertSpecX` — the same with `fuss := FussSX` over admitted
  shared atomics `GeteiltV P ws` (Opus lane O25c): an `atomic` global
  with no guard lock, not thread-local among the starts (`GeteiltA`),
  mentioned by no contract or owed invariant (`VertragsFrei`).
- `Pruefer` / `PrueferX`: `akzeptiert E fs ls cs : Bool` plus
  `korrekt` (soundness against `AkzeptiertSpec` / `AkzeptiertSpecX`).
  Concrete checker: `akzeptiertX_pruefer`.
- `NutzerPflicht E` (`LogikPflicht` at every `forever` budget: body
  triples, owed invariants at value AND reason exits, lock/axiom
  locality; plus `StartPflicht`: every lock invariant and every declared
  start's `requires` at `sp0`) and `NutzerPflichtA E` (every body by
  `execEndHA` against every atomic environment in `HavocA (GeteiltA
  E.P E.ws)`).
- `HardwareAnnahmen O E.Q` (c), `Laufzeit E sp init` (d, loader +
  thread creation, A4).
- `GabbroZiel` (over GX, `ZielFX`/`ZielX`, `PrueferX`,
  `NutzerPflichtA`), `GabbroZielSC` (corollary, derived by
  `gabbro_ziel_sc_aus`), `GabbroZielVerbund` (linked two-unit statement).
  Proofs: `Zielsatz/BeweisAtomar.lean` (`gabbro_ziel`),
  `Zielsatz/Beweis.lean` (`gabbro_ziel_sc`). Axioms: exactly `propext`,
  `Classical.choice`, `Quot.sound`.

### 1.6 Layout and correspondence (C record, kept for reuse of shape only)

- `EmitLay (D)` (table/global layout), `KCert (D)` (the generic
  certificate `gabbro corr-lean` prints), `korrOk EL fnNr zert P fs :
  Bool` (`grammatik/Grammatik/KorrespondenzAllg.lean`) with soundness
  `korrOk_fnCorr` at every call depth. Covered C forms: slot stores
  through a pointer or at a named table, local stores, direct calls with
  arguments, `let`, `(void)x;`, `return` of an expression or nothing,
  void fall-off; 27 of 42 `Expr` constructors, 5 of 27 `Stmt`
  constructors. Everything else: `false`.
- `Kette (src)` (`Schlusssatz.lean`): `u`, `E`, `fs0`, `uebersetzt`,
  `fs`/`ls`/`cs` (`Aufzaehlung`), `akzeptiert`, `nutzer`, `EL`,
  `zert`, `zertOk`.
- `schlusssatz (K : Kette src) O hH orc XR hXR bin tief hA1 sp init
  hA4` — six conclusions (parse fidelity; certificates; model judgement;
  every C run; the machine via `P.mitRuhe`, `ziel_ort_einfaden_ende`,
  `gabbro_ziel`; every binary run). Hypotheses about the world outside
  Lean are named: `hH` (c), `hXR` (foreign determinism), `hA1` (+A2/A3,
  binary behaviour refines C semantics at the layout), `hA4`
  (single-threaded start).
- Table-free closed chain from the source: `emitLayLeer` (empty layout
  from `ht : u.tabellen = []`), `ketteAllg` (`bruecke/Bruecke/Quelle.lean`).

## 2. What feeds final x86 validation directly

| Source-side piece | Feeds x86 directly | How |
|---|---|---|
| `uebersetzeAllg` + `declOf` + `lowerAllg` + `uOf` | yes | T3 parse fidelity is target-independent. The x86 validator takes the same `P` over the same `declOf u` from the same `src`; `uebersetzeAllg_von_zeichen` keeps its shape (character-pinned stages). No change needed except extending `elabU`/`lowerAllg` coverage as §3 closes (each extension needs its Lean model + checker side first, per standing rule). |
| `Pflichten src`, `meetsU`/`zuBody`/`postU`/`preExpr` | yes | User-duty computation is machine-independent: bodies run by `exec`/`execEnd`, contracts over entry/exit worlds. The GabbroV bridge (`bruecke_nutzer`, duty files vs `zuBody` reference) is reused unchanged for the x86 chain; `nutzer_aus_quelle`/`nutzerA_aus_quelle` supply premise (b) for the same `E`. Extending `zuBody` coverage extends (b) without touching the x86 side. |
| `nullB`/`nullSp`, `stimmigB`, `rangB`/`rangAuto` | yes | Decided Bools over the source; carried into any target chain unchanged. `rangB` (recursion rank over the computed call graph) already constrains the lowering the x86 validator must respect. |
| `einheitAllg` (`S := leer`, `Q := axWahr`, `startsAllg`, `nullSp`) | yes, as the base case | The shape of `E` the x86 refinement starts from. Units with lock invariants, non-trivial axiom ensures, non-empty `gestartet`, or non-zero memories need the general `Kette`, not `ketteAllg` — see §3. |
| `PrueferX` / `AkzeptiertSpecX`, `NutzerPflichtA`, `GabbroZiel` over GX, W/GX thread model | yes | The selected concurrency foundation (plan §3). The x86 work proves a per-access machine-to-W/GX refinement; it does not rebuild race freedom, contracts, locks, lifecycle, or progress. `Pruefer.alsX`, `nutzerPflichtA_of_akzeptiert`, `geteiltV_leer`, `fadenErreichbarX_of`, `zielF_of_X` carry the SC corollary. |
| `HardwareAnnahmen`, `Laufzeit` | yes, with x86-specific instances | Form reused; content extended: validated entry state, loaded-image mapping incl. relocations, calling/memory conventions, per-access TSO behaviour, timing bounds become named hardware premises. OS/scheduler/runtime code stays user/binding logic with contracts, never a new hardware assumption. |
| `Kette` structure (parse, unit, checker Bool, user proof, layout, certificate, check) | yes, as architecture | The x86 chain keeps the six-field shape; only the last two fields change kind (see §6). `schlusssatz` parts 1–3 and 5 are reused; parts 4/6 are re-proved against decoded bytes instead of C semantics. |
| `korrOk` / `KCert` / `EmitLay` / `CallAt` / C lemmas (`ecorr_*`, `scorr_*`) | no (reuse architecture only) | C-specific correctness conclusions do not transfer. The validator needs a new sound check from the final image to P/GX (plan T2); C lemmas are regression evidence while the C backend is in use, not premises of any x86 chain. |

## 3. Gaps that block generic coverage

Each gap names what is missing for EVERY-source-text coverage. None is
closed by trusting a Rust print or by a per-program file.

1. **Tables (non-empty units).** `ketteAllg`/`emitLayLeer`/`aufzTraegerLeer`
   require `u.tabellen = []`. A unit with tables needs a computed layout
   over its table/global blocks (x86 object layout, widths, overlapping
   accesses, alignment) and a carrier enumeration with content — the
   IMAGE-ABI lane's contract (lane 276). Source side is ready
   (`declOf`, `fieldRangeO`, `typAt`, footprint rules); the missing
   piece is the validated x86 layout + ownership relation, not the
   model.
2. **Statics and globals.** `einheitAllg` has no globals (`globs := fun
   g => nomatch g`); `nullSp` covers table slots only. Static
   initialisers, `static mut`, zeroing, and the loader's copy into the
   image need a validated data-segment relation (lanes 276/273). The
   `N569`/`N570` region discipline (`region.leeren`, `static.ausrichtung`)
   is checker-side and carries over; its x86 memory effect still needs
   correspondence.
3. **Shared atomics (the rely in a bridged unit).** `nutzerA_aus_quelle`
   goes through `declOf_kein_atomar`: bridged units have no shared
   atomic, so the rely is vacuous there. Example 162 (`geteilte-flagge`)
   is the first certified program with one, but it is not bridged
   (`zuBody` has no atomic form; `stimmigB`'s `keinBoolB`-style refusal
   pattern would need the atomic analogue). Until the bridge covers an
   atomic-bearing fragment, every program that relies on an unguarded
   atomic read across threads (OFFEN O25 residue: the plain-payload
   hand-off) reaches premise (b) only as an assumption, not from
   `Pflichten src`. The TSO/GX bridge (lane 274) depends on this:
   per-access atomicity/tearing/ordering correspondence has no
   source-duty counterpart yet.
4. **Arenas and dynamic regions.** No `arena … max` in `einheitAllg`
   (no reservation; `Laufzeit.reserve`/`commit` are Spec-header entries
   only). OFFEN O14 (arena programs close no chain: two statement shapes
   missing), O29 (unbounded regions planned, not required), O37 (a
   region handed by a gate: no G form, no release form). The hosted
   arena runtime and `region.leeren`/`tor.region` templates exist as
   proved C-side artefacts; their x86 counterparts (reserve/commit
   lowering, page return via `madvise`-equivalent gates, `child`
   regions) need target semantics + validator soundness before any
   arena program enters the x86 chain.
5. **Recursion depth and rank.** `rangB`/`rangAuto` decide the rank, but
   the x86 chain must also validate the machine stack bound that makes
   the rank honest: call depths (`tief f`, `rufAt` depth quantifiers)
   against real `call`/`ret` + stack-pointer discipline, and the
   declared cost/budget transfer (lane 278). An unbounded or
   stack-unmeasured lowering would make the rank a paper premise.
6. **Bindings: syscalls, gates, foreign bodies.** `Q := axWahr` and no
   foreign calls in the bridged fragment. Real programs reach the OS
   through `syscall`/`extern` items whose contracts the program declares
   (user logic, never an assumption), region answers (`tor.region`,
   C186), fallible gates (`tor.fehlbar`, `bindAxiomElse`), top-level
   gates (`bindAxiom`), trampolines (`tor.trampolin`), stack-gate clone
   handoff (`tor.kind`, N572, C187), entry hooks (`start.nolibc`,
   `tor.nie`). Each needs: G semantics + checker side (standing rule),
   Body model + bridge simulation, and an x86 correspondence for the
   emitted gate sequence — a C lemma alone does not discharge it.
   Unvalidated external code cannot enter through a declaration alone
   (plan §0). OFFEN O23 (gate preconditions: NUL path, frame length),
   O31 (syscalls as named variables rebound per target), O39 (code
   address as number — closed checker-side by N575–N577, needs x86
   form), O40 (one C name for two private same-name functions — open).
7. **Linking.** `GabbroZielVerbund` proves the linked statement in the
   model; the Rust race residue is closed (Opus agent F), the rest is
   open (OFFEN O28). The x86 chain needs validated per-unit images plus
   a linking step whose relocation/entry resolution is itself validated
   (lane 276) — two separately compiled units stay two chains until
   that step is proved.
8. **Fragment coverage (the binding sieve).** The 2026-09-15 census:
   sieve (a) binds — 20 programs stop at the Lean parser, 89 at
   elaboration (69 an item without G form, 12 a unit without a table, 7
   `bool`, 1 a `requires` without G form); chain count 2 of 129. Every
   construct outside `zuBody`/`postU`/`elabU` (locks held in bodies,
   `sperrtAuf`/`sperrtZu`, `assignB`, bool fields/results, `ensures`
   arithmetic, `traverse`/`by ops`/`mut`/`pub`/`opaque`/`const fn`,
   `costs`/`reads`/deadlines, `entry`/`boot` hardware wrappers,
   `assume`, foreign bodies, devices, MMIO) reaches (b) only as an
   assumption and reaches the image only as an assumption. Coverage is
   multiplicative: closing one sieve class moves the count by the
   programs stopped at no other wall.
9. **Entries, handlers, cores.** `startsAllg` covers parameterless
   `entry` roots; interrupt handlers (`via idt`/any `via`, H102,
   `maskenB`, `KernHaltE`), `boot`/`entry` hardware wrappers, per-core
   cells, and the metal/kmod entries need their x86 entry contract +
   calling-convention proof (lanes 276/278). Handler discipline is
   checker-side (`MaskenDisziplin`); its machine-code side (mask save /
   restore sequences, per-core stacks) is unproved.
10. **Floats, time, progress.** IEEE model exists source-side; the
    scalar-SSE mapping (rounding, exceptions, NaNs, control state) is
    lane 278's obligation. Timing/progress/cost transfer needs validated
    machine costs + named hardware bounds — instruction counts are not
    time bounds (plan §3). `FortschrittG` stop kinds (hardware, flag,
    budget, `nieZurueck`) must be re-established over decoded bytes
    with a proved stutter argument.
11. **Optimisations and lowering.** The wave-A package (constant/copy
    propagation, DCE, CSE, inlining, register allocation, peephole,
    LICM, bounded unrolling, selective SIMD) is untrusted until each
    pass has a checked correspondence certificate (lane 275). Register
    allocation spills, in particular, must preserve footprints —
    private spill slots cannot create new races — with a commutation /
    linearisation proof per grouping, never a block-atomicity
    assumption.

## 4. Generic closing schema for phase B (over EVERY source text/image)

No premise is a Rust print. Each premise is a Lean computation or a
proved statement; per-program instances are witnesses. `X86` below is
the validated target vocabulary (`Typen.lean` + reviewed extensions);
`Bild` is the final image (bytes, layout, entries, resolved
relocations); `valX86` is the proved validator (plan T2 for x86).

```
theorem schluss_x86 {src : String} {bild : Bild}
  (u : UProg) (P : Programm (declOf u)) (fs : List (declOf u).Fn)
  (hU : uebersetzeAllg src = .ok ⟨u, P, fs⟩)          -- T3, computed
  (E : Zielsatz.Einheit (declOf u)) (hE : E.P = P)    -- unit on the parser's code
  (fsL : Zielsatz.Aufzaehlung (declOf u).Fn)
  (lsL : Zielsatz.Aufzaehlung (declOf u).Lock)
  (csL : Zielsatz.Aufzaehlung ((declOf u).Tab ⊕ (declOf u).Glob))
  (C : Zielsatz.PrueferX)
  (hA : C.akzeptiert E fsL.1 lsL.1 csL.1 = true)       -- (a), decided Bool
  (hN : Zielsatz.NutzerPflichtA E)                    -- (b); for bridged
                                                      --   units: (nutzerA_aus_quelle hp h).2
  (O : Zielsatz.Orakel (declOf u)) (hH : Zielsatz.HardwareAnnahmen O E.Q)
  (sp : Speicher (declOf u).mitRuhe)
  (init : Faden → Σ f, Env _ (_.params f))
  (hL : Zielsatz.Laufzeit E sp init)                  -- (d), A4 shape
  (lay : X86BildLayout (declOf u) bild)               -- validated layout: object
                                                      --   extents, widths, alignments,
                                                      --   spill/frame map, entries
  (hV : valX86 lay bild P fsL.1 = true)               -- proved validator accepts
                                                      --   the BYTES, incl. relocations
  (hR : X86Verfeinerung lay bild P O)                 -- per-access refinement:
                                                      --   every admitted x86-TSO
                                                      --   execution of bild refines
                                                      --   to W, hence GX
  : ZielFX-on-every-X86-reachable-thread-machine E O sp init
```

Obligations on the schema (what makes it a theorem, not a wish):

- `X86Verfeinerung` is per-access: every ordinary/atomic access and its
  footprint is mapped; no instruction sequence or source block is
  treated as indivisible without a commutation/linearisation proof over
  actual interleavings. Forbidden-outcome probes (store-buffer
  forwarding, lost RMW, tearing at width boundaries) must fail closed.
- `hR` lands in GX, so `gabbro_ziel` applies unchanged: race freedom,
  contracts, locks, `SchwachX`, `ZeitAbX`, `KernHaltEA`,
  `sperrWechsel`/`sperrSicht`, `FolgeG`, progress legs all transfer.
  The schema does not restate any goal leg.
- For the bridged fragment, (b) is discharged by `Pflichten src`
  (`nutzerA_aus_quelle`); outside it, (b) stays an explicit assumption
  — never a synthesised duty, never a weakened `getD False` read as a
  proof.
- Finite and infinite executions: internal machine steps stutter only
  under a proved progress argument; costs transfer through validated
  machine costs + named hardware bounds.
- Axiom budget: `propext`, `Classical.choice`, `Quot.sound` only; no
  `sorry`/`admit`/`native_decide`/new `axiom`/`unsafe`; every premise
  used; no `Prop`-typed premise smuggling; joint non-degenerate witness
  per target theorem (a table some function writes; a reached run with
  a memory-changing step).

## 5. Artefacts that must NOT enter the new trust path

Existing per-example or per-name rules — kept as regression evidence
and witnesses, never as premises of the x86 chain:

- `corrlean.rs` `Cert104` section: rows only for functions named
  `einzahlen`/`lies` (standing-rule violation, booked for removal).
- `Cert104` / `certOkG` / `refD` map / `GRow` bodies / `printEnd104` /
  `ZeugnisStmt104b.lean`: the 104-cut printer sections and their
  hand maps. Unchanged by the 2026-09-15 widening; not a generic check.
- `schlusssatz_104`, `Kette104`/`Kette104Satz`, `Kette108`,
  `kette_104`/`kette_108` and their witnesses, `gPB`/`gPB_wie_gP`,
  `G104_referenz.gD`, `lowerProg`, `gEL104`, `refCProg`: one-program
  chains, machines, and layouts. Witnesses only.
- `GenOblig104`/`GenOblig108`, `Export104`/`Export108`,
  `Instanz104`/`Instanz108`/`Instanz130`/`Instanz69`/`Instanz73`,
  `Korpus07`/`Korpus109`/`Korpus124`/`Korpus125`/`Korpus59`,
  `KetteMehrfadenC`, `CText104`/`CText108`: per-program exports,
  instances, and hand-written terms. The UNCERTIFIED rows
  (`Korpus07`, `Korpus125`) are reached by hand terms no guardian pins
  to the source.
- `Zertifikat/REGISTER.txt` + `Zertifikate.lean` + `zertifikate.rs`:
  the corpus ledger. Coverage diagnostic (CERTIFIED vs UNCERTIFIED with
  first-refusal codes `LG001`–`LG007`), not a proof over all programs.
  `zaehle-kette.py` measures C chains; it must not be relabelled as a
  binary validator.
- Any `*_zeuge` / `*Zeuge.lean` content beyond its non-degeneracy
  duty: witnesses demonstrate joint inhabitation, they do not establish
  the universal claim.
- The C-form census (`pruefe-cformen.py` lemma/assumption/uncovered
  states, `KNOWN_UNCOVERED`), `chain-instance=` vs `chain=none` marks,
  `MARKE_EMIT*` counters: legacy emission measurements, not x86
  premises.

## 6. Three certificate kinds (do not conflate)

1. **Source/model certificate** — `Pflichten src` + `meetsU` proofs
   (GabbroV duty files checked against `zuBody` reference) and the
   checker Bool re-decided in Lean (`gCheck : … = true := by decide`
   per certified program). Says: the source elaborates, the duties
   hold, the checker accepts. Says nothing about any bytes.
2. **C correspondence certificate** — `KCert` + `korrOk` (+ `EmitLay`,
   `CallAt`, `kProg`). Says: the emitted C has the proved row shape of
   the model program. Says nothing about an x86 image; its closed
   chains (104, 108) do not establish x86 correspondence.
3. **Final-byte correspondence** — does not exist yet. Must say: the
   validated bytes decode (length from decoding, never an emitter
   annotation), execute per the proved `X86` semantics, refine per
   access to W/GX, respect the validated layout/relocations/entries,
   and cover the whole executable code. A proof about an instruction
   listing alone is insufficient; the loaded mapping must match the
   validated image.

Implementation status: (1) exists for the `zuBody` fragment (corpus 104
and 108 closed; 176+ accepted programs UNCERTIFIED with first-refusal
rows); (2) exists for the covered C forms (51 lemmas, 4 named
assumptions, 27 without semantics); (3) is planned — pilot vocabulary
(`Typen.lean`) only, no instruction semantics, no decoder, no TSO
bridge, no validator, no closed chain.

## 7. Minimal adapter ownership for phase B (proposal)

No adapter edits the source model, the goal, the parser, the checker,
or the emitter. Each adapter is a new file with a reviewed import; the
coordinator owns central integration.

- **Source-duty adapter (this lane's follow-up, if tasked):** extend
  `zuBody`/`postU`/`stimmigB` coverage one construct at a time against
  `bruecke/Bruecke/Pflichten.lean` as reference; each extension carries
  its `*_zeuge` (joint, non-degenerate) and its GabbroV printer check.
  Atomic fragment first (unblocks §3.3 and the TSO bridge's duty side).
- **Layout adapter (with lane 276):** computed `EmitLay`-analogue for
  x86 images from `UProg` + validated image header: table/global
  extents, widths, alignments, frame/spill maps, entry points. Purely
  computed; Rust layout hints checked by `decide`.
- **Validator adapter (with lanes 272/273/275):** `valX86` soundness
  (`valX86 … = true →` per-access refinement instance), proved against
  the canonical `X86` types and the actual step semantics — never
  against the Rust mirror. The Rust mirror (`crates/gabbro-check/src/x86/`)
  stays an unwired internal foundation until its Lean correspondence is
  reviewed.
- **Refinement adapter (with lane 274):** machine-to-W/GX per-access
  relation: byte memory, widths, overlap/tearing, store buffers,
  forwarding, coherence, acquire/release, locked RMW (success vs
  failure effects), fences, locks, start/join, publication,
  interrupts, call boundaries. Reuses W/GX/`gabbro_ziel` proofs; proves
  the hardware bridge. Must not assume W already models x86; must not
  treat blocks as indivisible.
- **Template adapter (with lane 278):** entry, lock, call, gate,
  trampoline, and runtime-helper correspondence bound to the target
  semantics; each template machine-checked in the template register
  with its premise bound to the pass that establishes it. C-only
  templates are not evidence here.
- **Measurement adapter:** extend `zaehle-kette.py`-style counting to
  x86 sieves (parse → elaborate → checker → duties → layout →
  validator → refinement) without relabelling C counts; per-sieve
  first-refusal diagnostics over the corpus as coverage signal only.

## 8. Claim ledger (what may and may not be said after this lane)

- May be said: the source-computed interfaces above (§1) are audited
  against their defining files; the reuse/blocked table (§§2–3)
  distinguishes what feeds final-byte validation from what blocks it;
  the phase-B schema (§4) ties every premise to a proved checker, a
  computed user duty, or named hardware behaviour; the exclusion list
  (§5) keeps per-program artefacts off the trust path.
- May NOT be said: that any x86 chain is closed, that any existing
  certificate validates bytes, that any per-program rule is generic, or
  that the goal theorem covers a program the validator has not
  accepted. No Lean file is added or changed by this lane; there is no
  new theorem, no new axiom, and no green-build claim beyond the
  untouched baseline.

*CUTS: docs-only lane. No Lean theorem proved; no decoder, execution,
TSO-bridge, layout, validator, template, or cost correspondence
established here. All file/claim checks are by reading the cited
definitions; no `cargo`/`lake` run is owed by this task (baseline build
untouched). Remaining gaps are §§3–4 and the per-lane deliverables of
wave A (lanes 269–276, 278), none of which this document pre-empts.*
