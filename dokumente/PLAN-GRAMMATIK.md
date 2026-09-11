# The grammar as the proof — plan, build, and the theorem

*Written 2026-09-09, the same day as `PLAN-SICHERHEIT.md`, and against it. Revised the same
evening, twice: first the grammar covers the whole surface and `SYNTAX.md` is one document;
then (turn 4) the six open items of §16.2 are closed — interleavings, memory model, devices
through hardware assumptions, bytes, signed arithmetic, sugar — and `PLAN-UMSETZUNG.md` says
how the checker and the emitter follow.*

> **The task, in four turns:** (1) design syntax and grammar on top of today's so that grammar
> and syntax alone cover everything — memory safety, races, invariants — and the only errors
> left in a Gabbro program are the person's logic and the hardware assumptions; (2) not as an
> appended section: `SYNTAX.md` is to be **the whole syntax**, the Lean proof is to cover
> **everything**, not only what is new; (3) say **what is still not covered** with this syntax;
> (4) close items 1–6 of that list, item 3 (devices) through hardware assumptions, and deliver
> the plan that puts it into the Gabbro checker and emitter — so that Gabbro covers everything
> except logic and hardware assumptions.

> **What was built, in one sentence:** an **attributed grammar** over the **entire** Gabbro
> surface — every production of `SYNTAX.md` §1–§14 carries the side condition a pass checks
> today — formalised as a typed inductive family in Lean 4 (`grammatik/`), with a **total**
> meaning function whose outcome type has exactly two error constructors, `logik` and
> `hardware`. `lake build` is green, 0 `sorry`, no own axioms, no mathlib, no import from
> `programmlogik/` or `passlogik/`. `SYNTAX.md` is rewritten as **one** document: every
> production names its Lean constructor or its sugar, and §16 of it answers turn (3).

---

## 0. The move, and why it is the right one

`PLAN-SICHERHEIT.md` proved *stuck ⇒ own logic* over `Body.lean` by writing a checker and
proving it sound. That is the classic shape, and it has a classic weakness: the checker is
a second register over the grammar, and the seam between them (`W16`) is unproved.

This plan makes the other move. **The grammar itself is the type system.** A production
does not admit a form and leave a pass to refuse it later; the production carries the
condition, and a form that fails it has no derivation. In Lean this is an *intrinsically
typed* syntax: `Expr D Γ Λ τ` is the set of expressions of type `τ` in scope `Γ` holding
resources `Λ`; `Expr.div` takes a proof that the divisor's range starts at `1`;
`Stmt.locks` takes a proof that the new lock's rank exceeds every held one; `Stmt.ret`
takes a proof that the marks in hand are exactly the ones the signature allocs;
`Stmt.regSchreib` takes a proof that the register's class is writable; `Stmt.publish` takes
a proof that the payload is the declared one; `Stmt.uebergang` takes a proof that the
transition is declared.

Then the safety theorem is not proved — it is **the fact that `eval` and `exec` are total
functions**, plus one theorem (`zwei_fehler`) that lists the outcome constructors so a
third one cannot be added quietly. What remains to prove are the properties that are NOT
by construction, and two of those are proved: the **frame** (`exec_rahmen`: a body writes
only what its contract names, up to the whole program) and **deadlock freedom from rank**
(`keine_verklemmung`).

This is also the honest reading of the sentence in the task. *Grammar and syntax* can carry
the goal only if the grammar is attributed; a context-free grammar cannot, and no amount of
EBNF will change that. `SYNTAX.md` is the attributed grammar written for a reader;
`grammatik/Grammatik/Syntax.lean` is the same thing written for a machine.

---

## 1. What stands — the files

```
grammatik/lakefile.toml, lean-toolchain          Lean v4.33.1, no dependencies
grammatik/Grammatik/Typen.lean       349 lines   Ty, Val, Zahl, Gleit; the arithmetic with its ranges, signed division, bytes
grammatik/Grammatik/Syntax.lean      556 lines   THE GRAMMAR: Signatur (with Held), Deklaration (with spiegel, rzusage, shared, a10, U003), Expr (41 constructors), Stmt (28), Block (20), Endblock, Arms, GrundArms, Programm
grammatik/Grammatik/Semantik.lean    791 lines   World with a TRACE, Ereignis, offen, eval (total), Logik (6), Hardware (6), Ausgang (7), Orakel (with sichtbar), exec, rufAt
grammatik/Grammatik/Satz.lean       1403 lines   zwei_fehler, 18 inversions, exec_gut = frame AND trace in one induction over every constructor, exec_rahmen, exec_spur, keine_verklemmung
grammatik/Grammatik/Wettlauf.lean    463 lines   runs, spur, haelt, Gesittet, HB; kein_wettlauf, kein_wettlauf_global, keine_ueberkreuzung
grammatik/Grammatik/Zucker.lean      246 lines   every SUGAR mark as a definition over the core; Expr.weaken
```

`cd grammatik && lake build` — 9 jobs, green, 0 `sorry`; every `#print axioms` shows only
`propext`, `Classical.choice`, `Quot.sound`.

### 1.1 The coverage — every production of `SYNTAX.md`, and where it is

| `SYNTAX.md` | production(s) | in Lean | status |
|---|---|---|---|
| §1 program, modules | `program item module use const static when boot entry entrust accumulates` | `Deklaration`; `const` = `Expr.lit`; `static` = `Glob`; `boot/entry/entrust` = `Ax` | **core** (declaration-level) |
| §2 types | `intty floatty boolty never indexty variants fnptr structty array opaque linear order` | `Ty.int/fl/bool/never/opt/sum/grund/fnptr/ptr`, `Marke` + `stufen`, records = tables of `count 1` | **core** |
| §3 pointers | `ptrty space rights` | `Ty.ptr n rw`; `Expr.ptrOf`, `Expr.durch`, `Stmt.assignDurch` — access through a pointer carries the carrier's guards; `own` = owner mark; bytes: `Expr.leseBytes`, `Stmt.schreibBytes` | **core** |
| §4 expressions | every operator, `place`, `call`, `&f`, `old`, `result`, `Some/None`, `R::F`, record constructor | `Expr` (38 constructors), `Args`, `Block.bindCall` | **core** |
| §5 predicates | `forall/exists`, the eight domains, `reaches`, `Held` | `forallSlots`, `existsSlots`, `reaches`; `Held(L)` = `Res.held L ∈ Λ`; domains as sugar over `forallSlots` | **core** |
| §6 functions | signature with `or R`, `refines`, `requires`, `ensures`, `maintains`, `advances`, `retires`, `effects`, `costs`, `decreases`, `by`, foreign bodies, `breaking` | `Signatur`, `Vertrag`, `Programm.requires/ensures`, `schuldet`, `Stmt.advances/retires/breaking`, `rufAt` (fuel = `decreases`), `Ax` for foreign bodies; `costs`: outside | **core** (`costs`: not a grammar item) |
| §7 statements | `let`, `let … else`, assign, state transition, `if`, `match`, `narrow`, `return`, `leave`, `next`, `publishes`, `awaits`, `exchange`, `advances` | `Stmt`/`Block`/`Endblock`/`Arms`/`GrundArms`: 26 + 20 + 6 + 2 + 2 constructors | **core** |
| §8 loops | `traverse`, `retry`, `forever` with `invariant`, `progress` | `Stmt.traverse/retry/forever`, `traverseLauf/retryLauf/foreverLauf` | **core** |
| §9 tables, formats | `table count backed owner slot invariant ops tree occupied walk format reason state` | `Tab`, `Inv`, `erlaubt`; `ops` = generated `Fn`; `format` = `count 1` + `Block.pruefung`; `walk` = nested `traverse` | **core** (layout: sugar/emitter) |
| §10 devices | `device reg class bank fields transition mirrors requires … else` | `Reg`, `Regklasse`, `Block.regLies/regLiesElse`, `Stmt.regSchreib`, `Stmt.transition` (with `spiegel`), `rzusage` → `hardware (register r)`, `hardware (geraet r)` | **core** (through named hardware assumptions) |
| §11 concurrency | `atomic publishes awaits exchange lock rank locks rcu observes group accumulates shared` | `Lock`, `rang`, `braucht`, `nutzlast`, `geteilt`; `Stmt.locks/publish`, `Block.awaits/exchange` (→ `hardware (sichtbarkeit)`); `keine_verklemmung`, `kein_wettlauf`, `keine_ueberkreuzung` | **core, proved over interleavings** |
| §12 assume, axiom | | `Annahme`, `Ax`, `Orakel` → `hardware (annahme a)`, `hardware (fortschritt a)` | **core** |
| §13 check | | a mark `Duty` produced by the `check`, consumed by `gates` | **core** (sugar over linearity) |
| §14 boot, asm | `raw/prim/extern/asm`, `-> never`, `retires`, `walk` | `Ax`, `Ty.never`, `Stmt.retires` | **core** |
| «F» float | `f32/f64 in`, `rounded`, `finite` | `Ty.fl`, `Gleit` (finite + in range by type), `Block.gleit/gleitLit/gleitVon/gleitNarrow` → `hardware ieee` | **core** (range checked, not derived) |

**Every row is in the core.** What the second revision of this plan listed as *designed*
(«SG-12» … «SG-18») is now formalised, with the exceptions that are not productions but
limits of the meaning — §3.

### 1.2 The error classes, and where each one is carried

| class | carried by | in Lean | status |
|---|---|---|---|
| index in range | `index into T` is the only index type; `narrow` the only way in | `Expr.slot i` with `i : .index (count t)` | **core** |
| no over-/underflow | every number carries its range; every operation its result range | `Zahl`, `Expr.add/sub/mul/…` | **core** |
| no division by zero | numerator `0 ..`, denominator `1 ..` | `Expr.div h0 h1'` | **core** (signed: `narrow` first) |
| bit operators on negatives | both operands `0 ..`, width named | `Expr.band/bor/bxor/shl/shr` | **core** |
| shape errors, non-exhaustive match | typed AST; one arm per case | `Arms cs`, `GrundArms n` | **core** |
| `else` that falls off | `Endblock` | `bindCallElse`, `narrow`, `regLiesElse`, `pruefung`, `gleitNarrow` | **core** |
| **memory safety** — access without guard | every access carries `darf`: `Held(L)` / owner mark in Λ — through a pointer, a byte view, a quantifier, an `old(…)` too | `Expr.slot/durch/leseBytes/forallSlots/altSlot … hL`, `Stmt.assignSlot/assignDurch/schreibBytes … hL` | **core** |
| **bytes** — a run past its carrier, a second view | the run's bound `hi + n ≤ count` is the attribute; views read one world | `Expr.leseBytes`, `Stmt.schreibBytes`, `Zucker.bitfeld/embeds` | **core** |
| **signed division** | the divisor's range excludes zero; `\|q\| ≤ \|a\|` | `Expr.sdiv/srem`, `Zahl.sdiv/srem` | **core** |
| **lock set across calls** | a callee names EXACTLY the held set («SG-20») — so its `locks` stands above everything | `RufPasst.hh` (↔), `Signatur.haelt`, `HeldGenau` | **core** |
| **races over interleavings** | every access event carries its guards and holders; over any interleaving with a mutually exclusive lock primitive, conflicting accesses are happens-before ordered or on an `atomic` | `exec_spur`, `Gesittet`, **theorems `kein_wettlauf`, `kein_wettlauf_global`, `keine_ueberkreuzung`** | **core, proved** |
| **memory model** | `awaits` sees the publication or the outcome is `hardware (sichtbarkeit A10)` | `Orakel.sichtbar`, `Hardware.sichtbarkeit` | **core** (A10 named) |
| **device promise** | a register's `requires` held at every read | `D.rzusage` → `hardware (geraet r)` | **core** (assumption named) |
| **trap 4** (`mirrors`) | `transition` reads the declared mirror by construction | `Stmt.transition hm hl` | **core** |
| **shared carriers** | a shared carrier has a guard; an unshared one belongs to one thread | `D.geteilt`, `geteilt_bewacht`, `ggeteilt_bewacht` («SG-21») | **core** (declaration) |
| **invariants across carriers** (`U003`) | a writer of one carrier of `I` holds the locks of all carriers of `I` | `D.invarianten_gehalten` | **core** (declaration) |
| **sugar** | every `SUGAR` mark is a definition over the core | `Zucker.lean` | **core** |
| **alias** — a second owner | owner marks allocated by nobody; marks linear | `eigner_nie_erzeugt`, Λ | **core** |
| **write through a read pointer** | `assignDurch` takes `.ptr n true` | theorem `zeiger_schreibt_mit_recht` | **core** |
| **wrong signature at an indirect call** | the `fnptr` value carries `sig f = n` | `Expr.fnref`, `Stmt.callInd`, `umsig` | **core** |
| **frame** | write right an attribute; callee's writes ⊆ caller's | **theorem `exec_rahmen`**, every constructor a case | **core, proved** |
| **lock at access**, **lock order** | `darf`; `locks L` requires the greater rank | **theorem `keine_verklemmung`** | **core, proved** |
| **linearity** | Λ a multiset index; `ret` requires `Λ ≡ allocs` | `Untermulti`, `List.Perm` | **core** |
| **phases** (`order`/`advances`) | stage on the mark; `advances a -> b` needs the mark at `a` | `Res.marke m s`, `Stmt.advances`; theorem `stufe_steigt` | **core** |
| **state transitions** | only a declared pair is derivable; the pre-state is logic | `Stmt.uebergang` → `logik uebergang` | **core** |
| **register class** | read needs `lesbar`, write needs `schreibbar` | `regLies hk`, `regSchreib hk` | **core** |
| **publication pairing** | payload = declared payload | `Stmt.publish hp`, `Block.awaits hp` | **core** |
| **invariants** (table, group) | owed at `return` by every writer of a carrier; `maintains` sugar | `schuldet`, `rufAt` → `logik (invariante i)` | **core** — the *proof* is the person's |
| **termination** | finite index set; `retry` bounded; `forever` by named assumption; recursion by `decreases` | `traverseLauf`, `retryLauf`, `foreverLauf`, `rufAt` | **core** |
| **float** | finite and in range by type; the machine's result held against the declared range | `Gleit`, `gleitPasst` → `hardware ieee` | **core** (checked, not derived) |
| **foreign bodies** | contract known, body the machine | `Ax`, `Orakel` → `hardware (annahme a)` | **core** |
| device access ORDER, handler scheduling, cost, emitter | — | — | **not a production: §3** |

### 1.3 The two errors, and the theorem that there is no third

```lean
inductive Logik (D)    | vorbedingung f | nachbedingung f | invariante i | schleife | abstieg f | uebergang
inductive Hardware (D) | annahme a | fortschritt a | ieee | register r | geraet r | sichtbarkeit a
inductive Ausgang (V : Vertrag D) : Bool → Ctx → Type where
  | ok | zurueck | grund | leave | next          -- control flow
  | logik (e : Logik D)
  | hardware (e : Hardware D)

theorem zwei_fehler (o : Ausgang V l Γ) : (control flow) ∨ (∃ e, o = .logik e) ∨ (∃ e, o = .hardware e)
theorem bedeutung_total … : ∃ o, exec P O passes fuel V b σ ρ = o
theorem wert_total (e : Expr D Γ Λ τ) … : ∃ v : Wert D τ, eval σ₀ e σ ρ = v
```

Twelve outcome sources in all (`SYNTAX.md` §16.1), six logic and six hardware. `bedeutung_total`
and `wert_total` are trivial *as theorems* — their content is that the definitions typecheck;
they exist so that a later edit which adds an `Option`, a `stuck`, or a partial match to
`exec` fails loudly.

### 1.4 The theorems that are NOT by construction

**`exec_gut`** — frame AND trace in one induction over the whole grammar (`stmt_gut` 28
cases, `block_gut` 20, `end_gut`, `arms_gut`, `grund_gut`, three loop lemmas, `rufAt_gut`
over the depth). Frame: the outcome world agrees with the entry world on every carrier the
contract does not write. Trace: every event the body appends carries the guards of its
carrier (`darf`), holds every lock its Λ names (`HeldIn`), every `nimmt` is above everything
held in rank and not a repeat, the trace stays consistent (each event's recorded holder set
is the `offen` of its own past), and the locks at the end are the locks at the start. The
premise: `GutO` — the hardware keeps its `effects` and touches neither locks nor trace; and
`HeldGenau Λ σ.haelt` at entry — the body is started in a world that holds exactly what its
Λ claims (trivial at the top, maintained across every call by «SG-20»).

**`kein_wettlauf`** (`Wettlauf.lean`) — over any run (an interleaving of thread steps) that is
`Gesittet`: consistent traces (W1), good events (W2), a lock taken only when no other thread
holds it (W3), a mark in one thread (W4), an unshared carrier in one thread (W5) — two
accesses of different threads to one table are happens-before ordered. The proof: both hold
the guard (W2); if it is a lock, both hold it at their times (W1), and between them the first
thread's `gibt` and the second's `nimmt` must lie (W3 with `haelt_zeuge`/`haelt_von`); if it
is a mark, W4 says they are one thread. **`kein_wettlauf_global`**: the same, or the global
is `atomic`. **`keine_ueberkreuzung`**: the recorded ranks cannot cross.

**`keine_verklemmung`** — two derivations, each holding one lock and deriving a `locks` on
the other's, do not exist; `omega` on the constructor hypotheses.

> **Cut G3 status 2026-09-10: NARROWED** (not the build step G3 in §4; the `InterferenzAllgemein` cut). Shared-side preservation is derived from checked lock discipline (`grammatik/Grammatik/InterferenzAllgemein.lean`: `schuldnerHaelt_gilt`, `eintrittHeldIn_aus_Passt`, `invSichtHaelt_aus_Eintritt`, `fremdDisziplin_gilt`, `fremdErhalt_disjunkt_aus_Disziplin`, `invErhalt_aus_Kontext`): each chain step respects guards and stays in its frame, the disjoint side flows through stability, and where the invariant itself is the property the shared-side premise is the derived equivalence — no preservation premise left to assume.
>
> **Stability status 2026-09-10: PROVED** (general N-thread theorem `allgemeinStabil` over a joint run, with the invariant corollary `allgemeinStabil_invariant`; `stabilSchritt_gilt`, `stabilKette_gilt`, `kette_erhaelt`).
>
> **Device status 2026-09-10: CHAINED** (`grammatik/Grammatik/Geraet.lean`: `dma_uebergabe`, `geraet_ohne_wettlauf`, `kette_anfang_vor_schreib`, `kette_schreib_vor_ende`, `kette_ohne_wettlauf`, `kette_uebergabe`; chained windows with doorbell linkage).
>
> **Copy status 2026-09-10: VALIDATED** (`grammatik/Grammatik/Adressraum.lean`: `gepruefteKopie_ohneToctou`, `modellSequenz_ohneToctou`, `einSnapshotWelt_gibtWertGleich`; validated copy is safe inside the model and wired to `World` (`weltBytes_istBytesAb`, `modellPruefung`/`modellKopie`/`modellSequenz`); the exec-side range check stays missing as booked).

### 1.5 What the semantics takes as a parameter — and why that is the answer

| parameter | what it is | class |
|---|---|---|
| `O : Orakel D` | what an `axiom` does and answers; what a register answers; whether a publication is visible (H1) | hardware |
| `passes : Nat` | how many passes the environment grants a `forever` (H2) | hardware (`progress a`) |
| `fuel : Nat` | the recursion depth; exhaustion is `logik (abstieg f)` | logic (`decreases`) |

These three are not gaps. They are the hardware and the logic — the two things the task
says may remain.

---

## 2. What was changed in `SYNTAX.md` — third version, one document

The second version's §1–§14 stand with every production; the appended §15 «SG» of the morning
is gone, its content is folded into the sections it belongs to. Every production carries a
`Lean:` line or an attribute table. The marks:

| tag | what | kind |
|---|---|---|
| «SG-0» | E6: every attribute is part of the production; the resource context Λ | new decision, no word |
| «SG-1» | `intty` carries its range; bare `u32` is sugar | CHANGED |
| «SG-2» | `+ − ×` carry their result range | CHANGED |
| «SG-3» | `/ %` unsigned with positive divisor; bits/shifts unsigned with width | CHANGED |
| «SG-4» | the index is an `index into T`; `option index` in range | CHANGED |
| «SG-5» | `endblock`/`endstmt`; `fn` body, `let … else`, `narrow … else` are `endblock`; `matcharm` list | NEW / CHANGED |
| «SG-6» | `consumes`/`allocs` as Λ in/out; `return` demands multiset equality; guards on every access | CHANGED reading |
| «SG-7» | `locks L` requires the greater rank | CHANGED |
| «SG-8» | `writes` as an attribute on every store and call; **pointers name carriers**, access through them carries the guards, `fnptr` values carry their signature | CHANGED |
| «SG-9» | `table … owner m` — **the one new word** (221 → 222) | NEW |
| «SG-10» | invariants owed by every writer; `maintains` is sugar | CHANGED |
| «SG-11» | `on_exceeded endblock`; `progress` mandatory at `forever` | CHANGED |
| «SG-13» | `publishes`/`awaits` payload = declared payload | CHANGED |
| «SG-14» | `advances a -> b;` as a statement (`advstmt`); stages on marks; `retires` names its assumption | NEW / CHANGED |
| «SG-15» | register class as attribute of the access; `requires … else` as `regLiesElse` | CHANGED |
| «SG-16» | `format … where` as a check at the read; `walk`/`mappings of` as nested `traverse` | CHANGED (sugar) |
| «SG-17» | every float finite and in range by type; the machine's result checked → `hardware ieee` | CHANGED |
| «SG-18» | foreign bodies are axioms; `-> never` has no `return` | CHANGED reading |
| «SG-19» | `transition place : A -> B;` (`stateassign`) — the state transition as a statement, same word as at a device | NEW |
| «SG-20» | `requires Held(L)` names EXACTLY the held set at every call — the lock set is part of the contract | CHANGED (evening) |
| «SG-21» | `shared` at `table`/`static`: reachable from two threads, hence guarded | CHANGED, no new word (evening) |
| «SG-3» ² | signed `/ %` with a zero-free divisor range | CHANGED (evening) |
| «SG-16» ² | bytes: `leseBytes`/`schreibBytes`; `format` fields as views | CHANGED (evening) |
| «SG-15» ² | `transition` in the core with its mirror; the register promise as `hardware (geraet r)` | CHANGED (evening) |
| «SG-13» ² | `awaits` as `hardware (sichtbarkeit A10)` | CHANGED (evening) |
| «SG-12» | contexts / interrupts | **not a production** — `SYNTAX.md` §16.2 (7); a handler is a thread of the run model |

Five new nonterminals (`endblock`, `endstmt`, `matcharm`, `stateassign`, `advstmt`), one new
word. The `ebnf` fences are real: **the guardians were not run** (no device shell today), and
`SYNTAX.md`'s own state table says so; G1 below is the first item.

---

## 3. What is NOT covered even with this syntax — the answer to turn (3), revised by turn (4)

| item | morning | **evening** |
|---|---|---|
| 1. interleavings | outside the semantics | **theorem** `kein_wettlauf` over any interleaving; premise W3 = the lock primitive's `assume` |
| 2. memory model | assumption A10 | **named outcome** `hardware (sichtbarkeit A10)`; `atomic` is the only unguarded shared access (`kein_wettlauf_global`) |
| 3. devices | assumptions | **named outcomes** `hardware (register r)`, `hardware (geraet r)`; `transition` with its mirror by construction; the device's view of access ORDER is the one `assume` left |
| 4. bytes | not modelled | **in the core** (`leseBytes`/`schreibBytes`, views as sugar) |
| 5. signed arithmetic, float | not derivable / checked | signed `/ %` **derived**; float range checked by the machine = IEEE as the named hardware assumption |
| 6. sugar | prose | **`Zucker.lean`** — definitions over the core |
| 7. contexts, cost, emitter, C | outside | outside — `PLAN-UMSETZUNG.md` §5 |
| 8. the parser | outside | outside — `PLAN-UMSETZUNG.md` §1 (and the derivation prints as Lean, so the parser's output is Lean-checked) |
| 9. the three parameters | not gaps | not gaps |

**The sentence:** with this syntax, no failure of a body is writable except the twelve
outcome sources of `SYNTAX.md` §16.1 — six the writer's logic, six a named hardware
assumption — and over any interleaving of bodies no data race on a guarded carrier and no
crossing of the lock order exists. What is outside is the scheduling of handlers, the cost
model, the parser, and the emitter — none of them an error class of a program.

Carries 2026-09-10/11 (see §1.4 statuses): N-thread stability and its invariant corollary hold as theorems; device windows chain with handover; validated copy holds inside the model; the sentence above stands and reads with those carries.

---

## 4. The build — steps, order, and what each one is measured by

**G1 — Run the guardians against the new `SYNTAX.md`.** *Measurement, first.*
`pruefe-syntax.sh` (closure, reachability from `program`, terminals in the vocabulary —
a hand check of the same three properties passed today, with the `? … ?` special sequences
as the only undefined names, as before), `zaehle-wortschatz.py` (expected 222),
`pruefe-grammatiktafel.py`, `pruefe-englisch.py`, `pruefe-widerruf.py`. A red guardian is a
finding about this file, not about the guardian — with one exception: a rule counter that
reads the attribute tables as prose and finds `owner` before the vocabulary table is a
guardian's fence rule.

**G2 — The attributed parser as a second front end.** *Build.* `gabbro-syntax` keeps its
parser; a new pass `attributiere` turns the AST into the family of `Syntax.lean` — not into
Lean source, into a Rust datum with the same shape, whose acceptance IS the derivation. This
is also where every `SUGAR` mark becomes code. **Measurement:** the 70 clean examples, one
row each: derives / refused at «SG-n». Predicted from `SYNTAX.md` §17: one refusal (`66`,
`forever` without `progress`), plus whatever `state` writes and signed divisions the count
finds.

**G3 — The corpus moves.** `66-transport-rueckgabe.gab` gets its `progress`; `state` writes
become `transition … : A -> B;`; signed divisions get `narrow`; `owner` appears where a
`static` region is owned today by convention. *No file changes meaning; a file that must is
a finding.*

**G4 — The guardian for `grammatik/`.** `instrumente/pruefe-grammatik.sh`: `lake build`,
`grep -c sorry` = 0, no `sorryAx` in `#print axioms`, the constructor count of `Ausgang` = 7,
of `Logik` = 6, of `Hardware` = 4 (ratchets: they may not rise without a row in `SYNTAX.md`
§16.1), the theorem list of `Satz.lean` present. Cheap, and without it every regression is
invisible.

**G5 — Bytes** — done (evening): `leseBytes`/`schreibBytes`, `exec_gut` extended.

**G6 — Devices through hardware assumptions** — done (evening): `rzusage` → `geraet r`,
`transition` with `spiegel`; the access order stays `dma_visibility_in_order`.

**G7 — The threaded semantics** — done (evening) in the form of a trace and a run model:
`exec_spur` + `Wettlauf.lean`. What `RACE.md` lists as unsupported is now either a guarded
access (ordered by the theorem) or an `atomic` (ordered by A10, `hardware`).

**G8 — Into the checker and the emitter:** `PLAN-UMSETZUNG.md`, steps U1–U8.

**Order:** G1 → G4 (both cheap) → G2 → G3 → G8. *No day estimates* (W7).

---

## 5. Speech tests — what the grammar derives, evaluated

`Satz.lean` §4, all by `rfl`:

* `x : u8 in 0 .. 5` — `(x + x) / (x + 1)` **is derivable**: `x + x : 0 .. 10`, `x + 1 :
  1 .. 6`, so the divisor's range starts at 1; result `0 .. 10`. Evaluated at `x = 3`: `1`;
  at `x = 0`: `0`.
* `x / x` **is not derivable**: `.div` demands `1 ≤ 0`, and `¬ (1 ≤ 0)` is the theorem.
* `let y = 1.5 rounded : f64 in 0 .. 10;` — a block with a float literal has an outcome (the
  meaning is total: in range, or `hardware ieee`).
* The sixteen inversion theorems of `Satz.lean` §2 are speech tests in the other direction:
  each says what a derivation at that site *had* to carry — a pointer access its guards, a
  register write its class, a transition its declaration, a publication its payload, an
  `advances` its pre-stage.

---

## 6. The verdict, row by row — against the morning

| | `PLAN-SICHERHEIT.md` (checker + soundness) | this plan, morning (core) | **this plan, evening (whole surface)** |
|---|---|---|---|
| index, overflow, division, bits, shapes | proved as checker property, vacuous in the model | by construction | by construction |
| frame / effects | outside | proved (`exec_rahmen`) | **proved over every constructor**, pointers and registers included |
| lock at access, rank | outside | by construction + proved | same |
| linearity, phases | outside | linearity by construction; phases designed | **both by construction** |
| invariants, state transitions | outside | invariants owed by construction | **both**: `logik (invariante i)`, `logik uebergang` |
| termination | outside | by construction / named assumption | same |
| memory safety | outside | tables and globals; pointers designed | **tables, globals, and pointers** (carrier-level); bytes: G5 |
| devices, publication, float, foreign bodies | outside | designed | **in the core**, each with its `hardware` row (device windows chained 2026-09-10 — see §1.4 status) |
| races | outside | discipline by construction; interleavings not modelled | same — G7 (N-thread stability proved 2026-09-10 — see §1.4 status) |
| seam to the checker (`W16`) | open | gone — the grammar is the type system | same; what replaces it is G2 |
| `SYNTAX.md` | — | §15 appended, fenced `text` | **one document**, every production with its constructor |
| what remains | `requires`, `invariant` | logic + hardware | **ten outcome sources**, six logic and four hardware — and the scope items of §3 |

**So: is the goal reached?** For the sentences of this grammar — **yes, as a theorem**, over
the whole surface AND over interleavings, with the two remaining classes exactly the two the
task allows (turn 4: bytes, signed division, sugar are in the core; devices and the memory
model are named hardware outcomes; races are a theorem over runs). For Gabbro as written
today — **not yet**: the checker does not yet produce the derivation and the emitter does not
yet lower it. That distance is `PLAN-UMSETZUNG.md`, steps U1–U8, each with its measurement.
