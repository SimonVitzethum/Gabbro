# The grammar into the checker and the emitter — the implementation plan

*Written 2026-09-09, evening. Companion to `PLAN-GRAMMATIK.md` (what was proved) and
`SYNTAX.md` §16 (what the theorem says). This file says how Gabbro — the checker
`gabbro-check` and the emitter — becomes what the theorem describes: a language in which
**every failure of a body is the writer's logic or a named hardware assumption**, and nothing
else.*

> **The principle.** `grammatik/Grammatik/Syntax.lean` is the specification of the checker,
> and `Semantik.lean` is the specification of the emitter. A program is accepted when it IS a
> term of `Syntax.lean`; the C the emitter writes is correct when it does what `exec` does.
> Both are checkable: the first by printing the term and letting Lean typecheck it, the second
> by running `exec` and the C on the same input. Nothing in this plan is a new judgment; it
> is the transfer of judgments that already exist in Lean.

---

## 0. What changes, in one table

| today | after this plan |
|---|---|
| twelve passes, each a rule set over an untyped AST, each with its own refusal codes | **one derivation**: the AST is elaborated into the attributed family of `Syntax.lean`; a construct that cannot be elaborated is refused at its site with the hypothesis it lacks |
| a rule that a pass forgets is silently absent (`GRAMMATIK-VOLLSTAENDIG-2026-09-08.md` §1.4) | a hypothesis that is not supplied is a type error in the derivation — it cannot be forgotten, because the term does not exist without it |
| the emitter lowers constructs by its own reading of `SPRACHE.md` | the emitter lowers **constructors**; each constructor has one lowering, and its meaning is `exec`'s clause |
| `hardware` failures are wherever the C happens to fault | every `Hardware` constructor is a **runtime site** (`gabbro_hardware(kind, name)`) or a named `assume` — twelve of them, listed |
| `logik` failures are proof obligations in the ghost theory, or nothing | every `Logik` constructor is an obligation in `gabbro pflichten` AND, under `TESTBUILD`, a runtime check — six of them, listed |
| race freedom is what `H007`/`H006` happen to enforce | the trace of `Semantik.lean` can be **recorded** in `TESTBUILD`; `Wettlauf.lean`'s `Gesittet` is a checkable predicate over the recording — a race detector that is the theorem's premise, not a heuristic |

---

## 1. The derivation — `gabbro-ableitung`

### 1.1 Shape

A new crate `crates/gabbro-ableitung` with one entry point:

```
ableite(ast: &Programm) -> Result<Ableitung, Absage>
```

`Ableitung` is a Rust datum with the same shape as `Syntax.lean`: an enum per family
(`Expr`, `Stmt`, `Block`, `Endblock`, `Arms`, `GrundArms`), each variant carrying the same
fields as the Lean constructor — **including the hypothesis fields**, as `Zeugnis` values:

| Lean hypothesis | Rust `Zeugnis` | how it is produced |
|---|---|---|
| a range fact (`0 ≤ l1`, `1 ≤ l2`, `lo' ≤ lo`, `hi + n ≤ count`, `h1 < 2^w`, `1 ≤ l2 ∨ h2 ≤ −1`) | `Zeugnis::Bereich(lhs, rhs)` | integer arithmetic on declared ranges (today's `M104` lattice, unchanged) |
| a guard (`darf D t Λ`, `gdarf D g Λ`) | `Zeugnis::Waechter(t, Λ)` | Λ is computed per site (§1.2) and `braucht t` is looked up; the check is list containment |
| a write right (`V.schreibt t = true`) | `Zeugnis::Recht(t)` | lookup in the enclosing signature's `effects` |
| the rank (`∀ M, held M ∈ Λ → rang M < rang L`) | `Zeugnis::Rang(L, Λ)` | comparison over the held part of Λ |
| linear balance at `return` (`Λ.Perm V.ende`) | `Zeugnis::Bilanz(Λ, ende)` | multiset equality |
| a call's fit (`RufPasst`: writes ⊆, consumes ⊆ Λ, `Held` exact) | `Zeugnis::Ruf(S, Λ)` | three list checks; the `Held` one is **both directions** («SG-20») |
| a declaration fact (`D.tabNr n = some t`, `D.sig f = n`, `D.erlaubt t f von nach`, `D.spiegel r = some m`, `payload = D.nutzlast g`, `D.typ t f = int 0 255`, class readable/writable, `a + 1 < stufen m`) | `Zeugnis::Erklaert(…)` | lookup |
| a mark in hand (`Res.marke m a ∈ Λ`) | `Zeugnis::Marke(m, a, Λ)` | containment |
| the loop flag (`l = true`) | structural | `leave`/`next` are only parsed under a loop |

**Every `Zeugnis` is checkable in isolation**, and that is what makes the derivation
different from a pass: a pass decides a program; a `Zeugnis` decides one hypothesis at one
site, and the set of hypotheses is the constructor list of `Syntax.lean`, not a rule set
somebody maintains.

### 1.2 The resource context Λ

Λ is not written; it is computed, exactly as `SYNTAX.md` §7 says:

```
Λ at the head of a body      = Held of the signature + consumed marks at their stage
Λ after f(…)                 = (Λ − consumes(f)) + allocs(f)          (nachSig)
Λ inside locks L { … }       = Λ + Held(L);   after the block: Λ
Λ after advances a -> b      = Λ − marke(m,a) + marke(m,b)
Λ after retires              = Λ − marke(m,s)
Λ after any other statement  = Λ
Λ at return                  = must be ≡ Held of the signature + allocs (multiset)
```

One function, `lambda_nach(stmt, Λ) -> Λ'`, the Rust twin of the Λ' index of each `Stmt`
constructor. The invariant `Stmt.held_iff` of `Satz.lean` — a statement never creates or loses
a `Held` — is a unit test of that function over every constructor.

### 1.3 The derivation printed as Lean — the acceptance test that cannot lie

`Ableitung` has a printer to Lean source:

```
$ gabbro ableite beispiele/01-capspace.gab --lean > /tmp/01.lean
$ cd grammatik && lake env lean /tmp/01.lean
```

The printed file declares the program's `Deklaration` (tables, locks, signatures, …) and its
`Programm` (bodies as terms of `Syntax.lean`), with every hypothesis discharged by `decide`,
`rfl`, `by simp`, or `by omega`. **Lean accepting the file is the statement that the program
is a sentence of the grammar.** A `Zeugnis` the Rust side got wrong is a Lean error at the
line of the constructor. This is the seam `W16` of `PLAN-SICHERHEIT.md` — checker versus
theorem — closed by construction: there is no second judgment to compare, the checker's
output is the theorem's input.

*Measurement:* the 70 clean examples of `beispiele/`, one row each: `derives` / `refused at
«SG-n»` / `Lean rejects the print` — the third column must be empty, and while it is not, the
finding is in `gabbro-ableitung`, never in Lean.

### 1.4 The pass rules, mapped

Every rule of the twelve passes is either a hypothesis of a constructor, a declaration
fact, or outside the grammar. `instrumente/pruefe-deckung.py` grows a third column and turns
red when a rule maps to nothing:

| pass family | rule → hypothesis |
|---|---|
| **M1** (`M102`–`M104`, `M137`) | `Expr.div/rem` (`0 ≤ l1`, `1 ≤ l2`), `sdiv/srem` (divisor excludes 0), `weiter` (`lo' ≤ lo ∧ hi ≤ hi'`), `bor/bxor` (`h < 2^w`), `slot` (`i : index into T`), `narrow` (an `Endblock`), `leseBytes` (`hi + n ≤ count`) |
| **M2** (linearity, `O001`–`O012`) | the Λ index; `ret` (`Λ.Perm ende`); `call` (`Untermulti`); `advances` (`marke m a ∈ Λ`, `a+1 < stufen`); `retires` (`marke m s ∈ Λ`, assumption named) |
| **M3** (`R002`–`R004`) | `Expr.durch`/`Stmt.assignDurch` (`.ptr n true` for a write; guards of the carrier); `own` = `owner` mark; alias is harmless in one world (`exec_rahmen` holds for every alias) |
| **M4** (loops, `S003`–`S005`, `M133`) | `traverse` over `alleIndizes`, `retry n`, `forever a` (assumption mandatory), `invariant` → `logik schleife` |
| **H** (locks, `H005`–`H012`) | `darf`/`gdarf` on every access; `locks L hr`; `RufPasst.hh` exact («SG-20»); `observes` = `locks` on an RCU lock; `H009`–`H012` as `braucht` lists |
| **E** (effects) | `V.schreibt t = true` on every store; `RufPasst.hw/hg`; `axiomCall hw hg` |
| **V** (`V001`–`V004`, `V006`/`V007` «SG-23») | `publish hp`, `awaits hp` (`payload = nutzlast g`); the ORDER — payload writes directly before `publishes`, payload reads directly after `awaits` — is a sequence check on the statement list, same class as `H102` |
| **K** («SG-22») | `deadline n ops arch X falsifier p`: the `ops` number held like `costs`, `X` against a declared `arch`, the falsifier existing like `progress`/`S003`; the outcome rides the `fortschritt` row of §2.1 — no second budget, no new check |
| **D** («SG-24») | `count k in slots of T : p` desugars to the generated count function of `T` (a `D.Fn` with `requires`, like `ops insert/remove`); the predicate `p` is the writer's logic |
| **R** (registers, `R005`–`R011`) | `regLies hk` (readable), `regSchreib hk` (writable), `regLiesElse` (fallible read), `transition hm hl` (mirror declared and readable); `rzusage` → `hardware (geraet r)` |
| **D** (`D010`–`D013`) | `breaking i` (name in the term), `ops` as generated `Fn` with `requires`, `occupied` in the generated `requires` |
| **U** (`U003`, `U005`–`U007`) | `invarianten_gehalten` (a declaration rule), `keine_verklemmung` (ranks), `schuldet` at every `return` |
| **T** (`T001`–`T003`) | `reaches t f hf` (`typ t f = opt (count t)`) |
| **N**, **K**, **G**, **A** (names, costs, gates, `arch`) | declaration-level or outside (cost model, build gate) — unchanged passes; `K008`/`K009` become the `decreases` parameter (`fuel`) |
| **H013**/**H102** (contexts) | `shared` («SG-21») and `maskiert` as declarations; the reachability computation stays a pass that PRODUCES the `shared` marks (or checks the ones written) |

### 1.5 Sugar

Every `SUGAR` mark of `SYNTAX.md` is a definition in `Zucker.lean`; `gabbro-ableitung`
desugars by **calling the same definitions** — i.e. the Rust twin of `Zucker.lean` builds the
core term the Lean definition builds, and the Lean print (§1.3) uses the Lean definition by
name, so that Lean checks the desugaring as well. A sugar with no twin in `Zucker.lean` is a
finding: either the sugar is new (add the definition) or it was never sugar (add the
constructor).

### 1.6 Refusals

A refusal names the constructor and the hypothesis: *"`assignSlot` at line 40: `writes
CapSpace` is not in the contract of `delete_leaf`"*. The old codes stay as **aliases** (`E001`
→ `assignSlot.hw`), so the poison corpus keeps its expectations; a code with no constructor
behind it is retired with a note — the list of retired codes is a measurement of how much of
the old checker was a rule about nothing.

---

## 2. The emitter — preserving `exec`

### 2.1 One lowering per constructor

The emitter takes the `Ableitung`, not the AST. Each constructor has one C pattern, and the
pattern's correctness is the claim *"this C does what the `exec` clause does"*. The table
that matters is the one for the outcomes:

| Lean outcome | in the shipping build | under `TESTBUILD` |
|---|---|---|
| `logik (vorbedingung f)` | an obligation in `gabbro pflichten` (the ghost theory proves `requires` at every call) | `if (!(requires)) gabbro_logik(VORBEDINGUNG, "f")` at the call |
| `logik (nachbedingung f)` | obligation | check at `return` (with `old(…)` values saved at entry) |
| `logik (invariante i)` | obligation for every function that `schuldet i` | check at `return` of every such function |
| `logik schleife` | obligation | check at every pass boundary |
| `logik (abstieg f)` | obligation (`K008`/`K009` necessary condition; the measure is the ghost theory's) | a depth counter per recursive function, `gabbro_logik(ABSTIEG)` at the declared bound |
| `logik uebergang` | obligation | `if (field != von) gabbro_logik(UEBERGANG)` before the store |
| `hardware (annahme a)` | **runtime**: the foreign body's result is held against its declared type; a miss is `gabbro_hardware(ANNAHME, "a")` — this is `einpassen` as C | same |
| `hardware (fortschritt a)` | **assume `a`** with its falsifier — no check possible (the environment ends the loop or not); the watchdog IS the falsifier | a pass counter, `gabbro_hardware(FORTSCHRITT, "a")` at the `passes` bound |
| `hardware ieee` | **runtime**: `isfinite(x) && lo <= x && x <= hi` after every float operation; a miss is `gabbro_hardware(IEEE)` — this is `gleitPasst` as C | same |
| `hardware (register r)` | **runtime**: the raw read held against the register's type (`einpassen`) | same |
| `hardware (geraet r)` | **runtime**: the raw read held against `rzusage r` — the device's promise | same |
| `hardware (sichtbarkeit A10)` | **assume A10** with its falsifier: an `awaits` is the acquire-load the memory order names; whether the payload is visible cannot be checked in C without a second reading | the trace (§2.3) can check the pairing on a recording |

`gabbro_hardware` and `gabbro_logik` are the two exits of the runtime, and the runtime has no
third one — the C twin of `zwei_fehler`. What each does (halt, log, jump to a handler) is a
configuration of the runtime, not of the language.

### 2.2 The locks, the marks, the traces

* `locks L { … }` → the lock primitive's acquire/release. The primitive is a foreign body;
  its mutual exclusion is **W3** of `Wettlauf.lean` and is booked as `assume lock_exclusive
  falsifier probe_lock` — the probe is the trace check of §2.3.
* Marks and Λ have no runtime: they are erased. Their correctness is the derivation (§1).
* `shared` carriers and `atomic` globals decide the memory order of the emitted access:
  guarded accesses are plain loads/stores (ordered by the lock's acquire/release), `atomic`
  accesses carry the declared order. `kein_wettlauf_global` says these are the only two
  kinds of shared access.

### 2.3 The trace, recorded — `TESTBUILD` as the theorem's probe

Under `TESTBUILD` the emitter can write the events of `Semantik.lean`'s `Ereignis` into a
per-thread ring buffer: `zugriff(t, w, Λ-id, held)`, `nimmt(L, held)`, `gibt(L)`. A tool
`gabbro spur` reads the buffers and checks `Gesittet` — (W1) consistency, (W2) every event
gut (the derivation guarantees this; the check is a self-test of the emitter), (W3)
exclusion at every `nimmt`, (W5) unshared carriers touched by one thread. **(W3) failing is
the falsifier of `assume lock_exclusive`; (W5) failing is a `shared` mark missing — a
declaration error found at run time.** This is not a race detector by heuristics; it is the
premise of `kein_wettlauf`, checked on a recording, and a recording that passes is a run the
theorem covers.

### 2.4 Differential test against the meaning

For a set of small programs (the speech tests of `Satz.lean` §4 first, then corpus programs
without devices), `Semantik.lean`'s `exec` is run by Lean (`#eval` over the printed
derivation with a concrete `World` and `Orakel`), the emitted C is run on the same world,
and the outcomes and final worlds are compared. A difference is an emitter bug or a
`Semantik.lean` bug; either is a finding, and the tool that finds it costs one script.

---

## 3. Guardians and ratchets

| guardian | reads | red when |
|---|---|---|
| `pruefe-grammatik.sh` | `grammatik/`: `lake build`, `grep sorry`, `#print axioms` | a `sorry`, a `sorryAx`, a new axiom |
| the constructor ratchet | `Ausgang` = 7, `Logik` = 6, `Hardware` = 6, `Ereignis` = 4 | a count rises without a row in `SYNTAX.md` §16.1 |
| `pruefe-deckung.py` (extended) | every pass rule → a constructor hypothesis, a declaration fact, or "outside" | a rule maps to nothing |
| `pruefe-ableitung.sh` | every `.gab` in `beispiele/`: derive, print, `lake env lean` | Lean rejects a print (§1.3) |
| `pruefe-zucker.py` | every `SUGAR` mark in `SYNTAX.md` names a definition in `Zucker.lean` | a mark without a twin |
| `vergleiche-bedeutung.sh` | §2.4 | an outcome differs |
| `gabbro spur` | §2.3 | `Gesittet` fails on a recording |

---

## 4. The steps, in order, and what each is measured by

**U1 — the guardians of `SYNTAX.md` and `grammatik/`.** `pruefe-syntax.sh`,
`zaehle-wortschatz.py` (222), `pruefe-grammatiktafel.py`, `pruefe-grammatik.sh` (new, cheap).
*Measured by:* all green; the hand counts in `SYNTAX.md` "State" replaced by the guardians'.

**U2 — `gabbro-ableitung`, expressions and Λ.** `Expr` and the Λ computation; the Lean
printer for expressions. *Measured by:* every expression of the 70 clean examples prints and
typechecks; `Stmt.held_iff` as a unit test of `lambda_nach`.

**U3 — statements, blocks, signatures.** The rest of the families; `RufPasst` with the exact
`Held`; `Endblock`; the sugar twins (§1.5). *Measured by:* the corpus table of §1.3 — the
third column empty; the refusals are the moves `SYNTAX.md` §17 predicts and nothing else,
or each surplus refusal is a finding with a rule name.

**U4 — the corpus moves.** `66` gets `progress`; `state` writes become `transition … : A ->
B;`; callees name their full `Held`; `shared` where `H013` finds two contexts; signed
divisions get `sdiv`'s range or a `narrow`. *Measured by:* U3's table all `derives`.

**U5 — the emitter on the derivation.** One lowering per constructor; the two runtime exits;
the twelve outcome sites of §2.1. *Measured by:* `vergleiche-binaerprogramme.py` over the 539
`.gab` — the emitted C of programs that derive is byte-identical to today's except at the
sites §2.1 adds (float checks, register checks, promise checks), and those sites are counted.

**U6 — `TESTBUILD` checks and the trace.** `gabbro_logik` sites; the ring buffer; `gabbro
spur`. *Measured by:* §2.3 green on the corpus's own tests; one deliberately broken lock (a
`beispiele/gift/` file with a hand-written unguarded access under `raw`) turns it red.

**U7 — the differential test.** §2.4 on the speech tests and ten corpus programs.
*Measured by:* zero differences, or a named bug.

**U8 — retire the passes.** Every pass rule mapped in §1.4 to a hypothesis is deleted from
`gabbro-check`; what remains is the declaration checks (names, `arch`, gates, costs, `H013`,
`H102`) and the front end. *Measured by:* `pruefe-deckung.py` — no rule left that a
constructor covers; the poison corpus verdicts unchanged (through the aliases of §1.6).

**Order:** U1 → U2 → U3 → U4 → U5 → U7 → U6 → U8. U6 is independent of U7. *No day
estimates* (W7).

---

## 5. What stays outside — and that it is the same list as `SYNTAX.md` §16.2 (7)–(9)

* **When a handler runs.** `entry … dispatch`, `via idt`, `masks irqs`: the trace model can
  represent a handler as a thread, and `maskiert` is in the declaration; `H102` stays a pass
  over the declaration, because the grammar of one body cannot say what interrupts it.
* **The cost model.** `costs`, `held <=`, `bounded n ops` as ops: the emitter's arithmetic
  over its own C; `K001`–`K009` stay passes.
* **The C compiler and the machine.** `cc` and the CPU are the last two foreign bodies;
  `PLAN-SICHERHEIT.md` §3 says what the emitter's own proof would have to be.

With U1–U8 done, a Gabbro program that the checker accepts is a term Lean accepts, the C it
becomes does what `exec` does or stops at one of twelve named sites, six of which are the
writer's clauses and six of which are assumptions with a falsifier — and a recording of its
run under `TESTBUILD` is a witness that the run is one the theorem covers.
