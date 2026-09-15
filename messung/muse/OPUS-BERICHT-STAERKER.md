# OPUS lane `staerker` — the closing theorem's two remaining conditions

*2026-09-15. Task: make `schlusssatz` (`grammatik/Grammatik/Schlusssatz.lean`) STRONGER, not
wider, on the two items `PLAN-UEBERSETZUNGSVALIDIERUNG.md` §6.5 keeps open — (1) part 4's
condition "the Gabbro call ends in no model error", (2) the un-re-instantiated link between
part 4 (`rufAt`) and part 5 (machine G for one thread).*

## Files touched

| file | what |
|---|---|
| `grammatik/Grammatik/RufOhneHardware.lean` | **new** — the check `hardwareFrei`, its soundness, `rufAt_ohneHardware`, `rufAt_hardware_von_rumpf` |
| `grammatik/Grammatik/RufOhneHardwareZeuge.lean` | **new** — the witness program and the FINDING (`befund_hardware_bleibt`, `ohneHardware_zeuge`) |
| `grammatik/Grammatik/KorrOkAdaequat.lean` | **new** — `korrOk_endR`: every certified body is in the adequacy fragment |
| `grammatik/Grammatik/KorrespondenzAllg.lean` | §5 added: `korrOk_hardwareFrei`, `korrOk_rufAt_ohneHardware` (this file was reserved for the lane) |
| `grammatik/Grammatik/Schlusssatz.lean` | §2b (`rufAt_tor`, `rufAt_vorbedingung`); three new conclusions 4b/4c/4d; docstring and CUTS |
| `grammatik/Grammatik/Kette104Satz.lean` | `kette_104_ohne_hardware` (witness of the new clauses); one conjunct index moved |
| `grammatik/Grammatik/CParser/Bruecke.lean` | `schlusssatz_text` restates the conclusion — the three clauses added there too |
| `grammatik/Grammatik/Kette108.lean`, `grammatik/Grammatik/CText108.lean` | conjunct indices moved (no statement change) |
| `grammatik/Grammatik.lean` | three imports |
| `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` | §6.5 two items rewritten, new §6.8 |
| `dokumente/SATZKARTE.md` | new §35 |
| `messung/muse/OPUS-BERICHT-STAERKER.md` | this report |

**Not touched:** `Parser/`, the elaborator, `Typen.lean`, `Syntax.lean`, `Schlusssatz104.lean`,
`Schlusssatz124.lean`, `Zielsatz/`.

## Standards

- No `sorry`, no `admit`, no `native_decide`, no new `axiom`.
- `#print axioms` on every new theorem: `[propext, Classical.choice, Quot.sound]`, or the two
  purely computational ones `[propext, Quot.sound]` (`stOk0_hardwareFrei`,
  `stOkBl_hardwareFrei`, `enOk_hardwareFrei`, `korrOk_hardwareFrei`, `stOk0_stmtR`,
  `axOBoese_gut`, `axOBoese_vertrag`).
- `#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel`: `[propext, Classical.choice,
  Quot.sound]` — **unchanged**.
- Whole library on `ki-pc-fisch-101` (`gabbro-opus-str`): **257 jobs, green**.
- `instrumente/zaehle-kette.py --lean`, 113 programs: **(a) 2, (b) 15, (c) 15, (d) 60, (e) 2;
  CHAIN COUNT 2 of 113 — unchanged**, first stopping sieve (a) elab 91, (a) parse 20. It could
  not change: sieve (a) binds, and this lane touched no parser, no elaborator and no lowering.
- Witnesses: `befund_hardware_bleibt`, `ohneHardware_zeuge` (`RufOhneHardwareZeuge.lean`),
  `kette_104_ohne_hardware` (`Kette104Satz.lean`) — the last one non-degenerate: the call it
  exercises is `einzahlen(k, 0, 7)` from the zero state, which moves the slot `0 → 100`.
- `schlusssatz_104` and `schlusssatz_124`: **statements unchanged** (not edited at all).

---

## Item 1 — part 4's condition. Clause by clause: what disappeared, what remains

### The hypothesis text is unchanged; three conclusions were added

The honest answer first: **no hypothesis text disappeared, because part 4's condition is not a
hypothesis of the theorem — it is a hypothesis INSIDE part 4's conclusion**, under the
quantifiers `∀ passes n f k … σ st ρG vs ρ0`:

```
(rufAt K.E.P O passes n f σ ρG).istFehler = false →
```

Removing it from part 4 without replacement is only sound if it is DERIVABLE there, and it is
not — see "what remains" below. Weakening the conclusion to make it go away was ruled out by
the task and would have been wrong anyway. So the theorem was strengthened the only way that
is strictly stronger: **the same premises, the same parts 1–6 verbatim, plus three new
conjuncts** that say how much of that condition can never fail.

`schlusssatz`'s premise list before and after, character for character:

```
{src : String} (K : Kette src) (O) (hH : HardwareAnnahmen O K.E.Q)
(orc : DevOrc) (XR : CCallR) (hXR : XR.Funktional) (bin) (tief)
(hA1 : ∀ f st vs st' rv, bin f st vs st' rv → CallAt K.EL.lay orc XR (kProg K.zert) (tief f) (fnNr f) st vs st' rv)
(sp) (init) (hA4 : EinFadenStart K.E sp init)
```

— identical. `Kette` gained no field. The conclusion gained, between part 4 and part 5:

| clause | text | what it kills |
|---|---|---|
| **4b** | `∀ (passes n) f σ ρG e, rufAt K.E.P O passes n f σ ρG ≠ .hardware e` | the whole HARDWARE half of the condition, at every depth, every budget, every world, every argument list, against every oracle |
| **4c** | `(rufAt … n f σ ρG).istFehler = true → ∃ e : Logik _, rufAt … = .logik e` | names the residue: the writer's logic, alone |
| **4d** | `(rufAt … (n+1) f σ ρG).istFehler = false → ReqAmEintritt K.E.P f σ ρG` | says the condition is at least the caller's duty — the first thing it asks for |

So, clause by clause: of the two error classes the model has (`Semantik.lean`: "es gibt keinen
dritten"), **one is gone for every chain and the other is named**.

### Why the hardware half is a theorem

`Hardware` has exactly five producers in `execStmt`/`execBlock`, and every one is a syntactic
form:

| form | outcome |
|---|---|
| `Stmt.axiomCall`, `Block.bindAxiom` | `Hardware.annahme a` — the raw answer misses the declared result type |
| `Block.regLies` | `Hardware.register r` / `Hardware.geraet r` |
| `Block.regLiesElse` | `Hardware.register r` |
| `Block.awaits` | `Hardware.sichtbarkeit D.a10` (A10) |
| `Stmt.forever` | `Hardware.fortschritt a` (H2, budget out) |

`Hardware.ieee` is no longer produced at all (verdict F1, 2026-09-15).

`Stmt/Block/Endblock/Arms/GrundArms.hardwareFrei` refuses exactly those five and admits
everything else. `Endblock.hardwareFrei_ok` is the soundness — the twin of
`Endblock.logikFrei_ok` in `ZielOrtGanz.lean` — against any handler in `OhneHardware`. The
handler premise then **carries itself by induction on the DEPTH**: `rufAt`'s own error branches
are all `logik` (`abstieg` at `0`, `vorbedingung`, `nachbedingung`, `invariante`), so
`rufAt_ohneHardware` needs no premise about the oracle and none about the user's logic.

And `korrOk` refuses all five — they have no `GRow` at all — which `korrOk_hardwareFrei` reads
off the check by an induction on the same measure `stOkBl_sound` runs on. Hence
`korrOk_rufAt_ohneHardware`, which is clause 4b.

### THE FINDING: premise (c) does not do this work — witness program included

This is the first-order part. **The goal theorem's hardware premise does NOT rule out a
hardware outcome**, and the shape is exact:

> An **axiom call whose raw answer misses its declared result type**. `HardwareAnnahmen O Q` is
> `GutO O ∧ RegLokal O ∧ AxVertragO Q O`, and `AxVertragO Q O` reads
> `∀ a σ ρ v, einpassenErg O.zeiger (D.aerg a) (O.wirkt a σ ρ).2 = some v → Q a (O.wirkt a σ ρ).1 v = true`.
> It constrains the oracle only **where the answer fits**. An answer that does not fit satisfies
> it VACUOUSLY and stops the model at `Hardware.annahme`.

Built and proved (`RufOhneHardwareZeuge.lean`, `befund_hardware_bleibt`) on the existing
witness program `axP` (`AxiomVertrag.lean` — `zaehle` is `if true { let r = inc(); return r }
return 0`, `haupt` calls it):

- `programmImFragmentV axP axFs = true` and `fussOrtB axP axFs = true` — the checker's program
  facts hold;
- `∀ f, KoerperGutA axP 0 axQ f` — the user's duty, proved in the tree, **against every oracle
  in the premise class**, so against the bad one too;
- `HardwareAnnahmen axOBoese axQ` — `axOBoese` is `axO` with the raw answer `99` (outside
  `int 0 3`); `GutO` transfers verbatim (`GutO` speaks only about the answer WORLD, which is
  unchanged), `RegLokal` holds (`axD.Reg = Empty`), `AxVertragO` holds vacuously;
- and still `∀ passes n σ, rufAt axP axOBoese passes (n+1) zaehle σ .nil = .hardware (.annahme inc)`.

A second witness, `ohneHardware_zeuge`, shows the check is **per body and not per run**:
`haupt`'s own body is `hardwareFrei = true`, and its call still ends `.hardware` — through
`zaehle`. That is exactly why `Endblock.hardwareFrei_ok` takes `OhneHardware R` and why
`rufAt_ohneHardware` asks the check of every body.

### What remains, and WHY — the second finding

The residue is the `logik` class: `vorbedingung`, `nachbedingung`, `invariante`, `abstieg`,
and the body-own `schleife` (a `traverse` invariant — `traverse` IS inside `korrOk`),
`vorzustand`, `bereich`.

**The user's duty does cover every one of the body-own ones** — `KoerperGutS`'s second clause
is "the body ends in no `logik` outcome" and its first clause is the caller duty. The obstacle
is not the content of the obligation but **the handler class it is quantified over**:

```
KoerperGutS P passes Q S f :=
  (… ∀ R, RespektiertRahmen P R → OhneVorbedingung R → … ) ∧
  (… ∀ R, RespektiertRahmen P R → OhneLogik R       → … )
```

and `rufAt` — the very handler part 4 speaks about — **is in neither class**, measured against
the definitions:

| class member | why `rufAt P O passes m` fails it |
|---|---|
| `OhneVorbedingung R` | `rufAt (m+1) g σ ρ = .logik (.vorbedingung g)` at every key whose `requires` is false (`rufAt_vorbedingung`, proved in this lane) |
| `OhneLogik R` | `rufAt 0 g σ ρ = .logik (.abstieg g)` — always |
| `RespektiertRahmen P R` | its frame half is `∀ f σ ρ σ' v, R f σ ρ = .ok σ' v → Rahmen … σ σ'` at EVERY world; `rufAt_gut` (`Satz.lean`) gives `GutR (rufAt …)` only at worlds with `HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt` |

Patching `rufAt` into the class (gate the bad keys, map `abstieg` to a non-`logik` default —
the trick `rufAusL` already uses in `ZielOrtGanz.lean`) gives a handler `R` that IS in the
class, but then the body run one wants to reason about is `execEnd … (rufAt m) body` and the
one the obligation speaks about is `execEnd … R body`. **Relating them is the one missing
lemma**, and it is missing from the whole tree:

> **A congruence of `execStmt`/`execBlock`/`execEnd` in the handler.** If two handlers answer,
> at every key, either the same outcome or two ERROR outcomes related by some relation `Er` on
> error tags, then the two body runs are either equal or two error outcomes related by `Er`.
> It holds because every error outcome propagates through every constructor verbatim, with its
> tag — `.logik`/`.hardware` are treated identically by `schrumpf`, `mapWelt`, `zuAusgang`,
> `schrumpfArm`, `traverseLauf`, `retryLauf`, `foreverLauf` and every `match` in the semantics.

I did **not** build it. Scope, measured against the comparable `Endblock.logikFrei_ok` and
`Endblock.hardwareFrei_ok` mutuals (≈230 and ≈250 lines): **400–500 lines** over ~50 `Stmt`
constructors, ~18 `Block` constructors, 6 `Endblock`, `Arms`/`GrundArms` and the three loop
combinators. It is worth doing because it unlocks **three** open items at once:

1. the `logik` half of part 4's condition (with `KoerperGutS` clauses 1 and 2 and
   `InvGutS`, the residue shrinks to `abstieg` alone);
2. **depth monotonicity** of `rufAt` — "an outcome that is not an `abstieg` is the outcome at
   every larger depth" — which turns the `abstieg` residue into a single computation a chain
   author already performs;
3. the first half of a `rufAt` ↔ `rufRumpf` bridge, which is item 2 below.

**And one part of the residue is NOT a defect and should be read as a sharpening.** Part 4
quantifies over ANY Gabbro world `σ` and ANY arguments `ρG`. `rufAt`'s first act is the
`requires` test, so for any callee with a non-trivial `requires` the condition is false at most
of them — and clause 4d now says this in the theorem: the condition IMPLIES `ReqAmEintritt`.
The condition is stated on the COMPUTATION where the CONTRACT would do; making that visible is
half the repair.

---

## Item 2 — the link between part 4 (`rufAt`) and part 5 (machine G)

**It cannot be brought in today, and the reason is not cost.** Measured:

### Cost, with numbers

`RufAdaequatRufG.lean` (the adequacy chain) is **already in `Schlusssatz.lean`'s transitive
import closure** (97 modules; `RufAdaequatRufG`, `RufAdaequatG`, `RufUmkehrRufG` and
`ZielOrtEinfaden` are all in it). Bringing the theorem in costs **no new import**.

Single-file builds on `ki-pc-fisch-101`, `lean` with the warm `LEAN_PATH` (wall clock, peak RSS
via `/usr/bin/time -f "%e %M"`):

| file | time | peak RSS |
|---|---|---|
| `RufAdaequatG.lean` | 47,8 s | 2,29 GB |
| `RufAdaequatRufG.lean` | 19,3 s | 1,69 GB |
| `KorrespondenzAllg.lean` (after this lane) | 18,8 s | 3,76 GB |
| `RufOhneHardware.lean` (new) | 23,5 s | 0,89 GB |
| `KorrOkAdaequat.lean` (new) | 5,9 s | 0,91 GB |
| `Schlusssatz.lean` | 0,4 s | 0,75 GB |

Whole library, warm `.lake`: **257 jobs, 20,7 s wall** after the change (255 jobs before the
two witness files were added).

### What actually stands in the way — four things, and one of them is now closed

1. **The fragment — CLOSED by this lane.** `korrOk_endR` (`KorrOkAdaequat.lean`): every body a
   correspondence certificate accepts is in the adequacy fragment `EndR`/`BlockR`/`StmtR`, for
   **every** lock class `A` and with the callee predicate taken as `True`. So the fragment is
   not the obstacle, and a later lane may say so with a theorem instead of a reading.
2. **`rufG_adaequat_ruf` realises `rufRumpf`, not `rufAt`.** `rufRumpf` runs the callee's body
   and checks nothing; `rufAt` also tests `requires`, `ensures` and the owed invariants **and
   READS their carriers** — `σ.lese (Signatur.anfang …) (P.requires f).orte` at entry,
   `σ'.lese (vertragVon D f).ende (P.ensures f).orte` at the return, one `lese` per owed
   invariant (`Semantik.lean`, `rufAt`). Machine G records none of those reads. So wherever a
   contract reads a carrier, the two outcomes agree on memory and **differ on the TRACE** —
   and the trace is what `SpurInv` and race freedom are about. The tree already books this:
   `RufAdaequatRufG.lean` §13, `befund_vertrag`, "G agrees with `exec` only where every
   contract holds *and reads nothing*".
3. **`Tief P A n` admits callees BY DEPTH** — the same `abstieg` residue part 4's condition
   carries, so item 2 cannot close before item 1 does.
4. **The adequacy is EXISTENTIAL and machine-shaped.** It gives SOME thread-`f` run realising
   the outcome, about a machine where thread `f` already stands on the body with a non-waiting
   caller frame (`hM`, `hnw : caller.wartend = false`, `hΛ : HeldGenau Λ (offen spur)`,
   `hfrei : ∀ L, A L → RufFreiG M f L`). Part 5 is UNIVERSAL over machines reachable from the
   single-threaded start, and nothing in a chain says a reachable machine has that shape. The
   universal converse exists only for the loop-free, error-channel-free part
   (`RufUmkehrRufG.lean`).

**So items 1 and 2 are one item**, and the order is forced: the congruence lemma, then
`rufAt` ↔ `rufRumpf` up to the contract reads, then the machine-shape side conditions. Nothing
in the theorem was changed for item 2 beyond naming these four in the CUTS — a hypothesis that
is not provable is not brought in.

---

## What a reviewer should check

- `git diff master -- grammatik/Grammatik/Schlusssatz.lean` — the premise list is untouched;
  the only conclusion change is three new conjuncts inserted after part 4.
- The three index moves (`Kette108.lean:307`, `CText108.lean:158`, `Kette104Satz.lean:276`)
  are conjunct positions only: parts 5 and 6 moved right by three `.2`s.
- `schlusssatz_text` (`CParser/Bruecke.lean`) restates `schlusssatz`'s conclusion, so the three
  clauses had to be added there as well; its proof is still the one-liner `schlusssatz K …`.
- No emission counter, no diagnostic code, no corpus file, no gift number was touched.
