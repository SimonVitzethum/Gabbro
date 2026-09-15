# OPUS lane `kongruenz` — the congruence of `execEnd` in its handler, and what it buys

*2026-09-15. Task: build the ONE lemma two open items of `PLAN-UEBERSETZUNGSVALIDIERUNG.md`
§6.5 wait on — a congruence of `execEnd` in its handler — state it before proving it, prove
it, and USE it on part 4's remaining `logik` condition.*

## Files touched

| file | what |
|---|---|
| `grammatik/Grammatik/HandlerKongruenz.lean` | **new**, 623 lines — `Fehlermarke`, `RufUnter`/`AusgangUnter`/`EndUnter`, `HandlerUnter`, the three loop combinators, the mutual congruence over `Stmt`/`Block`/`Endblock`/`Arms`/`GrundArms`, and `rufSchritt`/`rufAt_succ_eq`/`rufSchritt_kongruent` |
| `grammatik/Grammatik/RufTiefe.lean` | **new**, 89 lines — consumer 1: `rufAt_tiefer`, `rufAt_stabil`, `rufAt_stabil_ab` |
| `grammatik/Grammatik/RufLogik.lean` | **new**, 455 lines — consumer 2: `eval_spurfrei`, `req_lese`, `rufSchritt_nicht_logik`, `rufFrei`, the three congruence instances, `rufAt_vertraege`, `RufRahmenTreu`, `rufAt_nurAbstieg`, `rufRahmenTreu_ohneSperren` |
| `grammatik/Grammatik/KorrOkOhneLocks.lean` | **new**, 183 lines — `korrOk_ohneLocks`, the twin of `korrOk_hardwareFrei`, read off the SAME check (kept out of `KorrespondenzAllg.lean`, which another lane holds) |
| `grammatik/Grammatik/RufLogikZeuge.lean` | **new**, 73 lines — the two witnesses |
| `grammatik/Grammatik/Schlusssatz.lean` | clause **4e** (two halves) between 4d and part 5; docstring; CUTS rewritten |
| `grammatik/Grammatik/CParser/Bruecke.lean` | `schlusssatz_text` restates the conclusion — 4e added there too |
| `grammatik/Grammatik/Kette108.lean`, `CText108.lean`, `Kette104Satz.lean` | one conjunct index each (parts 5 and 6 moved right by one `.2`) |
| `grammatik/Grammatik.lean` | five imports |
| `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` | §6.5 bullet rewritten, new §6.9 |
| `dokumente/SATZKARTE.md` | new §36 |
| `messung/muse/OPUS-BERICHT-KONGRUENZ.md` | this report |

**Not touched:** `Semantik.lean`, `Fehler.lean` (they were mine for the lane and needed no
change — see "what did not have to move"), `KorrespondenzAllg.lean` and the C-form files
(the other Opus lane), `Parser/`, `m1.rs`, `saetze.rs`, `Zielsatz/`, `Schlusssatz104.lean`,
`Schlusssatz124.lean`, any corpus file, any diagnostic code, any emission counter.

## Standards

- No `sorry`, no `admit`, no `native_decide`, no new `axiom` (grep-checked over the diff).
- `#print axioms` on every new theorem: `[propext, Classical.choice, Quot.sound]`, except
  the two purely computational ones `enOk_ohneLocks` and `korrOk_ohneLocks`
  (`[propext, Quot.sound]`).
- `#print axioms Gabbro.Grammatik.Zielsatz.gabbro_ziel`: `[propext, Classical.choice,
  Quot.sound]` — **unchanged**.
- `schlusssatz_104`, `schlusssatz_124`: **not edited**; statements unchanged.
- `schlusssatz`: premise list unchanged character for character; ONE conjunct added to the
  conclusion. Strictly stronger.

## Build cost, measured on `ki-pc-fisch-101` (`gabbro-opus-kong`)

| what | before the lane | after |
|---|---|---|
| whole library, COLD (`.lake` re-seeded from `stage/lake3`) | 257 jobs, **189 s** wall | 262 jobs, **153 s** wall, **6,67 GB** peak RSS |
| whole library, warm no-op | — | 262 jobs, 20 s, 3,06 GB |

*(The two cold numbers are on the same machine under the 6-slot queue and different
neighbours; the honest reading is "the lane did not move the build out of its band" —
OFFEN O13's figure is ~5 min at 6,5 GB.)*

Single-file, warm `LEAN_PATH`, `/usr/bin/time -f "%e s %M KB"`:

| file | time | peak RSS |
|---|---|---|
| `HandlerKongruenz.lean` | 12,97 s | 0,74 GB |
| `KorrOkOhneLocks.lean` | 4,40 s | 0,95 GB |
| `RufLogikZeuge.lean` | 0,38 s | 0,77 GB |
| `Schlusssatz.lean` | 0,37 s | 0,75 GB |
| `RufLogik.lean` | 0,27 s | 0,66 GB |
| `RufTiefe.lean` | 0,16 s | 0,50 GB |

The congruence is the whole cost, and it is 13 s. The report that sized it at 400–500 lines
over ~50 `Stmt`, ~18 `Block` and 6 `Endblock` constructors plus the three loop combinators
was right about the shape; the file came out at 623 lines with the docstring, the mark
algebra and the `rufSchritt` section.

---

## 1. THE LEMMA, stated before it was proved

### 1.1 The statement

A **`Fehlermarke D`** is a `Logik D` or a `Hardware D` payload — the one thing `Ausgang`,
`EndAusgang` and `RufAusgang` share, since each has exactly those two error constructors
("es gibt keinen dritten", `Semantik.lean`). `m.zuRuf`, `m.zuAusgang`, `m.zuEnd` put a mark
back into each of the three types.

```lean
def HandlerUnter (Er : Fehlermarke D → Prop) (R₁ R₂ : Handler) : Prop :=
  ∀ g σ ρ, R₁ g σ ρ = R₂ g σ ρ ∨ ∃ m, R₁ g σ ρ = m.zuRuf ∧ Er m

theorem Endblock.kongruent (hR : HandlerUnter Er R₁ R₂) (b : Endblock D V l Γ Λ) (σ ρ) :
    execEnd O passes R₁ b σ ρ = execEnd O passes R₂ b σ ρ ∨
      ∃ m, execEnd O passes R₁ b σ ρ = m.zuEnd ∧ Er m
```

and the same for `execStmt`, `execBlock`, `execArms`, `execGrund` (one mutual block), plus
`traverseLauf_kongruent`, `retryLauf_kongruent`, `foreverLauf_kongruent` beside it.

In words: **`R₁` is `R₂` except that it may FAIL EARLY, and only in the named way; then a
body run under `R₁` is the body run under `R₂`, except that it may fail early, and only in
the same named way.**

**Side conditions: none.** Not on the oracle, not on the program, not on the user's logic,
not on worlds or traces. The lemma is about propagation alone: no constructor of the
semantics CATCHES an error (`bindCallElse` catches a REASON, which is not an error), so an
error mark travels verbatim through `schrumpf`, `schrumpfArm`, `mapWelt`, `zuAusgang`, the
three loop combinators and every `match`.

### 1.2 Why ONE-SIDED, and why that is the load-bearing decision

The report that asked for this lemma described it symmetrically: *"if two handlers answer,
at every key, either the same outcome or two ERROR outcomes related by some relation `Er`,
then the two body runs are either equal or two error outcomes related by `Er`."* I built
that version first — it compiles — and then **threw it away**, because it fails the first
consumer:

> **Depth monotonicity.** `rufAt n` and `rufAt (n+1)` differ exactly where the shallower
> call ran out of depth. There `rufAt n` answers `logik (abstieg g)` — and `rufAt (n+1)`
> may answer **`ok`**. The deeper call SUCCEEDS where the shallower one failed. A symmetric
> premise ("both are errors") has nothing to stand on.

This is exactly the failure mode the task named: *a lemma whose statement is chosen to be
provable rather than to be useful*. The symmetric version is provable and useless for
consumer 1. Checked against **both** consumers before building:

| consumer | `R₁` | `R₂` | `Er` | symmetric form? |
|---|---|---|---|---|
| depth (clause 4e(i)) | `rufAt n` | `rufAt (n+1)` | an `abstieg` mark | **no** — `R₂` need not err |
| `logik` half (4e(ii)) | `rufAt n` | `torRuf P (rufFrei n)` | an `abstieg` mark | yes, but the extra information about `R₂` is never used |

So the one-sided form serves both and the symmetric one serves one. And nothing is lost: the
symmetric statement follows from two instances of the one-sided one, in the two directions,
wherever it holds.

### 1.3 The other thing the statement had to get right

`rufAt P O passes (n+1)` is one entry-contract test, one body run against
`rufAt P O passes n`, one exit-contract test and the owed-invariant test. That is `rfl`:

```lean
def rufSchritt (P O passes) (R : Handler) (f σ ρ) : RufAusgang f := …   -- rufAt's body, R abstract
theorem rufAt_succ_eq : rufAt P O passes (n + 1) = rufSchritt P O passes (rufAt P O passes n) := rfl
theorem rufSchritt_kongruent (hR : HandlerUnter Er R₁ R₂) (P O passes f σ ρ) :
    RufUnter Er (rufSchritt P O passes R₁ f σ ρ) (rufSchritt P O passes R₂ f σ ρ)
```

Without `rufSchritt` the depth induction fights the unfolder: `simp only [rufAt]` unfolds the
INNER `rufAt (m+1)` as well, and the two sides stop being the same text. This cost one build
round and is worth recording: *a recursive definition with a handler parameter needs the
step named, or its induction is about a term nobody wrote.*

---

## 2. CONSUMER 1 — depth monotonicity, with no side condition

```lean
theorem rufAt_tiefer (P O passes) :
    ∀ n, HandlerUnter AbstiegMarke (rufAt P O passes n) (rufAt P O passes (n + 1))
theorem rufAt_stabil_ab (P O passes n f σ ρ)
    (h : ∀ g, rufAt P O passes n f σ ρ ≠ .logik (.abstieg g)) :
    ∀ k, rufAt P O passes (n + k) f σ ρ = rufAt P O passes n f σ ρ
```

No premise on the oracle, the program or the user. **What it buys the closing theorem**:
part 4's condition `(rufAt … n f σ ρG).istFehler = false`, once met at ONE depth by an
outcome that is not an `abstieg`, is met at EVERY larger depth **by the same outcome**. A
chain author computes at one depth and is done; the depth number stops being a promise and
becomes a computation. That is clause 4e(i).

## 3. CONSUMER 2 — part 4's `logik` condition. Clause by clause

### 3.1 The route

Three instances of the same lemma, and one induction on the depth.

1. **`rufFrei P O passes n`** — `rufAt` with every `logik` answer replaced by the hardware
   default `.hardware .ieee` (the trick `rufAusL` already uses in `ZielOrtGanz.lean`: a
   default that is neither `ok`, so no frame or contract duty attaches, nor `logik`, so the
   handler IS in `OhneLogik` and in `OhneVorbedingung`).
2. **`torRuf P (rufFrei …)`** — the gate `KoerperGutS` clause 1 is stated against.
3. The depth induction with hypothesis `NurAbstieg P O passes m`: at an entry meeting the
   callee's `requires`, `rufAt`'s only `logik` outcome is an `abstieg`.
   * `HandlerUnter AbstiegMarke (rufAt m) (torRuf P (rufFrei m))` — where `requires` holds
     the two agree unless `rufAt` answered a `logik`, and there the induction hypothesis
     says it is an `abstieg`; where `requires` fails they are EQUAL for `m = k+1` (both
     `logik (vorbedingung g)`) and the mark is an `abstieg` for `m = 0`.
   * `HandlerUnter VorbedMarke (torRuf P (rufFrei m)) (rufFrei m)` — they differ only where
     `requires` fails, and there the gate answers `vorbedingung`.
   * The caller duty (`KoerperGutS` clause 1, second half) kills that difference, so the
     gated body run IS the patched body run; then clause 1's triple, clause 2 and `InvGutS`
     apply to it, and `rufSchritt_nicht_logik` assembles them.

### 3.2 What disappeared from the condition, and what remains

| error kind | before this lane | after |
|---|---|---|
| `Hardware.annahme` / `.register` / `.geraet` / `.sichtbarkeit` / `.fortschritt` | discharged 2026-09-15 (clause 4b) | discharged |
| `Logik.vorbedingung` **of a callee** | open | **discharged** — `KoerperGutS` clause 1, caller duty |
| `Logik.nachbedingung` | open | **discharged** — `KoerperGutS` clause 1, body triple |
| `Logik.invariante` | open | **discharged** — `InvGutS` |
| `Logik.schleife` | open | **discharged** — `KoerperGutS` clause 2 |
| `Logik.vorzustand` | open | **discharged** — `KoerperGutS` clause 2 |
| `Logik.bereich` | open | **discharged** — `KoerperGutS` clause 2 |
| `Logik.vorbedingung` **of the call itself** | open | it IS the hypothesis: clause 4d already says the condition implies `ReqAmEintritt`, and 4e(ii) asks for it |
| `Logik.abstieg` | open | **stays** — but 4e(i) makes it a computation at ONE depth |

So: of the seven `Logik` constructors, six are gone and the seventh (`abstieg`) is the depth
residue that 4e(i) tames. That is what the report expected, and it held.

### 3.3 THE FINDING: what resists is ONE frame fact, and it is about LOCKS

`rufAt_nurAbstieg` is **not** unconditional. It carries, besides the oracle class and the
user's obligation, one named hypothesis:

```lean
def RufRahmenTreu (P : Programm D) (R : Handler) : Prop :=
  ∀ f σ ρ σ' v, R f σ ρ = .ok σ' v →
    Rahmen (D.schreibt f) (D.gschreibt f) σ σ' ∧ offen σ'.spur = offen σ.spur
```

This is the FRAME half of `RespektiertRahmen`. `rufAt_gut` (`Satz.lean`) proves it only at
worlds meeting `HeldB (D.signatur f).boden (Signatur.anfang D (D.signatur f)) σ.haelt`, and
part 4 quantifies over **any** Gabbro world, including worlds holding locks outside the
callee's floor.

**Three things sharpen this, and each is a measurement, not a hope:**

1. **The CONTRACT half is proved** (`rufAt_vertraege`). An `ok` answer of `rufAt` passed the
   callee's `ensures` test; that test and `EnsAmRueck` differ only by READS, and
   `eval_spurfrei` says no expression sees the trace. So the gap is **one** conjunct of
   `RespektiertRahmen`, not two — a reader can no longer wonder which half is missing.
2. **The gap is about LOCKS and nothing else** (`rufRahmenTreu_ohneSperren`). If the
   declaration has no `D.Lock` at all, no world holds anything, `HeldB` is vacuous, and
   `rufAt_gut` gives the frame everywhere. The residue is the lock discipline's `HeldB`
   premise, not the frame.
3. **On a real chain it is free.** Chain 108's declaration has no lock
   (`Kette108.kein_lock`), so clause 4e(ii) lands there **unconditionally**
   (`nurAbstieg_zeuge_108`): no call of 108's program ends in a `logik` outcome other than
   an `abstieg`, at any depth, from any entry meeting the callee's `requires`.

**What removing the hypothesis would cost:** a second long induction over the semantics —
either a `HeldB`-free `Rahmen` theorem (the frame is a static write-set fact and does not
need the lock discipline; `Gut` bundles it with `Brav`, which does), or the invariant
"every call site of a body run inherits `HeldB` from the entry" made explicit out of
`end_gutB`'s proof, where it exists but is not stated. Either is the same order of work as
the congruence itself. It is booked, not hidden.

### 3.4 A second obstacle that was NOT in the report, and how it fell

`KoerperGutS` and `InvGutS` are stated over **`execEndH`** — the body semantics WITH acquire
moves and release checks, quantified over every environment move in `HavocOk S`. `rufAt`
runs `execEnd`, which has neither. They agree on a body without `locks`
(`Endblock.execH_ohne`), and a certified body IS one: `GRow` has no acquire row, so `stOk0`
answers `false` on `Stmt.locks`. `korrOk_ohneLocks` (`KorrOkOhneLocks.lean`) reads that off
the check by the same induction `korrOk_hardwareFrei` runs on. The class `HavocOk S` is
inhabited under premise (b) (`havocOk_misch_lokal` over `StartPflicht.sperren` — the P1
repair), so the instantiation is not vacuous.

*This is the second time the same check has been read for something it was not written to
decide. It is worth saying out loud: `korrOk` now carries THREE readings — the C
correspondence, "no oracle form", "no `locks`" — and the third was found only because the
obligation's semantics did not match the model's.*

## 4. The other open item of §6.5 — checked against the lemma, and it does NOT close

The task asked for the lemma to be checked against **both** consumers before building it.
The second one is the un-re-instantiated link between part 4 (`rufAt`) and part 5 (machine
G). **The congruence does not close it, and the reason is structural, not a matter of
effort:**

> The congruence relates two runs of **the same body text, from the same world, with the
> same arguments**, differing only in what a handler ANSWERS. `rufAt` and `rufRumpf`
> (which `rufG_adaequat_ruf` realises) differ in the **world the body runs from and returns
> to**: `rufAt` reads `(P.requires f).orte` at entry, `(P.ensures f).orte` at the return and
> one `lese` per owed invariant. Those reads change the TRACE, and the trace is what
> `SpurInv` and race freedom are about. There is no `Er` and no pair of handlers for which
> `HandlerUnter Er` states that difference.

What the lemma DOES give that item is the depth half of its `Tief P A n` residue (4e(i)) —
one of the four obstacles §6.8 measured, and the smallest. The other three
(`rufRumpf` ≠ `rufAt` on the trace; the existential machine shape; and now the depth) are
unchanged. **So §6.8's "items 1 and 2 are one item" was half right**: item 1 needed the
congruence and got it; item 2 needed something else, and the congruence is not it.

## 5. What did NOT have to move

`Semantik.lean` and `Fehler.lean` were reserved for this lane and were **not edited**. That
is a result, not an omission: the congruence is a theorem ABOUT the semantics as written,
and if it had needed a change to `execEnd` — a caught error, a normalised tag, a new
outcome — the change would have invalidated every adequacy and correspondence file that
reads `execEnd`. The lemma went through because the semantics already has the property:
*errors propagate verbatim.* The docstring of `HandlerKongruenz.lean` says so at the site.

## 6. Witnesses

| witness | what it exercises | non-degeneracy |
|---|---|---|
| `Kette104.tiefe_zeuge_104` | `rufAt_tiefer`, `rufAt_stabil_ab` | depth `0` gives `logik (abstieg einzahlen)` (the right disjunct is inhabited); depth `2` RETURNS and moves the slot `0 → 100`; from depth `2` up, the same outcome at every depth |
| `Kette108.rahmenTreu_108` | `rufRahmenTreu_ohneSperren` | 108's declaration has no lock, `StufenOk P8` proved |
| `Kette108.nurAbstieg_zeuge_108` | clause 4e(ii) of `schlusssatz`, UNCONDITIONAL on 108 | the same statement is paired with `rufAt P8 O8 0 1 a8 … = .ok σ' v`, so it is not a statement about an empty set of runs |

## 7. What a reviewer should check

- `git diff master -- grammatik/Grammatik/Schlusssatz.lean` — the premise list is untouched;
  the only conclusion change is ONE new conjunct (4e) inserted after 4d, and the CUTS text.
- The three index moves (`Kette108.lean`, `CText108.lean`, `Kette104Satz.lean`) are conjunct
  positions only: parts 5 and 6 moved right by one `.2`.
- `schlusssatz_text` (`CParser/Bruecke.lean`) restates the conclusion, so 4e is there too;
  its proof is still the one-liner `schlusssatz K …`.
- `HandlerUnter` is ONE-SIDED. If a later reader "fixes" it to the symmetric form,
  `RufTiefe.lean` stops compiling — the docstring says why.
- `rufAt_nurAbstieg` carries `RufRahmenTreu` as a hypothesis. It is a hypothesis in the
  THEOREM and in clause 4e(ii) of `schlusssatz`; it is not smuggled in as an axiom, and
  `#print axioms` shows the standard three.
- No emission counter, no diagnostic code, no corpus file, no gift number was touched.
