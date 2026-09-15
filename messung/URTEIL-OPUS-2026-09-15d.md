# Verdict on `GabbroZiel` after the G1 repair (independent Opus reviewer, round 6, 2026-09-15d)

*Base: `master` at `dc880b54`. Lean 4.33.1. Server directory: `~/gabbro-muse/opus-urteil6/` on
ki-pc-fisch-101, with `.lake` taken from `stage/lake3`. There, `lake build Grammatik.Zielsatz.Beweis
Grammatik.Zielsatz.Proben Grammatik.Zielsatz.ProbenG1 Grammatik.EinpassenVoll` finished
successfully (88 jobs), so the oleans match the sources. My probe file is
`grammatik/.tmp/urteil_opus15d.lean` and is NOT committed. `lake env lean` on it exits 0 with 0
errors and 0 `sorry`. Every probe prints `[propext]`, `[propext, Quot.sound]` or
`[propext, Classical.choice, Quot.sound]`, and so does `gabbro_ziel`. No cargo was run and nothing
was pushed. I did not read any `URTEIL-*-2026-09-15d*` file except this one.*

## VERDICT: **the goal with named gaps -- no unnamed gap found.**

**G1 is closed.** My own probe uses three forms the committed G1 probes do not use:
- an axiom returning a function pointer;
- a THREE-case sum answered in its payload case;
- a float register whose range excludes `0.0`.

An oracle that meets (c) answers all three with fitting values, and probe A behind them is
refuted by (b).

**The systematic sweep finds no outcome** that has all four of these properties:
1. user code or the model decides it;
2. (b) does not constrain it;
3. it can empty the obligation;
4. it is not named in the ONE list.

**Every outcome the obligation does not constrain is one of these:**
- an oracle answer, which (b) quantifies;
- the `forever` budget, which is quantified;
- a named declaration-level vacuity of the `Q := false` kind: an empty answer type, a register
  promise that is false on the whole type, or an unsatisfiable axiom `ensures`.

**One wording defect (W1), not a gap.** It concerns the reason the ONE list gives for the new stop
kind `nieZurueck`. It says *"the continuation is unreachable in the C as in G"*. That is true only
for an axiom `-> never`, where the C prototype is `_Noreturn`. For every other empty answer type,
and for every register, the C call or read returns and the continuation runs in the C, covered by
nothing. That is honest vacuity, because the declaration is false, but the sentence claims more.
Probe `n_ziel` shows the consequence: probe A behind an axiom returning a pointer type that no
function has is certified. See §3.

---

## 1. G1: closed (own probe, `grammatik/.tmp/urteil_opus15d.lean`, part 1)

**The declaration.** `uD` is `g1D` with these changes:
- two axioms: `true : -> fn(sig 0)` and `false : -> a | b | c(5 .. 7)`;
- the register at `f64 in 1 .. 2`.

**The program.** Body `uP` is `if true { let p = zeiger(); let s = fall(); let t = temp; }
return;` under `ensures false`.

**The oracle `uO`.** It answers:
- address `7`, which the image `zeiger` maps to `haupt` (signature 0);
- `20 = 2 + 3 * 6`, which is case `c` with payload 6;
- the binary64 bits of `1.5` for the register.

| Probe | Shows | Axioms |
|---|---|---|
| two `example`s | the round-5 raw words now decode: `.sum [none, none]` at `0`, `.fnptr 0` at an image address | `decide` |
| `u_akzeptiert` | the checker accepts `uP` with `haupt` declared, so any refusal must come from (b) | `[propext]` |
| `uF_dek`, `uS_dek`, `uR_dek` | each of the three answers decodes (`zeigerPasst`, `summePasst`, `gleitWortPasst`) | std |
| `u_lauf` | under `uO`, `execEndH … (uP.rumpf ()) σ .nil = .zurueck σ' ()`: the body RETURNS | std |
| `u_widerlegt` | no program with code `uP` meets (b), whenever the two axioms' declared ensures hold at the decoded answers at some world (`GutO`, `RegLokal` and `AxVertragO` are all shown for `uO`) | std |
| `u_widerlegt_wahr` | the same with the trivial axiom ensures, unconditionally | std |

The committed probes `g1PA_widerlegt` and `g1PR_widerlegt` also rebuilt with standard axioms. The
decodings match what SATZKARTE §24.2 claims. `einpassen_voll` and `antwortLeer_iff` are the right
statements: the model refuses exactly the words that decode to no value of the type (for floats:
no well-formed value).

## 2. The sweep: every outcome, who decides it, and what constrains it

Legend:
- **(b)** means `KoerperGutS`/`InvGutS`/`InvGutGrund` (SperreFuss:374) constrain it.
- **concl.** means a leg of `Ziel` constrains it.
- **named** means an entry of the ONE list (Spec:126-210).
- "decides" means the party that fixes the outcome for EVERY oracle in the class of (b) and (c).

### 2.1 Outcomes of the sequential semantics (`execStmtH`/`execBlockH`/`execEndH`, SperreSem:186-382; `execStmt`/`execBlock`/`execEnd`, Semantik:669-862)

| Constructor | Site(s) | Decided by | Constrained by | Can it empty (b)? |
|---|---|---|---|---|
| `ok` | every normal step | user code | continues | no |
| `zurueck σ v` | `ret` | user code | (b) `EnsAmRueck` + `InvGutS` | no |
| `grund σ r` | `retGrund`; a handler's reason at `bindCallElse` | user code / callee | (b) `InvGutGrund`. The caller's `else` block is covered by the caller's (b). A plain `call` needs `gruende = 0`. Starts have no reasons (`wurzeln`). `ensures` is checked only at a value return (`rufAt`, Semantik:890-897) | no |
| `leave`/`next` | loops | user code | `l = false` at body level. `freiH` checks the invariant | no |
| `logik vorbedingung` | callee `requires` via `torRuf` | user code | (b) clause 1b, caller duty | no |
| `logik schleife` | `traverseLauf` 536/538/542, `foreverLauf` 575, release `freiH` 161-163 | user code | (b) clause 2 | no |
| `logik vorzustand` | `uebergang` 690/208 | user code | (b) clause 2 | no |
| `logik bereich` | `gleit`, `gleitLit`, `gleitVon` 828-837/347-356 | **model** (kernel IEEE) on user values | (b) clause 2 (F1) | no |
| `logik nachbedingung`/`invariante`/`abstieg` | only in `rufAt` 884-902 | model/user | not an `execEndH` outcome. G checks nothing at a return; the conclusion (`vertrag`, `invRueck`) states it | n/a |
| `hardware annahme` at `axiomCall` | 737/255 | — | dead: `axiomCall` requires `aerg a = none` (Syntax:496), and `einpassenErg none = some ()` | n/a |
| `hardware annahme` at `bindAxiom` | 793/312 | the **oracle** if `¬ AntwortLeer`. The **declaration** if `AntwortLeer` | unconstrained, but for an answerable type and an `E.Q` satisfiable at a decodable value, some (c)-oracle answers and (b) covers the continuation (`u_widerlegt`, `g1PA_widerlegt`). `AxEns` takes no call arguments (AxiomVertrag:44) and `AxEnsLokal` makes it depend only on write carriers, so infeasibility is GLOBAL to `Q`, never per call site | only by a false declaration: `Q` infeasible (named, "Q := false"), or an empty type (named `nieZurueck`, W1) |
| `hardware register` | `regLies`/`regLiesElse` 799/806 | the **oracle** if answerable, the **declaration** if empty | as above. `RegLokal` allows a constant fitting answer | only by an empty type (named, W1) |
| `hardware geraet` | `regLies` 798/317 | the oracle, OR the **declaration** when `rzusage r` is false on the whole type | the declared promise | yes, by a false declaration (named: "a promise the user declares false") |
| `hardware sichtbarkeit` | `awaits` 811/330 | the **oracle** (`sichtbar`). `RegLokal` allows `sichtbar ≡ true` | (b) covers the continuation for that oracle | no |
| `hardware fortschritt` | `foreverLauf 0` 573 | the **model** (the budget) | `passes` is quantified in (b) AND in `GabbroZiel` | only for a body that really never leaves (partial correctness, named `budget`) |
| `hardware ieee` | not produced (F1) | — | — | n/a |

**Handler answers.** (b) quantifies every `R` with `RespektiertRahmen` plus `OhneVorbedingung`
(clause 1) or `OhneLogik` (clause 2). The possible answers:
- `ok`: must meet the callee's ensures and frame.
- `grund`: goes into the caller's `else`.
- `hardware`: always admissible, so the class is never empty.
- `logik abstieg`: admissible in clause 1 only.

Suppose every admissible `R` must answer non-`ok` at a call. Then in G the callee cannot return
there either: the `vertrag` leg holds for the callee, whose own (b) forbids that return. So the
caller's uncovered continuation is unreachable in G, and the callee ends at one of the named stops
of §2.2 or diverges. Diverging includes non-returning recursion: stack depth is NOT CLAIMED and is
named.

### 2.2 Machine G: when a thread has no step (`FortschrittG`, Spec:619; complete by `gabbro_ziel`)

| Stuck condition | Decided by | Constrained by / named |
|---|---|---|
| `FertigG` (start frame at `ret`, empty stack) | user code | concl. `startEnde`, `keinStartGrund` |
| `WartetG` (`locks L`, another thread holds `L`) | scheduler and other threads | concl. `keineVerklemmung`, `keinZyklus`. A holder at a named stop inside `locks L` blocks forever: named (Spec:204-208; `HardwareImAbschnitt` in Lebendigkeit covers every kind `k`) |
| `KopfHalt .flagge` (`awaits g`, `sichtbar = false`) | oracle / liveness | named (`flagge`) |
| `RestHalt .budget` (`.ewig _ 0`) | model; `passes` is quantified | named (`budget`) |
| `KopfHalt .hardware` at `bindAxiom`/`regLies*` | oracle, answerable types only | named (`hardware`) |
| `KopfHalt .hardware` at a leaf (`.cons s`) | — | dead: no leaf yields `hardware`. `call`/`callInd`/`forever` are not leaves (Maschine:392), and `axiomCall` always answers |
| `KopfHalt .nieZurueck` | the declaration (empty type) | named (`nieZurueck`), with the W1 wording defect |
| failing loop invariant, `uebergang` or float range at the head | user code / model | concl. `keinLogikHalt` (`PrueftG`) and `BereichG`, from (b) |
| failing callee `requires` / `ensures` | user code | G has no check (`ruf`/`rueck`, RufMaschineG:269/296). The `vertrag` leg states them |

**Scheduler.**
- The interleaving is quantified (`RufErreichbarG`).
- (d) admits any subset of the declared starts: named, and `E.starts = []` is named.
- Starvation and termination: NOT CLAIMED.

**Result.** Each constraint-free row is named. Each named row is either decided by an oracle that
(b) and (c) quantify, or it is a declaration that is visibly false. So there is no unnamed gap of
the A/F1/G1 class.

## 3. The probe-A variant for the one new row, `nieZurueck` (part 2 of the probe file)

**The declaration.** `nD` is `g1D` whose axiom returns `fn(sig 5)`. No function has signature 5,
because every `sig` is 0.

**The program.** Body `nP`: `if true { let p = hol(); } return;` under `ensures false`.

| Probe | Shows | Axioms |
|---|---|---|
| `n_leer` | `AntwortLeer nD (nD.aerg ())` | `[propext, Quot.sound]` |
| `n_lauf` | `execEndH … = .hardware (.annahme ())` for EVERY `S`, `O'`, `U`, `passes`, `R`, `f` | std |
| `n_nutzer` | `NutzerPflicht nE` with `ensures false` | std |
| `n_akzeptiert` | the checker accepts, with `haupt` declared | `[propext]` |
| `n_erfuellbar` | all four groups jointly, and `haupt` runs on a thread | std |
| `n_ziel` | `gabbro_ziel akzeptiert_pruefer` certifies it: every leg, every run | std |
| `n_kopf` | the head is `KopfHalt .nieZurueck`, and NOT `KopfHalt .hardware` (which now demands `¬ AntwortLeer`) | std |

**Why this is named and not a gap.**
- Spec:177-183 and the `HaltArt.nieZurueck` docstring (Spec:565-572) list "a pointer type no
  function has" explicitly.
- They state that the continuation and the `ensures` stay vacuous.
- The declaration is false: SYNTAX §2 says a `fnptr` value "is a function of exactly this
  signature", and no such function exists. So no foreign code can meet it, which is the
  `Q := false` class.

**W1, the defect.** The sentence *"The continuation is unreachable in the C as in G"* (Spec:182-183)
is false outside `-> never`:
- An `extern fn hol() -> fn(sig 5)`, an empty range or `grund 0` has an ordinary C prototype. The
  call returns some word, and the C continuation runs.
- A register read never "does not return" in C.

"Visible in the declaration" is also weaker for pointer types than for ranges. Emptiness is a
whole-program fact (no function of that signature in `D.Fn`). It holds even when a separately
linked unit supplies such a function: the linked C then reaches the continuation, while the
unit's certificate is vacuous there. That interacts with the linking gap (PLAN §10), which Spec's
NOT CLAIMED list does not mention by name.

**Repair (small, pick one):**
- **(i)** Correct the sentence. For a non-`never` empty type: *"the declaration is false (no answer
  can meet it), so the C continuation runs outside every assumption and is covered by nothing,
  like a call after `Q := false`"*. Say the same of registers.
- **(ii) (preferred)** The checker refuses `bindAxiom`/`regLies`/`regLiesElse` at an `AntwortLeer`
  type other than an axiom's `never`. This is decidable: range bounds, `grund 0`, sum cases, and
  `∃ f ∈ fs, D.sig f = m`. Then `nieZurueck` means exactly `_Noreturn`, where the stated reason is
  true.

## 4. The four review questions (PLAN-ZIELSATZ §5), as `GabbroZiel` stands

1. **The legs.** Unchanged in substance. `fortschritt` names one more kind. `zeit` is still weak
   (named). Crash freedom is still not a leg: all stops are named, none is claimed absent.
2. **Groups.** Every premise is in exactly one group.
   - `Orakel.zeiger` is new. It is an oracle field that no assumption restricts, and (b)
     quantifies it. That makes (b) stronger ("for every layout"), so nothing is smuggled.
   - `mitRuhe` maps it as `(O.zeiger k).map some` (MitRuhe:657), so the idle root is never a
     pointer answer.
3. **Can a user choice empty an obligation?** Only by a visibly false declaration:
   - `E.Q` infeasible;
   - `rzusage` false on the whole type;
   - an empty answer type (W1: named, justification to be corrected);
   - `E.starts = []`.

   None of these is new, except that the empty types moved from `hardware` to `nieZurueck`. I
   re-checked the per-call variant of `Q`-infeasibility (a contract unsatisfiable only at the
   arguments one call passes). It cannot be written, because `AxEns` does not see the arguments.
4. **Does G run what the language means?** G1 is closed for sums, floats and pointers. Two notes
   for the C-side bridge (T1-T5), not gaps of the statement:
   - The sum packing `marke + |cases| * last` is a bijection on VALID pairs only. A C struct whose
     `marke` is out of range can alias a valid raw word: `(marke 5, last 6)` over three cases
     packs to `23`, which decodes as `c(7)`. So the emitted `dekodiere` must reject an
     out-of-range `marke` before it forms the word.
   - "For a satisfiable `E.Q`, oracles with fitting answers exist" (Spec:152-153) is exact only
     for "satisfiable at a DECODABLE value". For floats that means a well-formed one
     (`WertOk`, EinpassenVoll:162). This is a precision note: a `Q` true only at malformed bit
     triples is again a false declaration.

## 5. The gaps

**Not named, to be repaired or named:** none.

**Wording:** W1 (§3). The `nieZurueck` reason is right for `-> never` only. Either correct the
sentence or let the checker refuse empty answer types other than `never`.

**Named, and may stay named:** everything in the round-4 and round-5 lists
(URTEIL-OPUS-2026-09-15b §6, URTEIL-OPUS-2026-09-15c §4), with G1 now repaired as SATZKARTE §24
records it.

---
CUTS:
- This file proves nothing by itself. The probes live in the uncommitted
  `grammatik/.tmp/urteil_opus15d.lean`. I checked them on ki-pc-fisch-101 with EXIT 0, 0 errors and
  no `sorryAx`, against oleans that `lake build` confirmed current (88 jobs).
- The table of §2 comes from reading every `.hardware`/`.logik` site in Semantik.lean and
  SperreSem.lean and the stuck cases of `FortschrittG`. Its completeness for G rests on
  `gabbro_ziel`, not on my reading.
- W1's C behaviour (an ordinary prototype returns) comes from reading SYNTAX.md and SATZKARTE §24.
  I did not check what the emitter writes for an empty range or `grund 0`.
- The sum-aliasing note is arithmetic on `summePasst`. I did not check `dekodiere`/`emit.rs`.
- No existing file was changed.
