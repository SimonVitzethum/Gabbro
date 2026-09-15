# Verdict on `GabbroZiel` after the fourth-round repair (independent Opus reviewer, round 5, 2026-09-15c)

*Base: `master` at `cf154952`, which contains `ffdb9362`. Lean 4.33.1. Server directory:
`~/gabbro-muse/opus-urteil5/` on ki-pc-fisch-101, with `.lake` taken from `stage/lake3`. There,
`lake build Grammatik.Zielsatz.Beweis Grammatik.Zielsatz.Proben` finished successfully (85 jobs),
so the oleans match the sources. `gabbro_ziel` prints `[propext, Classical.choice, Quot.sound]`.
My probe file is `grammatik/.tmp/urteil_opus15c.lean` and is NOT committed. `lake env lean` on it
exits 0 with 0 errors. Every probe prints `[propext]`, `[propext, Quot.sound]` or
`[propext, Classical.choice, Quot.sound]`. No cargo was run and nothing was pushed. I did not
read any `URTEIL-*-2026-09-15c*` file except this one.*

## VERDICT: **unnamed gap found: G1, an axiom answer or register read whose declared type `einpassen` cannot hold.** Probes `g_ziel` and `r_ziel`.

**F1, F2 and F3 are closed as stated.** But the class F1 belonged to is not empty. The kernel
function `einpassen` (Semantik.lean:348) returns `none` for EVERY raw answer when the type is
`.sum _`, `.fl _ _`, `.fnptr _` or `.never` (the last also holds for `.grund 0` and for `.int lo hi`
with `lo > hi`). This has three consequences:

- An axiom whose declared result has one of these types ends in `hardware (annahme a)` at every
  call, for EVERY oracle (Semantik.lean:708, SperreSem.lean:312). The axiom is a foreign
  function, a syscall, `entry` or `entrust`.
- A register of such a type ends in `hardware (register r)` at every read (Semantik.lean:714/721).
- `KoerperGutS` does not constrain hardware outcomes. So whatever follows the call or the read is
  free of obligation. Probe A behind one such call passes all of this:
  - it meets (b);
  - the concrete checker accepts it with `haupt` declared;
  - its start runs;
  - every declared `ensures` is `false`;
  - `gabbro_ziel` certifies it.

This is F1's shape exactly: the model decides the stop, the oracle does not, and the stop is
filed under `hardware`. The header's justification for the class does not hold for these types.
It says (Spec.lean:123-126) that *"a type-correct answer is constrained, an ill-typed one is the
foreign code breaking its declaration"*. For `.sum`, `.fl` and `.fnptr` no type-correct raw
answer exists at all. `AxVertragO Q O` is then vacuous for EVERY `Q` (`g_axVertrag_jedes`). So the
foreign function's declared `ensures` is never delivered, and nothing the user writes can be
refuted after the call.

**The types are ordinary, not a false assumption.**
- A tagged result (`ok | err`) is the documented answer type of every syscall. SYNTAX.md:318 and
  :1864 and PLAN-SYSCALL.md:66-67 say *"the answer type is the `ok value | reason r` sum,
  `einpassen` holds the raw answer against it"*. In the model that "holding" always fails, so
  every syscall in that form is a certain stop.
- An `extern fn` returning a float, or an enum-typed or float-typed device register, is equally
  plain.
- This is not the honest vacuity of `Q := false`. That false assumption is visible in the
  declaration. Here the declaration is true, and it is the model's decoder that has no inhabitant.

**Repair (small, pick one):**
- (i) The fragment check (`gOk`) refuses `bindAxiom`, `regLies` and `regLiesElse` at a type that
  `einpassen` cannot inhabit. Name that restriction. `.never` stays admitted, but as a separately
  named stop, "diverges" (see §3).
- (ii) Give `einpassen` a real decoding for `.sum` (tag plus payload), `.fl` (bits, as in
  `GleitkommaBits`) and `.fnptr`.
- (iii) Let `Orakel.wirkt` / `regLies` answer a typed value, so that "out of type" is only the
  explicit out-of-range case.

(i) is the smallest change and keeps the proof. (ii) is what SYNTAX.md already claims.

---

## 1. F1-F3: are they really closed?

**F1: closed for floats.**
- `gleit`, `gleitLit` and `gleitVon` without `else` answer `.logik .bereich` in both `execBlock`
  (Semantik.lean:739-752) and `execBlockH` (SperreSem.lean:347-356).
- `Hardware.ieee` is no longer produced by either semantics. The only remaining use is the
  default of a proof-internal handler (`rufAusL`, ZielOrtGanz.lean:86), which is not an outcome.
- My own probe `hw_lauf_jetzt` is the round-4 crash, `if true { let x = 2.0 in 0 .. 1; }` in
  front of probe A. It now gives `execEnd … = .logik .bereich` for every oracle, handler and
  budget, so the "no `logik` outcome" clause of `KoerperGutS` refutes it.
- `FortschrittG` lists no float stop, and `BereichG` carries the check to G.
- **But see G1:** the same mechanism, a model-decided stop under the `hardware` label, survives in
  `einpassen`.

**My search for every stop the obligation does not constrain.** I checked every `.hardware _`
constructor site in `execStmt`, `execBlock`, `execEnd`, the loop runners and `rufAt` (Semantik)
and in `execBlockH` (SperreSem), together with `KopfHalt`/`RestHalt` in G:

| Site | Who decides it | Verdict |
|---|---|---|
| `foreverLauf 0`, `hardware (fortschritt a)` / G `budget` | `passes`, which is universally quantified | fine: model artefact, justified |
| `axiomCall`, `aerg = none` | `einpassenErg none = some ()`, so it never stops | dead case |
| `bindAxiom`, `hardware (annahme a)` | the oracle, OR `einpassen` alone when the type is `.sum`, `.fl`, `.fnptr`, `.never`, `.grund 0` or an empty `.int` | **G1** |
| `regLies`/`regLiesElse`, `hardware (register r)` | the oracle, OR `einpassen` alone (same types) | **G1** |
| `regLies`, `hardware (geraet r)` | the oracle; `rzusage ≡ false` is named | fine |
| `awaits`, `hardware (sichtbarkeit)` / G `flagge` | `O.sichtbar`; `RegLokal` does not force it `false` | fine, named |
| `locks` release with a failing invariant (SperreSem:161) | `logik schleife` | constrained by (b) |
| `uebergang` | `logik vorzustand` | constrained |
| `rufAt 0` | `logik abstieg`; only in `rufAt`, while (b) quantifies handlers | constrained |

**F2: closed.** `KeinWarteZyklus` is the cycle-free statement of the lock wait-for graph:
- no `t₀ … tₙ₊₁ = t₀` in which each `tᵢ` stands at `locks Lᵢ` while `tᵢ₊₁` holds `Lᵢ`;
- `n = 0` covers the self-loop;
- a chain may repeat threads, and only its closure is refused.

`WartetAuf` is a real blocking relation: `AnSperre` means the head is `locks L`, and `L ∈ offen`
of the holder. `kein_warteZyklusG` is the rank argument, with its links checked by reading.

*Wording note (not a gap):* "no wait CYCLE among any threads" (Spec.lean:182) is true of LOCK
waits only. Suppose `t₁ : locks L { awaits g }` and `t₂ : locks L { publish g }`. That is a mixed
lock/flag cycle, and `Ziel` holds on it. It is covered by the named sentence "a thread at ANY of
these stops while it holds a lock `L`…" (Spec.lean:149-153). Say "no LOCK-wait cycle".

**F3: closed as a list, not as a justification.**
- `HaltArt` has three kinds and each is in the ONE list:
  - `flagge` has a sound reason: any subset of starts may run, and G has no "later";
  - `budget` has a sound reason: every `passes` is quantified, so a thread at this stop is one the
    C keeps running.
- **The reason given for `hardware`/`annahme` and `hardware`/`register` is false for the G1
  types** (above).
- `.never` also deserves its own entry. A call to a `divergent`/`prim fn … -> never` really does
  not return in C either, so stopping there is right. But it is not "foreign code breaking its
  declaration". It is the program's declared end, and a thread doing it inside `locks L` blocks
  `L`'s waiters forever.

## 2. The probes (`grammatik/.tmp/urteil_opus15c.lean`, EXIT 0)

Both probes use `zD` with ONE addition and probe A's contracts: `requires true`,
`ensures false` everywhere. Every body is `if true { <the call or read>; } return …`.

```lean
def gD : Deklaration := { zD with Ax := Unit, aparams := fun _ => [],
  aerg := fun _ => some (.sum [none, none]),          -- `extern fn hol() -> ok | err`
  aschreibt := fun _ _ => false, agschreibt := fun _ _ => false }
def gCrash : Stmt gD V false Γ Λ Λ := .ite .wahr (.bindAxiom () .nil rfl … .nil) .nil
def rD : Deklaration := { zD with Reg := Unit, rtyp := fun _ => .fl (0, 1) (1, 1),
  rklasse := fun _ => .r, spiegel := fun _ => none, rzusage := fun _ _ => true,
  rtraeger := fun _ => [] }                            -- `reg T : f32 in 0 .. 1`
```

| Probe | What it shows | Axioms |
|---|---|---|
| `einpassen_sum/_fl/_fnptr/_never` | `einpassen τ n = none` for every `n`, by `rfl` | none |
| `g_lauf` | `execEndH S O' U passes R (gP.rumpf f) σ ρ = .hardware (.annahme ())` for EVERY `S`, `O'`, `U`, `passes`, `R`, `f` | std |
| `g_nutzer` | `NutzerPflicht gE`, with the start obligation and `ensures false` | std |
| `g_akzeptiert` | `Akzeptiert gP gS gFs [()] [.inl ()] [gHaupt] = true` | `[propext]` |
| `g_erfuellbar` | `Erfuellbar gE`: all four groups jointly, and `haupt` runs on a thread | std |
| `g_ziel` | `gabbro_ziel akzeptiert_pruefer` applied: every leg on every run | std |
| `g_axVertrag_jedes` | `AxVertragO Q gO` for EVERY `Q`: the declared ensures is never delivered | `[propext, Quot.sound]` |
| `r_lauf`, `r_nutzer`, `r_akzeptiert`, `r_erfuellbar`, `r_ziel` | the same for the float register: `hardware (register ())` for every oracle | std / `[propext]` |
| `hw_lauf_jetzt` | the round-4 F1 crash now gives `logik bereich` (F1 closed) | std |

## 3. The four review questions (PLAN-ZIELSATZ §5), as `GabbroZiel` stands

1. **The legs.** Unchanged since round 4, except for the new `keinZyklus`, which is correct for
   lock waits (wording note above). `zeit` is still weak (named). Crash freedom is still not a
   leg. G1 is exactly such a crash: a stop that the user's declaration forces is reported as
   hardware.
2. **Groups.** Every premise belongs to exactly one group. Nothing new.
3. **A user choice empties an obligation: YES, G1.** The user declares the result type of a
   foreign function or the type of a register. `.sum`, `.fl` and `.fnptr` make every call or read
   a certain stop, for every oracle in (c), and (c) stays inhabited for every `Q`. Probe A passes
   (a), (b), (c) and (d) with a running start. Every other user choice I re-tried behaves as in
   round 4: `sp0`, `starts`, the lock family, the start `requires`, `rzusage`, recursion and
   `forever`.
4. **Does G run what the language means?** For G1 it does not. The C returns the syscall's
   `ok | err` value, the float or the enum register value. The model stops. Every program using
   those forms is therefore "covered" only up to its first such call. That fact is not named, and
   it contradicts SYNTAX.md §12.1. (The exporter emits no axioms today, `aerg := nomatch`,
   lean_g.rs:2836, so no exported program hits G1 YET. But `GabbroZiel` quantifies every `E`, and
   hand-written `E` are the only covered programs.)

## 4. The gaps

**Not named, to be repaired or named:**
1. **G1.** `einpassen` has no inhabitant for `.sum`, `.fl` and `.fnptr` (and trivially for
   `.never`, `.grund 0` and empty `.int`). Axiom calls and register reads at those types are
   model-decided `hardware` stops that empty (b). See the repair options above, then correct the
   justification in the ONE list and in SYNTAX.md §12.1 / PLAN-SYSCALL §3.
2. **`.never` as its own named stop kind (or entry)**: "the program's declared end". It is not
   hardware.

**Wording:** "no wait cycle" means lock waits (Spec.lean:182).

**Named, and may stay named:** everything in the round-4 list (URTEIL-OPUS-2026-09-15b §6),
together with the round-4 repairs as SATZKARTE §23.7 records them.

---
CUTS: this file proves nothing by itself. The probes live in the uncommitted
`grammatik/.tmp/urteil_opus15c.lean`, checked on ki-pc-fisch-101 with EXIT 0 and 0 errors,
against oleans that `lake build` confirmed current (85 jobs, replayed). The mixed lock/flag cycle
comes from reading; I built no machine for it. That real programs use tagged or float extern
results comes from reading `beispiele/*.gab` (`-> u32 or HolFehler`, `-> BootPhase`) and
SYNTAX.md. How the Rust side would map those types was not checked. No existing file was changed.
