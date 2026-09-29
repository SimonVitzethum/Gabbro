# Assignment: verify GabbroV — from "the duties are green" to the goal theorem

*Written 2026-09-29 after the GabbroV server lane (report: `messung/GABBROV-SERVER-REPORT.md`).
Self-contained entry point for whoever takes this on (an Opus-class agent or a contributor).
Companion document: `dokumente/AUFTRAG-UEBERSETZUNGSVALIDIERUNG.md` (the chain to the C) — this
one closes the OTHER open end of the project's central claim.*

---

## 1. The claim, and why it is not a theorem yet

The project's sentence: **a person who wants to verify a Gabbro program proves only their own
logic plus named hardware assumptions.** Two pieces exist:

- **The goal theorem** `gabbro_ziel` (`grammatik/Grammatik/Zielsatz/Spec.lean`): if the checker
  accepts a unit `E` and **premise (b)** `NutzerPflicht E` / `NutzerPflichtA E` holds (the user's
  logic and start obligations, `Spec.lean:1590` ff., `:2078`), then every reachable machine
  satisfies the goal. Premise (b) is stated over **machine G** (`Programm D`, `execEndH`,
  `KoerperGutS` in `SperreFuss.lean:374`).
- **GabbroV** (`programmlogik/`): `gabbro prove` generates, per unit, a duty file
  (`programmlogik/Duty/*.lean`, written by `crates/gabbro-check/src/lean.rs`) whose statements
  `X_meets_statement` / `X_keeps_statement` the person proves; the gate (`beweis.rs`) says GREEN
  only when Lean checked every duty with standard axioms. The duties are stated over a
  **different model**, `programmlogik/Gabbro/Body.lean` (`Stmt` :966, `exec` :1357, `Env`).
  Measured 2026-09-29: 192 corpus units GREEN, 12 OWED, 0 RED.

**Nothing connects them.** Three gaps, each of which alone breaks the claim:

| | Gap | What could go wrong today, undetected |
|---|---|---|
| **G1** | **Fidelity of what GabbroV generates.** The duty file's data — the body as a `Stmt` term, the `requires`/`ensures` as `pre`/`post`, the callee contracts, loop rules, frames — is printed by `lean.rs`, unverified Rust. | `lean.rs` drops a conjunct of an `ensures`, mistranslates an operator or a branch, or prints another function's body: the person proves a statement about a program that is NOT theirs, and the gate says GREEN. |
| **G2** | **Two semantics.** `exec` over `Body` and `execEndH` over G are different definitions, filled by different exporters (`lean.rs` vs `lean_g.rs`). | A construct means one thing in `Body` and another in G: a GabbroV proof is valid about `Body` and says nothing about the goal theorem. |
| **G3** | **Parts of (b) no duty covers.** `StartPflicht` (lock invariants and start `requires` at the initial memory — GabbroV ASSUMES `Initially`); the atomic rely of `NutzerPflichtA` (every value a shared atomic read may return — the exporter refuses `Exchange`/`AwaitLoad`); owed invariants at reason exits (partly). | All duties GREEN, and (b) still false. |

**G1 is the one Simon named explicitly:** it must be proved that what GabbroV generates really
corresponds to the program. Note what does NOT need verifying: the proof automation
(`gabbro_pipeline`, `gabbro_calls`, `gabbro_auto`) — the Lean kernel checks every proof it
produces. Only the STATEMENTS must be the right ones; that is exactly G1 + G2.

## 2. The target theorem

For a source text `src` (the `.gab` file, byte for byte):

```
bruecke : uebersetzeAllg src = .ok ⟨u, P, fs0⟩              -- the Lean parser/elaborator (T3), not Rust
        → E is the Einheit of P (as in a Kette, Schlusssatz.lean)
        → (∀ duty d ∈ pflichten (zuBody P), proved d)       -- GabbroV's duties, GENERATED IN LEAN
        → startDuties E                                     -- G3: the start obligation as duties
        → NutzerPflicht E        (and NutzerPflichtA E where shared atomics occur)
```

Two things make it strong:
- **Everything is anchored at the source text in Lean.** The G program comes from the Lean parser
  (`uebersetzeAllg`, `grammatik/Grammatik/Schlusssatz.lean`), not from `lean_g.rs`; the `Body`
  program and the duty statements are computed from it by **Lean functions** (`zuBody`,
  `pflichten`). The Rust exporters are demoted to printers: their output must be *equal* to the
  Lean computation, checked per unit by `rfl`/`decide`, so a wrong Rust print is a failed check,
  never a wrong theorem. This closes G1.
- **The semantic relation is proved once, generically** (`zuBody` simulates G), not per program.
  This closes G2.

Combined with the goal theorem and the translation-validation chain (the companion document):
*source text → (Lean) G → goal theorem, (Lean) G → Body → the person's proofs, G → emitted C* —
the central claim becomes a Lean theorem, up to the named assumptions (C compiler, hardware).

## 3. How to proceed — stages with measurable finishes

**The one metric: the bridge count** — the number of corpus units for which an instance of
`bruecke` is Lean-checked. Build a counter for it in the style of `instrumente/zaehle-kette.py`
(an instance counts only when Lean re-ran it; the source is pinned byte for byte).

**S0 — make the two projects meet, and measure the overlap.**
- `grammatik/` (core Lean, `leanprover/lean4:v4.33.1`) and `programmlogik/` (mathlib,
  `v4.33.0`) are separate Lake projects on DIFFERENT toolchains. A theorem about both needs one
  project that imports the other (recommended: `programmlogik` requires `grammatik` as a Lake
  dependency; `grammatik` stays mathlib-free). Unify the toolchain first; `#print axioms
  gabbro_ziel` must stay the standard three.
- Measure which `Stmt`/`Expr` constructors of `Body` and of G the corpus uses, and which units
  pass BOTH `uebersetzeAllg` (sieve (a) of the chain count) and `gabbro prove`. That
  intersection is where bridges can close first. Write it into the report before building.

**S1 — `pflichten` in Lean (closes G1 for the duty statements).**
- A Lean function that computes, from a `Body` program with its contracts, exactly the
  statements `lean.rs` prints (`X_pre`, `X_post`, `X_body`, the callee contracts, the
  `meets`/`keeps` statements). Per unit: `rfl` between the printed Duty file's definitions and
  the Lean computation.
- Planted defects (mandatory): a `lean.rs` that drops an `ensures` conjunct, swaps `<`/`<=`,
  prints a wrong callee contract — each must make the per-unit check FAIL.

**S2 — `zuBody : Programm G → Body program` (closes G1 for the program itself).**
- Defined for the common fragment of S0; every other construct is refused with a reason (a
  refusal is not a gap in the bridge, it is a unit outside it — counted).
- Per unit: `rfl` between `lean.rs`'s body datum and `zuBody` of the parsed program.

**S3 — the simulation theorem (closes G2).**
- `exec` on `zuBody P` corresponds to `execEndH` on `P` (outcomes, the reason channel, the
  world) for the fragment; then `meets_statement (zuBody P) f → KoerperGutS P … f`, with the
  owed invariants at value AND reason exits (`InvGutS`, `InvGutGrund`) and the lock rely
  (`HavocOk`, already modelled as acquire/release in the duty channel since 2026-09-29).
- Start with the smallest kernel (assignment, `if`, direct call, `return`, the reason channel),
  close one bridge, then widen by constructor — each widening judged by the bridge count.

**S4 — the parts of (b) no duty covers (closes G3).**
- `StartPflicht` as generated duties (lock invariants and start `requires` hold at the declared
  initial memory) instead of the assumption `Initially`.
- The atomic rely: duties quantify over every value a shared atomic read may return
  (`HavocA`), and the exporter stops refusing the forms it needs.

**S5 — the generic `bruecke` theorem and its instances;** the bridge counter in the guardian
set; `Spec.lean`'s header and `README.md` §5 say exactly what the bridge covers.

**S6 — join with the chain to the C:** a unit with a closed chain (`schlusssatz`) AND a closed
bridge is verified end to end. Report that count too.

A realistic first result: S0–S3 for the kernel fragment and the first closed bridges on small
corpus units (e.g. the four units that carry a proof today: 120, 124, 151 and the tagged probe),
with the planted defects of S1/S2 caught.

## 4. Rules (non-negotiable)

- No `sorry`, `admit`, new `axiom`, `native_decide`; `#print axioms` standard for every theorem,
  and still exactly `propext`, `Classical.choice`, `Quot.sound` for `gabbro_ziel`.
- **`Zielsatz/Spec.lean`'s statement is not changed to make the bridge fit.** The bridge proves
  premise (b) as it stands. If (b) itself looks wrong, write down why and stop for review.
- **Never weaken a duty to make it provable**, and never make `pflichten` produce a weaker
  statement than `lean.rs` did — S1's `rfl` would pass, and the bridge would be about a
  different program. The duty statement has to be STRONG ENOUGH for (b); that is what S3 proves.
- Witnesses for every ∀-over-syntax theorem; a planted defect for every check.
- Measure, never estimate; every number with its command. English everywhere in the tree.
- Ownership: `programmlogik/`, `crates/gabbro-check/src/lean.rs` and `beweis.rs` are this
  work's; `grammatik/Grammatik/Zielsatz/` is read-only; the Lean parser (`grammatik/Grammatik/
  Parser/`, `uebersetzeAllg`) is shared with the translation-validation work — coordinate.
- `cargo test --no-fail-fast` stays at zero failures.

## 5. What this does NOT cover

- The C and the hardware — that is the companion chain (`AUFTRAG-UEBERSETZUNGSVALIDIERUNG.md`)
  and the named assumptions.
- Whether a person's `ensures` says what they MEANT: the bridge proves the proved statement is
  the program's own contract, not that the contract is the right specification.
- Constructs outside the common fragment: counted and refused by name, never silently bridged.

## 6. Effort

S0–S2: days to two weeks. S3 is the core — a simulation proof between two semantics, comparable
to the generic closing theorem; estimate 2–6 weeks. S4: StartPflicht is small, the atomic rely
medium. Opus-class work; the per-unit checks and widening afterwards are schematic.

## 7. Reading list

1. This file; `messung/GABBROV-SERVER-REPORT.md` §4 (the gap, measured, part by part).
2. `grammatik/Grammatik/Zielsatz/Spec.lean` — the header, then `LogikPflicht`, `NutzerPflicht`,
   `NutzerPflichtA`; `SperreFuss.lean` `KoerperGutS`.
3. `programmlogik/PLAN.md` §1–§3, `programmlogik/Gabbro/Body.lean`, one generated Duty file
   (`programmlogik/Duty/Duty01Tabelle.lean`) and one proof (`programmlogik/Proofs/`).
4. `grammatik/Grammatik/Schlusssatz.lean` (`Kette`, `uebersetzeAllg`) and
   `instrumente/zaehle-kette.py` (how an instance is counted — the model for the bridge counter).
5. `crates/gabbro-check/src/lean.rs` (the printer to be checked) and `beweis.rs` (the gate).
