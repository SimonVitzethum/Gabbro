# SYNTAX.md section draft: fault outcomes as a parallel model

Status: DESIGN ONLY, no implementation. Worktree `lane-36`, 2026-09-10.
Not committed. This file is a draft of a `SYNTAX.md` section; `SYNTAX.md`
itself is untouched.

Goal: give the fault outcome a home in the grammar documentation without
touching the proved sentences. The model is `grammatik/Grammatik/Fehler.lean`
(new file, checked standalone with `lake env lean Grammatik/Fehler.lean`);
`Grammatik/Semantik.lean`, `Grammatik/Satz.lean`, and `Grammatik.lean` are
unchanged.

## Proposed section text (to land after §18, before "Open items")

```markdown
## 19. Fault outcomes — named, beside the semantics, not in it

Four faults have names: `index` (index out of range), `ueberlauf` (store
outside its declared width), `nenner` (zero denominator), `gestalt` (shape
mismatch). They live in a PARALLEL outcome (`ErgebnisF`: `wert` or `fehler`)
next to `Semantik.lean`, never inside it: `eval` stays total, `exec` keeps
its two error exits (`logik`, `hardware`), and no third exit is added to
`Ausgang`.

Why the parallel outcome never faults today — and that is the statement,
not a gap: a `slot` index has type `.index (count t)` and carries its range
proof with it; out-of-range is not writable. The fault arm is reachable
only through RAW data (`IndexFalle`: a table plus a bare `Int` with no
range proof) — exactly the place where the checker holds the range today.

Agreement shape: no fault implies `eval` agrees (`evalF_ok`, `evalF_stimmt`
as `Prop` definitions). Falsifier shapes are DATA, not proofs: an
out-of-range index reaches `fehler .index` by definition
(`indexFalleErgebnis`), every named case its own fault (`fehlerFallErgebnis`).

Cuts: no threading through `execStmt`/`execBlock` (propagation lemmas for
`evalAll`, step sequence, loop iteration are named, not built); `evalF`
delegates every call to `eval`; not wired into `Grammatik.lean`.
```

## Mapping to the Lean file

| draft phrase | Lean name in `Grammatik/Fehler.lean` |
|---|---|
| four named faults | `Fehlerklasse`: `index`, `ueberlauf`, `nenner`, `gestalt` |
| parallel outcome | `ErgebnisF`: `wert` / `fehler` |
| parallel evaluation, `State -> Expr -> Value plus fault` shape | `evalF (σ₀ σ : World D) (ρ : Env D Γ) (e : Expr D Γ Λ τ) : ErgebnisF D τ` |
| agreement shape, no-fault implies `eval` agrees | `evalF_ok` (`Prop`-def), `evalF_stimmt` (`Prop`-def) |
| gift falsifier, out-of-range index reaches `fehler .index` | `IndexFalle` (structure) + `indexFalleErgebnis` (def) |
| gift falsifier, general | `FehlerFall` (structure) + `fehlerFallErgebnis` (def) |

## Constraints honoured (design only)

- NO `theorem`/`lemma`/`example` commands; NO `sorry`/`admit`/`axiom`;
  proof terms only inside def bodies (none needed — every body is a
  constructor application or a delegation to `eval`).
- NO mathlib, no new dependency; imports only `Grammatik.Semantik`;
  NO import from `programmlogik/` or `passlogik/`.
- Header language matches the neighbours (`Semantik.lean`, `Syntax.lean`):
  German. This draft and the commit message stay English per the
  work-language rule.
- `Body.lean` and every existing file untouched; no `Grammatik.lean`
  index edit. Self-check is `lake env lean Grammatik/Fehler.lean` only —
  no full build, no cargo.

## Cuts (booked, not hidden)

- C1: `exec`-level threading is cut — `Ausgang` gains no `fehler` case, so
  there is no propagation lemma and no `finalState` mapping.
- C2: `evalF` reports `wert` on every term — the fault arms are reachable
  only via the falsifier DATA, not via grammar terms.
- C3: The four classes mirror `S3-FEHLER-ENTWURF.md` design A on the
  `Body.lean` side (`Outcome.fehler`), but no link between the two models
  is stated or proved here.
