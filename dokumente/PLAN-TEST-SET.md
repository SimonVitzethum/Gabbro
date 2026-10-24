# PLAN-TEST-SET — generating the test sets M, N and R from the Lean model

*State 2026-10-20: a plan. Nothing in this file is implemented yet; where it says "exists" it names the file that
does it today. The theory is `CHECKER.md` §16 (Lean: `grammatik/Grammatik/Adaequanz/`). This plan is about the
GENERATOR side: how the sets the theory asks for are produced from the model, and how the producer stays correct when
the model changes.*

## 0. Goal and rule

Produce, from the Lean model alone, the finite set of programs that — together with the hypotheses H1–H8 of
`CHECKER.md` §16.1 — makes a program-neutral checker and compiler correct on all programs, and know exactly how far the
set is from complete.

**The Lean model is the only source** (CLAUDE.md): every denominator (cells, premises, constructors, atoms) is
computed from the model, never typed beside it. A change to the model must stop a build in a named place; a printer
gap must cost a counted amount of coverage, never a wrong program.

## 1. Terms

| Set | Meaning | Where it lives |
|---|---|---|
| **M** | valid programs: `AkzeptiertX = true`, the proof is in the value (`Gutes`) | G terms, then printed |
| **N** | well-typed, well-formed, refused by exactly component `c` (`NurAn c`, `Schlechtes c`) | G terms, then printed |
| **R** | everything that is no G term: a violated typing premise, a syntax error | text only |

G terms are intrinsically typed, so a G term never violates a premise: the local refusal cells (130 premises, 151 child
positions, `Adaequanz/Gabbro/Signatur.lean`) are reachable only as TEXT. That is the open gap of today's generator.

## 2. What exists

| File | Role |
|---|---|
| `Gen/Erzeuger/*`, `Gen/Familie/*` | generators of programs and of declarations (`Spez`) by exact size, with completeness theorems (`*Vollst`) |
| `Gen/Erzeuger/Gueltig.lean` | soundness (S) and completeness (C) of `genGueltig`, `genBad c`; `komp`, `akzeptiertX_iff` |
| `Gen/Abdeckung/Waehlen.lean` | `Spez.erzeuge`: emits only `Gutes` or `Schlechtes c`, each carrying its proof; one body per `Rumpf.schluessel` |
| `Gen/Abdeckung/Zellen.lean` | the cells of the ten components of `AkzeptiertX` (atoms by hand), `zellenStimmen` against `komp` |
| `Gen/Abdeckung/ZellenLauf.lean` | driver `gen-zellen NB KMAX`: first witness per cell, printed witnesses, skip reasons |
| `Gen/Abdeckung/Mitglieder.lean`, `Erklaerung.lean` | total register of constructors and declaration members (new constructor stops the build) |
| `Gen/Druck/Druck.lean`, `Einheit.lean` | the PARTIAL printer: skipped form = counted reason, never a wrong print |
| `Adaequanz/Gabbro/Signatur.lean`, `Zaehlung.lean` | constructor table checked against the model; root-cell counts |
| `Adaequanz/Ueberdeckung.lean`, `Muster.lean` | cover theorems: `deckung_iff`, `deckung_schranke`, `muster_schranke`, `schlecht_noetig` |
| `Parser/Elab/Uebersetze*.lean` | text → G term (Lean elaborator), the candidate oracle for text-level refusals |

## 3. Stages

### Stage 0 — the denominators, computed from the model

Three sets, all derived, none typed:

* **Z_good** — reachable accepted cells of the ten components; for the compiler also constructor × lowering context ×
  child classes (the cells of `lowerS_ok`; their definition is **not yet written**: read `lowerS_ok` first).
* **Z_bad** — all `Zelle.schlecht`.
* **Z_text** — every premise and child position of `Signatur.lean`, every grammar production.

Steps:

1. In `Zelle.kern` replace `| _, _, _ => true` by an error for an unknown (component, kind, length). A wrong-length
   vector must stop the build, not pass.
2. A meta check (same style as `Signatur.pruefeTabelle`) that reads the atoms of each component of `AkzeptiertX` from
   the definition and compares them with `Zelle.kern`; reconcile `atome` in `Zaehlung.lean` with the cell atoms.
3. Generate `dokumente/llvm-modelldeckung.tsv` from the model and compare it in the build.

*Done when:* Z_good, Z_bad, Z_text are computed values and a drift in any of them fails a named build step.

### Stage 1 — M as a cover

1. Sweep `mitglieder × sizes × parameters` with `Spez.erzeuge` (exists); record `zellenVon` per program (exists).
2. **New:** choose a small cover of Z_good among the `Gutes` programs: greedy, then drop every program whose cells are
   covered by the rest. Printable programs first, because only they reach Rust and LLVM.
3. **New:** a lower bound with `deckung_schranke`: a set A of cells that never co-occur; report `|A| ≤ |cover|` so the
   distance to the minimum is a number.
4. A manifest per program: file, class, cells covered. Generated, not written by hand.

*Done when:* every reachable cell of Z_good has a printed witness, or sits in a list "not printable: reason".

### Stage 2 — N as single-fault programs

1. For every bad cell find a `Schlechtes c` in which that cell is the only bad cell of the whole program
   (isolability, `schlecht_noetig`).
2. Cells that are never alone are listed with the masking reason; they lower the bound of `muster_schranke`.
3. Take the smallest program per cell: raise `groesseHaut` until every isolable bad cell has one.

*Done when:* printed N programs = isolable bad cells, and the non-isolable ones are listed.

### Stage 3 — R at text level

Raw material: the printed M programs.

1. One RECIPE per premise (constructor, premise index): a text edit that violates exactly that premise. The 130 recipes
   are hand work; `Signatur.lean` knows the number of premises, not their content.
2. The recipe table is checked for totality against `Signatur.lean`: a new premise stops the build until it has one.
3. Per grammar production: mutations from the grammar (drop, duplicate, swap a token).
4. Oracle: the Lean elaborator `uebersetzeAllg`. The mutated text must be refused and the original accepted; a mutation
   the elaborator accepts is another valid program and is reclassified, not discarded.

*Open:* whether `Uebersetze` returns a distinguishable refusal reason per premise (not read). It decides whether
"exactly one premise" is measured or only assumed.

*Done when:* every premise and child position has a refused text with an accepted twin, or is listed with the reason.

### Stage 4 — the printer, widened without trusting it

Today the printer is partial: `Einheit.lean` skips marks, invariants, registers, a declared floor that the body does not
derive, a lock that protects nothing, call chains of depth ≥ 4, types other than integer range / bool / never; `Druck.lean`
has clauses for 14 of 42 expression constructors.

1. `gen-zellen` reports, per skipped form, the number of cells that stay unreachable. That is the order in which to
   close clauses.
2. A clause counts only when the round trip holds: print → parse → elaborate returns the same term (`Parser/Round`;
   whether the existing round-trip theorems cover each new clause is to be checked).

*Done when:* the skip list is empty or every entry is a language gap (the model is wider than the language), named.

### Stage 5 — compatibility with changes of the model

Per kind of change, the place where the build must stop:

| Change | Stops in |
|---|---|
| new constructor | `Signatur.lean`, `Mitglieder.lean`, the `*Vollst` proofs; the printer only loses counted coverage |
| new premise | `Signatur.lean`, the recipe table (new) |
| new atom in a component | the atom meta check (new, Stage 0) |
| new component | `Fin 10` in `komp`, `akzeptiertX_iff` |
| new field of `Deklaration` | `Spez.deklaration`, `Erklaerung.mitglieder` |

Verification: five model mutations, one per row, each in a throwaway worktree (own worktree, `master` caught up, one
heavy `lake build` at a time). A mutation that does not stop at the named place is a gap in the generator.

*Done when:* the table is a measured result, not a claim.

## 4. Open decisions

1. **Observation for the compiler.** For each M program the compiler test needs the expected behaviour. For concurrent
   programs that is a specification of observations, not one run. Nothing found in `Gen/` or `Adaequanz/` yet.
2. **Lowering cells.** Define them from `lowerS_ok`, otherwise M covers the checker and not the compiler.
3. **Where the manifests live:** generated at run time, or checked in.

## 5. What this plan has not checked

Not read: `Rumpf.schluessel`, `lowerS_ok`, `Parser/Round`, the refusal messages of `Uebersetze`, the current numbers of
`gen-zellen`. Nothing was built or run when this plan was written.

## 6. Order

Stage 0 first: its result supplies the numbers for every other stage. Stages 1 and 2 are independent of each other and
reuse the existing sweep. Stage 4 runs alongside, driven by the skip counts. Stage 3 needs Stage 1 (printed bases) and
the open question about the elaborator. Stage 5 closes the work after Stages 0–3 exist.
