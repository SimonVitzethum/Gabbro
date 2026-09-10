# SYNTAX.md section draft — program composition (lane 35)

*Design draft for `dokumente/SYNTAX.md`, not an edit of it. Status on
2026-09-10: drafted, not built. Base: commit `2657f77` (lanes 26–33 baseline).
Companion file: `grammatik/Grammatik/Komposition.lean` (design only: `def`
shapes, no `theorem`; per-file check `lake env lean Grammatik/Komposition.lean`
in `grammatik/` is green). No edit of `grammatik/Grammatik.lean` (lane scope).*

## 0. Where this section lands

`SYNTAX.md` §6 fixes the per-routine clauses (`requires`, `ensures`,
`decreases`), §8 the three loop forms, and §16.1 the sentence the tree proves
about a body. None of them says how the routines of a program compose: in what
order contracts are established, what carries a call cycle, and what discharges
the two environment premises (`UmgebungOK`, `SchleifenOK`) that the safety
theorem still assumes. This draft proposes that missing section — placed after
§18 as a new §19, so the closed §§1–18 stay untouched.

## 1. Proposed section text (to be moved into SYNTAX.md verbatim on acceptance)

```markdown
## 19. Program composition — in what order the contracts stand

A program is a **body table**: one row per routine with its callees, its
optional `decreases` measure, and its loop identifiers — plus, per routine,
the environment entry that runs the body (`Runs`: where the body ends, the
environment answers with exactly that state and value). The claim is that
both environment premises of the safety theorem are theorems over this table:

| premise today | theorem after composition | induction |
|---|---|---|
| `UmgebungOK` (every declared callee keeps the world and answers per its signature) | `umgebung_ok_of_runs` | topological order where acyclic, measure where cyclic |
| `SchleifenOK` (every registered loop keeps the world and its scope) | `schleifen_ok_of_runsloop` | index list of the loop (`iterate`) |

**Acyclic part — no measure needed.** Where the call graph below a routine is
acyclic, callees precede their callers in a topological order and contracts
are proved innermost first: a leaf meets its duty directly, a caller closes
each call site with the already proved callee contract. The induction is over
the graph order, which is well founded because the fragment is finite and
acyclic.

**Cycles — `decreases` or refusal.** A cycle cannot use the order above: no
member precedes the others. Every member of a cycle must therefore carry a
`decreases` expression, and the induction is over the measure, not the graph —
the `RecursionCycleCarried` shape (`Coverage.lean`): where the environment
runs every body and every duty holds under the bounded contracts of all cycle
members, every member holds its contract. A cycle with a member edge that
carries no `decreases` is not composed; it is refused (`K008`/`K009` on the
checker side, an undischarged bounded duty on the model side).

**Loops — one pass per index.** A loop runs as a sequence of passes over an
index list (`iterate`); each pass preserves the world and the scope under the
invariant, `leave` ends the visitation early. Recursion through a loop body
nests the inductions in a fixed order: the measure induction outside, the
loop rule inside.

**Foreign bodies stay hypotheses.** `extern`, `asm`, and entrusted routines
have no row and hence no duty; their contracts remain hypotheses about the
environment, threaded through rather than closed.
```

## 2. Def-to-surface mapping (what `Komposition.lean` names)

| SYNTAX.md surface | `Komposition.lean` def | model location (cited, not imported) |
|---|---|---|
| the program's routines with bodies | `Gefuege.tabelle` (`Routine`: `ruft`, `mass`, `schleifen`) | `Programm.sig` / `Programm.schleife` (`Sicherheit/Anweisung.lean`:206) |
| the environment runs the body | `Gefuege.laeuft` | `Runs` (`Body.lean`:1408) |
| call sites of a body | `ruftAn` | the `step` call arms (`Body.lean`) |
| acyclic call order | `Topologisch`, `AzyklischUnter` | the graph induction of `S2-UMGEBUNG-ENTWURF.md` §3.2 |
| `decreases e` (§6, «K5.4») | `Routine.mass` (`some` = declared, `none` = absent) | `Below` / `BelowM` (`Body.lean`:1446/1521) |
| every cycle edge lowers | `ZyklusGetragen`, `UnterMass`, `VertragSchranke` | `ContractBelowM` (`Body.lean`:1525) |
| cycle lifting | `RekursionZyklusGetragen`, `ZyklusAusMass` | `RecursionCycleCarried` / `recursion_cycle_carried` (`Coverage.lean`:972/979) |
| (U1) / (U2) | `UmgebungOk` / `SchleifenOk` (Prop-valued) | `UmgebungOK` / `SchleifenOK` (`Anweisung.lean`:599/608) |
| loop passes (§8) | `Durchgang.indizes`, `DurchgangBesucht`, `SchleifeLaeuft` | `iterate` / `RunsLoop` (`Body.lean`:1415/1429) |
| `umgebung_ok_of_runs` shape | `RufAusOrdnung`, `UmgebungOkAusLaeufen` | `contract_of_duty` + graph induction |
| `schleifen_ok_of_runsloop` shape | `SchleifenOkAusLaeufen` | `looprule_of_body` over `iterate` |
| cycle without `decreases` refuses | `OhneMassTabelle`, `ZyklusOhneMass`, `ohne_mass_ist_none`, `ZyklusOhneMassWirdAbgewiesen` | `K008`/`K009` refusal; undischarged `ContractBelowM` |

## 3. Statement shapes (as `def`s, proofs in the later phase)

- `RufAusOrdnung G fs` — order carries, environment runs ⟹ every contract in `fs`.
- `UmgebungOkAusLaeufen G fs zs` — every table row lies in the acyclic part `fs`
  or the carried cycle `zs`; order + carried cycles + runs ⟹ `UmgebungOk G`.
- `ZyklusAusMass G rs` — runs + duties under all bounded member contracts ⟹ all
  member contracts (through `RekursionZyklusGetragen`).
- `SchleifenOkAusLaeufen G d` — the loop runs over its index list ⟹ `SchleifenOk G`.
- `ZyklusOhneMassWirdAbgewiesen` — checked: `¬ ZyklusGetragen ZyklusOhneMass
  ["a", "b"]` (member `"b"` declares no measure). The must-refuse probe is a
  datum plus a checked negation, not a comment.

## 4. Cuts (booked, not hidden)

- C1 No import of the model: lane scope forbids the `Grammatik.lean` index
  edit and the check is per-file, so the correspondence is by name and shape,
  not by reference. Nothing names `Runs`/`Contract`/`iterate` as terms.
- C2 The per-body duty (`pruefeBlock_sicher` over the body, the `exited`/`left`
  rows) is not restated here: THAT a body meets its duty is the writer's logic
  and the checker's work. This design shows only WHERE the duty is lifted to.
- C3 Foreign bodies (`extern`, `asm`, entrusted) have no row and no contract:
  their contracts stay hypotheses over `laeuft`, exactly as `PLAN-VERIFIKATION`
  §2.3 records.
- C4 No liveness beyond the index list: the loop half covers `traverse`/`retry`
  over finite indices; `forever` stays unbounded by contract (cf.
  `Terminierung.lean` §4), not by this composition.

## 5. Acceptance (later phase)

This draft counts as built when `Komposition.lean` grows the four theorems of
§3 over these shapes with `#print axioms` clean, the `ZyklusOhneMass` refusal
still checks, and the §1 text above lands in `SYNTAX.md` as §19 with no change
to §§1–18.
