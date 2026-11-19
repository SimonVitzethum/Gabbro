/-
  File:      Grammatik/Gen/Abdeckung/ZellenPruefung.lean
  Subject:   The DRIFT CHECK of the cells (Stage 0 of `dokumente/PLAN-TEST-SET.md`): a change of the model that touches a
             component of `AkzeptiertX` must stop the build HERE, at a named place, until the atoms and tests of
             `Zellen.lean` are read again.

  The atoms of `Zellen.lean` were read off the definitions by hand. What this file pins is not their meaning but
  their SOURCE: for each of the ten components, a hash over the definition of the component and of every definition it
  uses, transitively, inside `Gabbro.Grammatik` (the model; the generator and the printer under `Gabbro.Grammatik.Gen`
  are excluded, so changing them does not move it). `komp` and `AkzeptiertX` are pinned too: a new component moves them.

  A mismatch is an error that names the component and prints the new hash. To accept a change: read the component's
  definition again, adjust the atoms and the tests in `Zellen.lean` if they no longer follow it, then update the pin.
  The hash is `Expr.hash` of the definition bodies (structural, independent of binder names); it can also move with a
  change of the Lean toolchain, in which case the pin is updated the same way.
-/
module
public import Lean
public import Grammatik.Gen.Abdeckung.Zellen
meta import Lean
meta import Grammatik.Gen.Abdeckung.Zellen
@[expose] public section


namespace Gabbro.Grammatik.Gen.ZellenPruefung

open Lean Meta

/-- The ten components, then `komp` and `AkzeptiertX` (label, name). -/
def gepinnt : List (String × Name) :=
  [("0 fragment", ``Gabbro.Grammatik.programmImFragmentG), ("1 closedness", ``Gabbro.Grammatik.abgAlleB),
   ("2 footprint", ``Gabbro.Grammatik.Zielsatz.fussWXB), ("3 lock ranks", ``Gabbro.Grammatik.stufenB),
   ("4 lock sites", ``Gabbro.Grammatik.sperrOrteB), ("5 roots", ``Gabbro.Grammatik.wurzelnB),
   ("6 single pool", ``Gabbro.Grammatik.einzelnPoolB), ("7 race freedom", ``Gabbro.Grammatik.rennB),
   ("8 answers", ``Gabbro.Grammatik.antwortenB), ("9 masks", ``Gabbro.Grammatik.maskenB),
   ("komp", ``Gabbro.Grammatik.Gen.komp), ("AkzeptiertX", ``Gabbro.Grammatik.Zielsatz.AkzeptiertX)]

/-- Is the name inside the model (and not in the generator or the printer)? -/
def imModell (n : Name) : Bool :=
  (`Gabbro.Grammatik).isPrefixOf n && !(`Gabbro.Grammatik.Gen).isPrefixOf n

/-- All definitions inside the model that `start` uses, transitively, with `start` itself. -/
partial def huelle (env : Environment) (start : Name) : Std.HashSet Name := Id.run do
  let mut gesehen : Std.HashSet Name := {}
  let mut offen : List Name := [start]
  while !offen.isEmpty do
    match offen with
    | [] => pure ()
    | n :: rest =>
      offen := rest
      if gesehen.contains n then continue
      gesehen := gesehen.insert n
      match env.find? n with
      | some (.defnInfo d) =>
        for c in d.value.getUsedConstants do
          if imModell c && !gesehen.contains c then offen := c :: offen
      | _ => pure ()
  return gesehen

/-- The hash of the definitions in the closure of `start`. -/
def huelleHash (env : Environment) (start : Name) : UInt64 :=
  let namen := (huelle env start).toList.toArray.qsort (fun a b => a.toString < b.toString)
  namen.foldl (fun h n =>
    match env.find? n with
    | some (.defnInfo d) => mixHash h (mixHash (hash n) d.value.hash)
    | _ => h) 7

/-- The numbered component formulas and their cell atoms were re-read after the C-package
    integration. Their quantifiers and Boolean tests still match `Zellen.zellen`;
    scoped-return traversals and native-float type classification changed their closures.
    `AkzeptiertX` also retains interface/library, accumulator, check, reset, scope and
    guest admission. These are not additional numbered cells: reset has its own cell,
    while `Gueltig.akzeptiertX_iff` states the descriptor-free generator boundary.
    Pinning the whole checker detects future drift; it does not claim coverage of
    every source form or of the extra descriptor gates.
    Re-pinned 2026-11-11: `Ty.decEq` (and the two front-end equalities beside it) recurse structurally
    instead of by a size measure, which changes the closures of `8 answers`, `komp` and `AkzeptiertX`
    without changing what they decide; no component formula was touched.
    Re-pinned 2026-11-15: `AkzeptiertX` retains both invariant and contract VC gates,
    including explicit lock sources and loop hints. The ten numbered component closures
    and `komp` still match their pins, and their atoms and the appended reset cell still
    follow their definitions. No cell kind, arity or verdict changed; the new VC gates
    remain outside the numbered cell table rather than being claimed as covered cells.
    Re-pinned after integrating generic totality for fallible foreign binders, literal-true
    locks and finite traversals, its measure-duty transport, and tautological pointer
    refinement. The strict VC path and all numbered component formulas are unchanged;
    the existing 126 cells (21 bad) therefore need no new kind or constructor numbering.
    Re-pinned after naming the dependent post-translation match once. This pure
    factoring preserves the strict contract decision and all numbered cell formulas.
    Re-pinned for the approved option-indexed foreign-binder totality certificate:
    both continuations are certified for every environment, including void results.
    No strict VC rule, numbered component or cell data changed.
    Re-pinned 2026-11-16 after extending the contract control fragment,
    structural totality and decoded-local returns. The VC implementation and
    its work-budget preflight changed; the numbered components and reset cell
    above were re-read and remain unchanged. No VC coverage is claimed by
    those cells. Re-pinned after sharing decoded selections across contract
    bindings, assignments and arguments and matching the specialization scan
    to shared discarded-call continuations. These are VC implementation
    changes; the numbered components, reset cell and `komp` remain unchanged.
    The continuation-cost scan now charges tails only on reaching paths;
    this changes the VC work gate, with no numbered cell change.
    Generalizing the totality recursion's syntax indices changes its closure
    and equation layout, preserving its cases and semantic certificates.
    Loop constructor dispatch is disjoint; the inner invariant/count matches
    preserve the same certificates without dependent overlap assumptions.
    Re-pinned after reviewing constant local bindings and integer interval stores:
    both extend the proved VC gates outside the numbered cell table. The eleven
    cell formulas and their atoms remain unchanged; acceptance still conjoins
    both VC gates, as stated by `akzeptiertX_zellen`.
    The specialization scan now distinguishes domains that enumerate from
    wide constant fallback. The numbered cells and `komp` are unchanged.
    Re-pinned after reviewing certified uniform return and discarded-call
    continuations and exact constant selection before finite specialization.
    These extend the proved contract VC path; all numbered component pins,
    their atoms and the reset cell remain unchanged.
    Re-pinned 2026-11-17 after reviewing symbolic parameter/local/result environments,
    actual-world continuations, call havoc, shared discarded answers and symbolic
    measure tuples. Their certified WPs retain the all-runtime/all-world duties.
    The numbered component formulas, reset cell and `komp` remain unchanged.
    Re-reviewed for entry-world observation intervals, call-entry capture before
    havoc and equivalence-preserving VC substitution/normalization. Acceptance
    still conjoins both strict VC gates with all-world/runtime-WP certificates.
    No numbered component, reset-cell atom or constructor number changed.
    Re-reviewed for quantified oracle answers/arbitrary typed poststates and
    quantified true-annotation traversals through the original runtime WPs.
    Their work estimate changes the VC implementation closure; the numbered
    component formulas, reset-cell atom and `komp` remain unchanged.
    Re-reviewed for typed product component observations and their quantified
    parameter/result coverage. Runtime-WP soundness and all numbered cell
    formulas, reset-cell atoms and `komp` remain unchanged.
    Re-reviewed for complete finite domains of option, tagged, product and
    empty locals (`VC/Finite.lean`): only the local elimination grows; every
    numbered cell formula, reset-cell atom and `komp` remain unchanged.
    Re-reviewed for finite-domain selection in the contract checker
    (`finiteSelection`): only the selection of finite-type locals grows; every
    numbered cell formula, reset-cell atom and `komp` remain unchanged.
    Re-reviewed for option and tagged dispatch in the contract checker
    (`optionCondition`, `tagCases`): only the certified statement forms grow; every
    numbered cell formula, reset-cell atom and `komp` remain unchanged.
    Re-reviewed for `exists` over finite tables, known-option dispatch and the
    dispatch work estimate: only translation and preflight grow; every numbered
    cell formula, reset-cell atom and `komp` remain unchanged.
    Re-reviewed for unobserved values (`SymValue.unobserved`): only the contract
    checker's certified forms grow; every numbered cell formula, reset-cell atom and
    `komp` remain unchanged. -/

def erwartet : List (String × UInt64) :=
  [("0 fragment", 12310482679876591554),
   ("1 closedness", 13800082909054645524),
   ("2 footprint", 8645075724653866665),
   ("3 lock ranks", 2306745462484401830),
   ("4 lock sites", 10233556393123137737),
   ("5 roots", 17739234837013753632),
   ("6 single pool", 498286097438491847),
   ("7 race freedom", 16948703990380454043),
   ("8 answers", 17025460873829671098),
   ("9 masks", 11679533481577547307),
   ("komp", 9954942803692629413),
   ("AkzeptiertX", 1573731297096355768)]

/-- The check: every pinned definition closure has its expected hash. -/
def pruefe : MetaM Unit := do
  let env ← getEnv
  let mut fehler : List String := []
  for (label, name) in gepinnt do
    let h := huelleHash env name
    match erwartet.lookup label with
    | some e => if e != h then fehler := fehler ++ [s!"{label}: the definition changed (hash {h}, pinned {e})"]
    | none => fehler := fehler ++ [s!"{label}: not pinned (hash {h})"]
  unless fehler.isEmpty do
    throwError "the model moved under the cells of `Zellen.lean`:\n{String.intercalate "\n" fehler}\nread the component again, adjust Zellen.lean if needed, then update `erwartet` in ZellenPruefung.lean"

run_meta pruefe

end Gabbro.Grammatik.Gen.ZellenPruefung
