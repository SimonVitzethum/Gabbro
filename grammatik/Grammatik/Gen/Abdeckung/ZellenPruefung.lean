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
    every source form or of the extra descriptor gates. -/
def erwartet : List (String × UInt64) :=
  [("0 fragment", 12310482679876591554),
   ("1 closedness", 13800082909054645524),
   ("2 footprint", 8645075724653866665),
   ("3 lock ranks", 2306745462484401830),
   ("4 lock sites", 10233556393123137737),
   ("5 roots", 17739234837013753632),
   ("6 single pool", 498286097438491847),
   ("7 race freedom", 16948703990380454043),
   ("8 answers", 8026916965665620149),
   ("9 masks", 11679533481577547307),
   ("komp", 8376091305020244546),
   ("AkzeptiertX", 5966813553801955746)]

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
