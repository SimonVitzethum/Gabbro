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
import Lean
import Grammatik.Gen.Abdeckung.Zellen

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

/-- The pinned hashes (label, hash). Update them as described in the header after reading the component again. -/
def erwartet : List (String × UInt64) :=
  [("0 fragment", 11677231959375987666),
   ("1 closedness", 17262265220448277580),
   ("2 footprint", 6204145873492238965),
   ("3 lock ranks", 8867317688494790824),
   ("4 lock sites", 9116693156525816439),
   ("5 roots", 17828337562962847522),
   ("6 single pool", 16702058522406760429),
   ("7 race freedom", 5579627554436256182),
   ("8 answers", 4829398399563797823),
   ("9 masks", 12909789761629797381),
   ("komp", 17445159426705273308),
   ("AkzeptiertX", 8381758122789048558)]

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
