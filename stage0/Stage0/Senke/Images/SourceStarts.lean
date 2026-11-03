/- Bind image roots to the selected original declarations and their canonical closed arguments. -/
module
public import Stage0.StartArgument
public import Stage0.Senke.Welt.StartEnv
@[expose] public section

namespace Gabbro.Stage0.StartArgument
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg

/-- An inherited dispatch/dynamic root has the canonical parameterless start rule. -/
structure NamedStart (u : UProg) where
  name : String
  resolved : Resolved u name []

def namedStart (u : UProg) (name : String) : Except String (NamedStart u) := do
  let resolved ← resolve u name []
  pure ⟨name, resolved⟩

/-- The explicit concurrent members remain ordered occurrences. Only the historical named
    parameterless roots are deduplicated, independently of the concurrent occurrences. -/
structure Plan (u : UProg) (items : List SItemTief) (main : (declOf u).Fn) where
  concurrent : List (SourceStart u items)
  recovered : fromItems u items = .ok concurrent
  dispatch : List String
  dispatchOrigin : uEingangsWurzeln u.fns items = .ok dispatch
  canonicalRoots : u.roots = concurrent.map (·.name) ++ dispatch
  named : List (NamedStart u)
  namedOrigin : (uOhneDoppelte (dispatch ++ u.gestartet)).mapM (namedStart u) = .ok named

def plan (u : UProg) (items : List SItemTief) (main : (declOf u).Fn) :
    Except String (Plan u items main) := do
  match hc : fromItems u items with
  | .error e => throw e
  | .ok concurrent =>
    match hd : uEingangsWurzeln u.fns items with
    | .error e => throw e
    | .ok dispatch =>
      if hr : u.roots = concurrent.map (·.name) ++ dispatch then
        match hn : (uOhneDoppelte (dispatch ++ u.gestartet)).mapM (namedStart u) with
        | .error e => throw e
        | .ok named => pure ⟨concurrent, hc, dispatch, hd, hr, named, hn⟩
      else throw "ir: concurrent source starts differ from the selected canonical roots"

/-- Canonical typed starts are passed unchanged to the image constructor. A concurrent
    occurrence of main is also a distinct thread; it is never filtered by function identity. -/
def Plan.starts {u : UProg} {items : List SItemTief} {main : (declOf u).Fn}
    (p : Plan u items main) (world : World (declOf u)) :
    List (Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f)) :=
  p.concurrent.map (fun source => source.resolved.start world) ++
    ((p.named.map (fun source => source.resolved.start world)).filter (fun start => start.1 != main))

/-- Source identity and multiplicity are attached to the same starts the constructor consumes. -/
theorem Plan.source_identity {u : UProg} {items : List SItemTief} {main : (declOf u).Fn}
    (p : Plan u items main) :
    p.concurrent.map (fun start => (start.path, start.sourceArgs)) = sourceIdentities items :=
  fromItems_identity p.recovered

theorem Plan.starts_pure {u : UProg} {items : List SItemTief} {main : (declOf u).Fn}
    (p : Plan u items main) (world world' : World (declOf u)) :
    p.starts world = p.starts world' := by
  have concurrent : p.concurrent.map (fun source => source.resolved.start world) =
      p.concurrent.map (fun source => source.resolved.start world') := by
    apply List.map_congr_left
    intro source _
    simp only [Resolved.start, source.resolved.environment_pure world world']
  have named : p.named.map (fun source => source.resolved.start world) =
      p.named.map (fun source => source.resolved.start world') := by
    apply List.map_congr_left
    intro source _
    simp only [Resolved.start, source.resolved.environment_pure world world']
  simp only [Plan.starts, concurrent, named]

/-- Every actual start carries the shared ABI's value-validity evidence, derived from
    its canonical argument rule, including the inherited parameterless named roots. -/
theorem Plan.starts_valid {u : UProg} {items : List SItemTief} {main : (declOf u).Fn}
    (p : Plan u items main) (world : World (declOf u)) (L : Senke.Lay (declOf u))
    (start : Σ f : (declOf u).Fn, Env (declOf u) ((declOf u).params f))
    (member : start ∈ p.starts world) :
    ∀ τ (x : Var ((declOf u).params start.1) τ), Senke.ValueValid L τ (start.2.get x) := by
  simp only [Plan.starts, List.mem_append, List.mem_map, List.mem_filter] at member
  rcases member with ⟨source, _, rfl⟩ | ⟨⟨source, _, rfl⟩, _⟩
  · exact Senke.startArguments_valid u _ source.sourceArgs source.resolved.checked L world
  · exact Senke.startArguments_valid u _ [] source.resolved.checked L world

end Gabbro.Stage0.StartArgument
