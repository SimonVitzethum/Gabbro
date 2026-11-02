module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Pipeline
public import Grammatik.Parser.Elab.UebersetzeAllg3.TransitionCert
public import Grammatik.Parser.Cover.Differenz
public import Grammatik.Parser.Elab.UebersetzePipeline
import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice
@[expose] public section

namespace Gabbro.Grammatik.Parser.Measures.Fixtures
open Uebersetze UebersetzeAllg UebersetzeAllg2 Zielsatz

/-- The smallest nontrivial countdown domain: the recursive branch calls with `0 < n`. -/
def function (name callee : String) (twice : Bool := false) : UFn :=
  { name, params := [("n", .int 0 1)], kinds := [.int], res := none, held := [], puts := [], gives := [], ret := .empty, decreases := some (.variable "n"), body := [.ifBeg (.cmp ">" (.param "n") (.lit 0)), .call callee [.val (.lit 0)]] ++ (if twice then [.call callee [.val (.lit 0)]] else []) ++ [.ifElse, .blkEnd] }

def countdown : UProg := { tabs := [], locks := [], fns := [function "countdown" "countdown"] }
def mutualU : UProg := { tabs := [], locks := [], fns := [function "left" "right", function "right" "left"] }
def nonTail : UProg := { tabs := [], locks := [], fns := [function "branch" "branch" true] }
def acyclic : UProg :=
  { tabs := [], locks := [], fns := [{function "leaf" "leaf" with body := []}] }

/-- Function numerals of the fixtures (`(declOf u).Fn` is `Fin u.fns.length`). -/
instance (u : UProg) (n : Nat) [NeZero u.fns.length] : OfNat (declOf u).Fn n :=
  inferInstanceAs (OfNat (Fin u.fns.length) n)
instance : NeZero countdown.fns.length := ⟨by decide⟩
instance : NeZero mutualU.fns.length := ⟨by decide⟩
instance : NeZero nonTail.fns.length := ⟨by decide⟩
instance : NeZero acyclic.fns.length := ⟨by decide⟩

/-- Original parser items, including the clause, for the countdown source fixture. -/
def countdownItems : List SItemTief :=
  [.fnT { art := "impl", name := "countdown", params := [("n", .range (.atom "u8") (.lit 0) (.lit 1) false)], res := none, fehler := none, klauseln := [.drops (.variable "n")] }
    (.block [.cond (.bin ">" (.variable "n") (.lit 0))
      (.block [.call "countdown" [.lit 0]] none) [] (some (.block [] none))]
      (some (.ret none)))]

/-- The source clause reaches the elaborated function as exactly the written measure. -/
theorem countdown_origin_zeuge :
    (elabU countdownItems).toOption.map (fun u => u.fns.map (·.decreases)) =
      some [some (.variable "n")] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The complete elaborated fixture, not only its measure projection, comes from these items. -/
theorem countdown_elaborated_zeuge : elabU countdownItems = .ok countdown := by decide +kernel

theorem countdown_lowered : (lowerAllg countdown).toOption.isSome = true := by decide +kernel
theorem mutual_lowered : (lowerAllg mutualU).toOption.isSome = true := by decide +kernel
theorem nonTail_lowered : (lowerAllg nonTail).toOption.isSome = true := by decide +kernel
theorem acyclic_lowered : (lowerAllg acyclic).toOption.isSome = true := by decide +kernel

def program (u : UProg) (lowered : (lowerAllg u).toOption.isSome = true) : Programm (declOf u) :=
  ((lowerAllg u).toOption.get lowered).1

/-- Recover a concrete body through the generic lowering certificate, without reducing program assembly. -/
theorem program_rumpf_of_lowerFn {u : UProg} {lowered : (lowerAllg u).toOption.isSome = true}
    {f : (declOf u).Fn} {ens : EnsTy u f} {body : RumpTy u f} {req : ReqTy u f}
    (functionLowered : lowerFnAt u f = .ok (ens, body, req)) :
    (program u lowered).rumpf f = body := by
  obtain ⟨value, origin, _, bodyEq, _⟩ := lowerAllg_fields u (program u lowered)
    ((lowerAllg u).toOption.get lowered).2 (except_ok_get lowered) f
  rw [functionLowered] at origin
  cases origin
  exact bodyEq

/-- The requires projection also follows the ordinary assembler, including the empty-clause case. -/
theorem program_requires_of_lowerFn {u : UProg} {lowered : (lowerAllg u).toOption.isSome = true}
    {f : (declOf u).Fn} {ens : EnsTy u f} {body : RumpTy u f} {req : ReqTy u f}
    (functionLowered : lowerFnAt u f = .ok (ens, body, req)) :
    (program u lowered).requires f = if (fnAt u f).needs = [] then .tru else req := by
  have success := except_ok_get lowered
  change lowerAllg u = .ok (program u lowered, ((lowerAllg u).toOption.get lowered).2) at success
  unfold lowerAllg at success
  split at success
  · cases success
  · split at success
    · cases success
    · split at success
      · obtain ⟨same, _⟩ := checkedProgram_eq success
        rw [same]
        simp only [progOfFn, reqOf, lowerAtPair_of_ok u f _ functionLowered]
      · cases success

def exported (u : UProg) (lowered : (lowerAllg u).toOption.isSome = true) :
    {measure : Export u // lowerMeasures u = .ok measure} :=
  checkedExport u (by
    have hl := except_ok_get lowered
    obtain ⟨m, origin, _⟩ := lowerAllg_measures u _ _ hl
    exact ⟨m, origin⟩)

def countP := program countdown countdown_lowered
def countM := (exported countdown countdown_lowered).val
def mutualP := program mutualU mutual_lowered
def mutualM := (exported mutualU mutual_lowered).val
def nonTailP := program nonTail nonTail_lowered
def nonTailM := (exported nonTail nonTail_lowered).val
def acyclicP := program acyclic acyclic_lowered
def acyclicM := (exported acyclic acyclic_lowered).val

/-- Every fixture jointly supplies a source measure and passes the ordinary structural checker. -/
theorem countdown_accepted_zeuge :
    AkzeptiertX countP (Cover.Differenz.sperrFamilie countdown) [⟨0, by decide⟩] [] [] [] = true := by decide +kernel
theorem mutual_accepted_zeuge :
    AkzeptiertX mutualP (Cover.Differenz.sperrFamilie mutualU) [⟨0, by decide⟩, ⟨1, by decide⟩] [] [] [] = true := by decide +kernel
theorem nonTail_accepted_zeuge :
    AkzeptiertX nonTailP (Cover.Differenz.sperrFamilie nonTail) [⟨0, by decide⟩] [] [] [] = true := by decide +kernel
theorem acyclic_accepted_zeuge :
    AkzeptiertX acyclicP (Cover.Differenz.sperrFamilie acyclic) [⟨0, by decide⟩] [] [] [] = true := by decide +kernel

theorem lowerMeasures_source_zeuge : SourceTuple countdown ⟨0, by decide⟩ (countM.mass ⟨0, by decide⟩) := countM.source ⟨0, by decide⟩
theorem cycleLengths_sound_zeuge : cycleLengths mutualU mutualP mutualM.mass = true := by decide +kernel

end Gabbro.Grammatik.Parser.Measures.Fixtures
