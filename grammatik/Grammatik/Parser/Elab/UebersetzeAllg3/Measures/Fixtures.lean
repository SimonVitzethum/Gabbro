module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Pipeline
public import Grammatik.Parser.Cover.Differenz
public import Grammatik.Parser.Elab.UebersetzePipeline
@[expose] public section

namespace Gabbro.Grammatik.Parser.Measures.Fixtures
open Uebersetze UebersetzeAllg UebersetzeAllg2 Zielsatz

/-- The smallest nontrivial countdown domain: the recursive branch calls with `0 < n`. -/
def function (name callee : String) (twice : Bool := false) : UFn :=
  { name, params := [("n", .int 0 1)], kinds := [.int], res := none, held := [], puts := [], gives := [], ret := .empty, decreases := some (.variable "n"), body := [.ifBeg (.cmp ">" (.param "n") (.lit 0)), .call callee [.val (.lit 0)]] ++
      (if twice then [.call callee [.val (.lit 0)]] else []) ++ [.ifElse, .blkEnd] }

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

theorem countdown_lowered : (lowerAllg countdown).toOption.isSome = true := by decide +kernel
theorem mutual_lowered : (lowerAllg mutualU).toOption.isSome = true := by decide +kernel
theorem nonTail_lowered : (lowerAllg nonTail).toOption.isSome = true := by decide +kernel
theorem acyclic_lowered : (lowerAllg acyclic).toOption.isSome = true := by decide +kernel

def program (u : UProg) (lowered : (lowerAllg u).toOption.isSome = true) : Programm (declOf u) :=
  ((lowerAllg u).toOption.get lowered).1

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
