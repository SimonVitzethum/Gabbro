module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Pipeline
public import Grammatik.Parser.Cover.Differenz
public import Grammatik.Parser.Elab.UebersetzePipeline
@[expose] public section

namespace Gabbro.Grammatik.Parser.Measures.Fixtures
open Uebersetze UebersetzeAllg UebersetzeAllg2 Zielsatz

/-- The smallest nontrivial countdown domain: the recursive branch calls with `0 < n`. -/
def function (name callee : String) (twice : Bool := false) : UFn :=
  { name, params := [("n", .int 0 1)], kinds := [.int], res := none,
    held := [], puts := [], gives := [], ret := .empty,
    decreases := some (.variable "n"),
    body := [.ifBeg (.cmp ">" (.param "n") (.lit 0)), .call callee [.val (.lit 0)]] ++
      (if twice then [.call callee [.val (.lit 0)]] else []) ++ [.ifElse, .blkEnd] }

def countdown : UProg := { tabs := [], locks := [], fns := [function "countdown" "countdown"] }
def mutual : UProg := { tabs := [], locks := [], fns := [function "left" "right", function "right" "left"] }
def nonTail : UProg := { tabs := [], locks := [], fns := [function "branch" "branch" true] }
def acyclic : UProg :=
  { tabs := [], locks := [], fns := [{function "leaf" "leaf" with body := []}] }

/-- Original parser items, including the clause, for the countdown source fixture. -/
def countdownItems : List SItemTief :=
  [.fnT { art := "impl", name := "countdown",
      params := [("n", .range (.atom "u8") (.lit 0) (.lit 1) false)],
      res := none, fehler := none, klauseln := [.drops (.variable "n")] }
    (.block [.cond (.bin ">" (.variable "n") (.lit 0))
      (.block [.call "countdown" [.lit 0]] none) [] (some (.block [] none))]
      (some (.ret none)))]

theorem countdown_origin_zeuge : elabU countdownItems = .ok countdown := by decide +kernel

theorem countdown_lowered : (lowerAllg countdown).toOption.isSome = true := by decide +kernel
theorem mutual_lowered : (lowerAllg mutual).toOption.isSome = true := by decide +kernel
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
def mutualP := program mutual mutual_lowered
def mutualM := (exported mutual mutual_lowered).val
def nonTailP := program nonTail nonTail_lowered
def nonTailM := (exported nonTail nonTail_lowered).val
def acyclicP := program acyclic acyclic_lowered
def acyclicM := (exported acyclic acyclic_lowered).val

/-- Every fixture jointly supplies a source measure and passes the ordinary structural checker. -/
theorem countdown_accepted_zeuge :
    AkzeptiertX countP (Cover.Differenz.sperrFamilie countdown) [0] [] [] [] = true := by decide +kernel
theorem mutual_accepted_zeuge :
    AkzeptiertX mutualP (Cover.Differenz.sperrFamilie mutual) [0, 1] [] [] [] = true := by decide +kernel
theorem nonTail_accepted_zeuge :
    AkzeptiertX nonTailP (Cover.Differenz.sperrFamilie nonTail) [0] [] [] [] = true := by decide +kernel
theorem acyclic_accepted_zeuge :
    AkzeptiertX acyclicP (Cover.Differenz.sperrFamilie acyclic) [0] [] [] [] = true := by decide +kernel

theorem lowerMeasures_source_zeuge : SourceTuple countdown 0 (countM.mass 0) := countM.source 0
theorem cycleLengths_sound_zeuge : cycleLengths mutual mutualP mutualM.mass = true := by decide +kernel

end Gabbro.Grammatik.Parser.Measures.Fixtures
