module
public import Grammatik.Parser.Elab.UebersetzeAllg3.Measures.Duties
import all Grammatik.Parser.Elab.UebersetzeAllg3.Rest1
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

def withMeasure (measure : UMeasure) : UProg :=
  { countdown with fns := [{function "countdown" "countdown" with decreases := some measure}] }

def unequalCycle : UProg :=
  { mutualU with fns := [function "left" "right", {function "right" "left" with decreases := none}] }

def unchanged : UProg :=
  { tabs := [], locks := [], fns := [{function "stay" "stay" with body := [.call "stay" [.val (.param "n")]]}] }
def increasing : UProg :=
  { tabs := [], locks := [], fns := [{function "grow" "grow" with needs := [.cmp "==" (.param "n") (.lit 0)], body := [.call "grow" [.val (.lit 1)]]}] }

instance : NeZero unchanged.fns.length := ⟨by decide⟩
instance : NeZero increasing.fns.length := ⟨by decide⟩

theorem unchanged_lowered : (lowerAllg unchanged).toOption.isSome = true := by decide +kernel
theorem increasing_lowered : (lowerAllg increasing).toOption.isSome = true := by decide +kernel

def unchangedP := program unchanged unchanged_lowered
def unchangedM := (exported unchanged unchanged_lowered).val
def increasingP := program increasing increasing_lowered
def increasingM := (exported increasing increasing_lowered).val

private def unchangedBody : RumpTy unchanged 0 :=
  .cons (.call 0 (.cons (.widen (by decide) (by decide) (.var .here)) .nil)
    (rufPasstB_ok (u := unchanged) (by decide)) (by rfl)) (.ret .empty (List.Perm.refl []))

private def increasingBody : RumpTy increasing 0 :=
  .cons (.call 0 (.cons (.widen (by decide) (by decide) (.lit 1)) .nil)
    (rufPasstB_ok (u := increasing) (by decide)) (by rfl)) (.ret .empty (List.Perm.refl []))

set_option maxRecDepth 100000 in
private theorem unchanged_function : lowerFnAt unchanged 0 = .ok (.tru, unchangedBody, .tru) := by with_unfolding_all rfl

set_option maxRecDepth 100000 in
private theorem increasing_function :
    lowerFnAt increasing 0 = .ok (.tru, increasingBody, .eq (.var .here) (.lit 0)) := by with_unfolding_all rfl

private theorem unchangedP_rumpf : unchangedP.rumpf 0 = unchangedBody :=
  program_rumpf_of_lowerFn unchanged_function

private theorem increasingP_rumpf : increasingP.rumpf 0 = increasingBody :=
  program_rumpf_of_lowerFn increasing_function

private theorem unchangedP_requires : unchangedP.requires 0 = .tru :=
  program_requires_of_lowerFn unchanged_function

private theorem increasingP_requires : increasingP.requires 0 = .eq (.var .here) (.lit 0) :=
  program_requires_of_lowerFn increasing_function

private theorem unchanged_cycle : zykS unchangedP [0] 0 0 = true := by
  simp only [zykS, zyklusMit, reachB, erreichB, erreichSchritt, ruftB, unchangedP_rumpf]
  rfl

private theorem increasing_cycle : zykS increasingP [0] 0 0 = true := by
  simp only [zykS, zyklusMit, reachB, erreichB, erreichSchritt, ruftB, increasingP_rumpf]
  rfl

set_option maxRecDepth 100000 in
private theorem unchangedM_mass : unchangedM.mass 0 =
    [⟨1, .widen (by decide) (by decide) (.var .here), rfl⟩] := by rfl

set_option maxRecDepth 100000 in
private theorem increasingM_mass : increasingM.mass 0 =
    [⟨1, .widen (by decide) (by decide) (.var .here), rfl⟩] := by rfl

/-- Division over a positive denominator lowers with an empty footprint. -/
def divU : UProg := withMeasure (.bin "/" (.variable "n") (.lit 1))
instance : NeZero divU.fns.length := ⟨by decide⟩
theorem divLowered : (lowerAllg divU).toOption.isSome = true := by decide +kernel
def divM := (exported divU divLowered).val
theorem divSource : SourceTuple divU 0 (divM.mass 0) := divM.source 0
theorem divDenotes :
    ∃ c : Component divU 0, divM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf divU)) (env : Env (declOf divU) ((declOf divU).params 0)),
        SourceValue (fnAt divU 0) (fnAt divU 0).measureConstants env
          (.bin "/" (.variable "n") (.lit 1)) (eval initial c.2.1 state env).n :=
  lowerMeasures_denotes divU divM 0 [] [.drops (.bin "/" (.variable "n") (.lit 1))]
    (.bin "/" (.variable "n") (.lit 1)) (.bin "/" (.variable "n") (.lit 1)) rfl rfl rfl

/-- Remainder over a positive denominator lowers with an empty footprint. -/
def remU : UProg := withMeasure (.bin "%" (.variable "n") (.lit 2))
instance : NeZero remU.fns.length := ⟨by decide⟩
theorem remLowered : (lowerAllg remU).toOption.isSome = true := by decide +kernel
def remM := (exported remU remLowered).val
theorem remSource : SourceTuple remU 0 (remM.mass 0) := remM.source 0
theorem remDenotes :
    ∃ c : Component remU 0, remM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf remU)) (env : Env (declOf remU) ((declOf remU).params 0)),
        SourceValue (fnAt remU 0) (fnAt remU 0).measureConstants env
          (.bin "%" (.variable "n") (.lit 2)) (eval initial c.2.1 state env).n :=
  lowerMeasures_denotes remU remM 0 [] [.drops (.bin "%" (.variable "n") (.lit 2))]
    (.bin "%" (.variable "n") (.lit 2)) (.bin "%" (.variable "n") (.lit 2)) rfl rfl rfl

/-- Bitwise and over non-negative ranges lowers with an empty footprint. -/
def andU : UProg := withMeasure (.bin "&" (.variable "n") (.lit 1))
instance : NeZero andU.fns.length := ⟨by decide⟩
theorem andLowered : (lowerAllg andU).toOption.isSome = true := by decide +kernel
def andM := (exported andU andLowered).val
theorem andSource : SourceTuple andU 0 (andM.mass 0) := andM.source 0
theorem andDenotes :
    ∃ c : Component andU 0, andM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf andU)) (env : Env (declOf andU) ((declOf andU).params 0)),
        SourceValue (fnAt andU 0) (fnAt andU 0).measureConstants env
          (.bin "&" (.variable "n") (.lit 1)) (eval initial c.2.1 state env).n :=
  lowerMeasures_denotes andU andM 0 [] [.drops (.bin "&" (.variable "n") (.lit 1))]
    (.bin "&" (.variable "n") (.lit 1)) (.bin "&" (.variable "n") (.lit 1)) rfl rfl rfl

/-- Bitwise or over non-negative ranges lowers with an empty footprint. -/
def orU : UProg := withMeasure (.bin "|" (.variable "n") (.lit 1))
instance : NeZero orU.fns.length := ⟨by decide⟩
theorem orLowered : (lowerAllg orU).toOption.isSome = true := by decide +kernel
def orM := (exported orU orLowered).val
theorem orSource : SourceTuple orU 0 (orM.mass 0) := orM.source 0
theorem orDenotes :
    ∃ c : Component orU 0, orM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf orU)) (env : Env (declOf orU) ((declOf orU).params 0)),
        SourceValue (fnAt orU 0) (fnAt orU 0).measureConstants env
          (.bin "|" (.variable "n") (.lit 1)) (eval initial c.2.1 state env).n :=
  lowerMeasures_denotes orU orM 0 [] [.drops (.bin "|" (.variable "n") (.lit 1))]
    (.bin "|" (.variable "n") (.lit 1)) (.bin "|" (.variable "n") (.lit 1)) rfl rfl rfl

/-- Bitwise xor over non-negative ranges lowers with an empty footprint. -/
def xorU : UProg := withMeasure (.bin "^" (.variable "n") (.lit 1))
instance : NeZero xorU.fns.length := ⟨by decide⟩
theorem xorLowered : (lowerAllg xorU).toOption.isSome = true := by decide +kernel
def xorM := (exported xorU xorLowered).val
theorem xorSource : SourceTuple xorU 0 (xorM.mass 0) := xorM.source 0
theorem xorDenotes :
    ∃ c : Component xorU 0, xorM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf xorU)) (env : Env (declOf xorU) ((declOf xorU).params 0)),
        SourceValue (fnAt xorU 0) (fnAt xorU 0).measureConstants env
          (.bin "^" (.variable "n") (.lit 1)) (eval initial c.2.1 state env).n :=
  lowerMeasures_denotes xorU xorM 0 [] [.drops (.bin "^" (.variable "n") (.lit 1))]
    (.bin "^" (.variable "n") (.lit 1)) (.bin "^" (.variable "n") (.lit 1)) rfl rfl rfl

/-- Shift left over non-negative ranges lowers with an empty footprint. -/
def shlU : UProg := withMeasure (.bin "<<" (.variable "n") (.lit 1))
instance : NeZero shlU.fns.length := ⟨by decide⟩
theorem shlLowered : (lowerAllg shlU).toOption.isSome = true := by decide +kernel
def shlM := (exported shlU shlLowered).val
theorem shlSource : SourceTuple shlU 0 (shlM.mass 0) := shlM.source 0
theorem shlDenotes :
    ∃ c : Component shlU 0, shlM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf shlU)) (env : Env (declOf shlU) ((declOf shlU).params 0)),
        SourceValue (fnAt shlU 0) (fnAt shlU 0).measureConstants env
          (.bin "<<" (.variable "n") (.lit 1)) (eval initial c.2.1 state env).n :=
  lowerMeasures_denotes shlU shlM 0 [] [.drops (.bin "<<" (.variable "n") (.lit 1))]
    (.bin "<<" (.variable "n") (.lit 1)) (.bin "<<" (.variable "n") (.lit 1)) rfl rfl rfl

/-- Shift right over non-negative ranges lowers with an empty footprint. -/
def shrU : UProg := withMeasure (.bin ">>" (.variable "n") (.lit 1))
instance : NeZero shrU.fns.length := ⟨by decide⟩
theorem shrLowered : (lowerAllg shrU).toOption.isSome = true := by decide +kernel
def shrM := (exported shrU shrLowered).val
theorem shrSource : SourceTuple shrU 0 (shrM.mass 0) := shrM.source 0
theorem shrDenotes :
    ∃ c : Component shrU 0, shrM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf shrU)) (env : Env (declOf shrU) ((declOf shrU).params 0)),
        SourceValue (fnAt shrU 0) (fnAt shrU 0).measureConstants env
          (.bin ">>" (.variable "n") (.lit 1)) (eval initial c.2.1 state env).n :=
  lowerMeasures_denotes shrU shrM 0 [] [.drops (.bin ">>" (.variable "n") (.lit 1))]
    (.bin ">>" (.variable "n") (.lit 1)) (.bin ">>" (.variable "n") (.lit 1)) rfl rfl rfl

/-- A conversion through a built-in width lowers with an empty footprint. -/
def convU : UProg := withMeasure (.conv "u8" (.variable "n"))
instance : NeZero convU.fns.length := ⟨by decide⟩
theorem convLowered : (lowerAllg convU).toOption.isSome = true := by decide +kernel
def convM := (exported convU convLowered).val
theorem convSource : SourceTuple convU 0 (convM.mass 0) := convM.source 0
theorem convDenotes :
    ∃ c : Component convU 0, convM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf convU)) (env : Env (declOf convU) ((declOf convU).params 0)),
        SourceValue (fnAt convU 0) (fnAt convU 0).measureConstants env
          (.call "u8" [.variable "n"]) (eval initial c.2.1 state env).n :=
  lowerMeasures_denotes convU convM 0 [] [.drops (.call "u8" [.variable "n"])]
    (.call "u8" [.variable "n"]) (.conv "u8" (.variable "n")) rfl rfl rfl

/-- A conversion through a unit alias lowers once the alias scope travels with the function. -/
def convAliasU : UProg := { countdown with fns :=
  [{function "countdown" "countdown" with decreases := some (.conv "A" (.variable "n")), measureTypes := [("A", (0, 7))]}] }
instance : NeZero convAliasU.fns.length := ⟨by decide⟩
theorem convAliasLowered : (lowerAllg convAliasU).toOption.isSome = true := by decide +kernel
def convAliasM := (exported convAliasU convAliasLowered).val
theorem convAliasSource : SourceTuple convAliasU 0 (convAliasM.mass 0) := convAliasM.source 0
theorem convAliasDenotes :
    ∃ c : Component convAliasU 0, convAliasM.mass 0 = [c] ∧
      ∀ (initial state : World (declOf convAliasU))
        (env : Env (declOf convAliasU) ((declOf convAliasU).params 0)),
        SourceValue (fnAt convAliasU 0) (fnAt convAliasU 0).measureConstants env
          (.call "A" [.variable "n"]) (eval initial c.2.1 state env).n :=
  lowerMeasures_denotes convAliasU convAliasM 0 [("A", (0, 7))]
    [.drops (.call "A" [.variable "n"])]
    (.call "A" [.variable "n"]) (.conv "A" (.variable "n")) rfl rfl rfl

end Gabbro.Grammatik.Parser.Measures.Fixtures
