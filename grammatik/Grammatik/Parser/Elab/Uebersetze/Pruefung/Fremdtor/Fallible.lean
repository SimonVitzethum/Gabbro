/- The fallible foreign gate: retain each checker component as its own
   kernel-checked certificate, so one conversion never retains every reduction. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Fremdtor.Source
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Fremdtor.Source
import Grammatik.Kern.Taktik.KernelRfl
import all Init.Data.Int.Repr
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

namespace Gabbro.Grammatik.Parser.Uebersetze

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
open Gabbro.Grammatik.Zielsatz

set_option Elab.async false

#eval IO.FS.createDirAll "../.scratch-agent"

open Lean Elab Tactic in
elab "foreign_fallible_progress " label:str : tactic =>
  liftM (IO.FS.writeFile "../.scratch-agent/foreign-progress" label.getString)

attribute [local irreducible] checkPFremdFallible

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Fallible.lean:fragment_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem fragment_checked :
    programmImFragmentG checkPFremdFallible (List.finRange uFremdFallible.fns.length) = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Fallible.lean:bounds_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem bounds_checked :
    abgAlleB checkPFremdFallible (List.finRange uFremdFallible.fns.length) = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Fallible.lean:footprints_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem footprints_checked :
    fussWXB checkPFremdFallible (Cover.Differenz.sperrFamilie uFremdFallible) (List.finRange uFremdFallible.fns.length) [] = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Fallible.lean:levels_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem levels_checked :
    stufenB checkPFremdFallible (List.finRange uFremdFallible.fns.length) = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Fallible.lean:pool_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pool_checked :
    einzelnPoolB checkPFremdFallible (List.finRange uFremdFallible.fns.length) [] [] = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Fallible.lean:races_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem races_checked :
    rennB checkPFremdFallible (List.finRange uFremdFallible.fns.length) [] [] = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Fallible.lean:answers_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem answers_checked :
    antwortenB checkPFremdFallible (List.finRange uFremdFallible.fns.length) = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Fallible.lean:scopes_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem scopes_checked :
    scopesOkProgB checkPFremdFallible (List.finRange uFremdFallible.fns.length) = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Fallible.lean:invariants_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem invariants_checked :
    Invarianten.Pruefer.programInvariantsB checkPFremdFallible (Cover.Differenz.sperrFamilie uFremdFallible) (List.finRange uFremdFallible.fns.length) (fun _ => none) = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Fallible.lean:contracts_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem contracts_checked :
    Vertraege.Pruefer.KontrakteGeprueftB checkPFremdFallible (Cover.Differenz.sperrFamilie uFremdFallible) (List.finRange uFremdFallible.fns.length) = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Fallible.lean:compose"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- End-to-end acceptance from source text with a real Duty. -/
theorem fremdFallible_akzeptiert :
    AkzeptiertX checkPFremdFallible (Cover.Differenz.sperrFamilie uFremdFallible)
      (List.finRange uFremdFallible.fns.length) [] [] [] [] checkChecksFremdFallible = true := by
  have masks : maskenB checkPFremdFallible (List.finRange uFremdFallible.fns.length) = true :=
    maskenB_ohne (P := checkPFremdFallible) (by
      delta checkPFremdFallible
      exact
        lowered_no_handlers uFremdFallible uFremdFallible_lowered (by kernel_rfl))
  foreign_fallible_progress "Fallible:split"
  simp only [AkzeptiertX, Invarianten.Pruefer.invariantVCB, Bool.and_eq_true]
  foreign_fallible_progress "Fallible:and"
  and_intros
  · foreign_fallible_progress "Fallible:1"
    exact fragment_checked
  · foreign_fallible_progress "Fallible:2"
    exact bounds_checked
  · foreign_fallible_progress "Fallible:3"
    exact footprints_checked
  · foreign_fallible_progress "Fallible:4"
    exact levels_checked
  · foreign_fallible_progress "Fallible:5"
    rfl
  · foreign_fallible_progress "Fallible:6"
    rfl
  · foreign_fallible_progress "Fallible:7"
    exact pool_checked
  · foreign_fallible_progress "Fallible:8"
    exact races_checked
  · foreign_fallible_progress "Fallible:9"
    exact answers_checked
  · foreign_fallible_progress "Fallible:10"
    exact masks
  · foreign_fallible_progress "Fallible:11"
    exact (schnittstellenB_iff (fun g => List.mem_finRange g)).mpr (schnittstellen_standard _ _)
  · foreign_fallible_progress "Fallible:12"
    exact libraryB_immer _ _
  · foreign_fallible_progress "Fallible:13"
    exact Kernzelle.accumulatorB_leer
  · foreign_fallible_progress "Fallible:14"
    exact fremdFallible_checkB
  · foreign_fallible_progress "Fallible:15"
    rfl
  · foreign_fallible_progress "Fallible:16"
    exact scopes_checked
  · foreign_fallible_progress "Fallible:17"
    exact GuestBoundary.admissionB_nil
  · foreign_fallible_progress "Fallible:18"
    exact invariants_checked
  · foreign_fallible_progress "Fallible:19"
    exact contracts_checked

end Gabbro.Grammatik.Parser.Uebersetze
