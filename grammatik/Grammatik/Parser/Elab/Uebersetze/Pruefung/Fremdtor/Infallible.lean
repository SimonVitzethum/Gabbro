/- The infallible foreign gate: retain each checker component as its own
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

attribute [local irreducible] checkPFremd

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Infallible.lean:fragment_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem fragment_checked :
    programmImFragmentG checkPFremd (List.finRange uFremd.fns.length) = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Infallible.lean:bounds_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem bounds_checked :
    abgAlleB checkPFremd (List.finRange uFremd.fns.length) = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Infallible.lean:footprints_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem footprints_checked :
    fussWXB checkPFremd (Cover.Differenz.sperrFamilie uFremd) (List.finRange uFremd.fns.length) [] = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Infallible.lean:levels_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem levels_checked :
    stufenB checkPFremd (List.finRange uFremd.fns.length) = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Infallible.lean:pool_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pool_checked :
    einzelnPoolB checkPFremd (List.finRange uFremd.fns.length) [] [] = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Infallible.lean:races_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem races_checked :
    rennB checkPFremd (List.finRange uFremd.fns.length) [] [] = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Infallible.lean:answers_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem answers_checked :
    antwortenB checkPFremd (List.finRange uFremd.fns.length) = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Infallible.lean:scopes_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem scopes_checked :
    scopesOkProgB checkPFremd (List.finRange uFremd.fns.length) = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Infallible.lean:invariants_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem invariants_checked :
    Invarianten.Pruefer.programInvariantsB checkPFremd (Cover.Differenz.sperrFamilie uFremd) (List.finRange uFremd.fns.length) (fun _ => none) = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Infallible.lean:contracts_checked"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem contracts_checked :
    Vertraege.Pruefer.KontrakteGeprueftB checkPFremd (Cover.Differenz.sperrFamilie uFremd) (List.finRange uFremd.fns.length) = true := by
  decide +kernel

#eval IO.FS.writeFile "../.scratch-agent/foreign-progress" "Infallible.lean:compose"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- End-to-end acceptance from source text with a real Duty. -/
theorem fremd_akzeptiert :
    AkzeptiertX checkPFremd (Cover.Differenz.sperrFamilie uFremd)
      (List.finRange uFremd.fns.length) [] [] [] [] checkChecksFremd = true := by
  have masks : maskenB checkPFremd (List.finRange uFremd.fns.length) = true :=
    maskenB_ohne (P := checkPFremd) (by
      simpa only [checkPFremd] using
        lowered_no_handlers uFremd uFremd_lowered (by kernel_rfl))
  simp only [AkzeptiertX, Invarianten.Pruefer.invariantVCB, Bool.and_eq_true]
  and_intros
  · exact fragment_checked
  · exact bounds_checked
  · exact footprints_checked
  · exact levels_checked
  · rfl
  · rfl
  · exact pool_checked
  · exact races_checked
  · exact answers_checked
  · exact masks
  · exact (schnittstellenB_iff (fun g => List.mem_finRange g)).mpr (schnittstellen_standard _ _)
  · exact libraryB_immer _ _
  · exact Kernzelle.accumulatorB_leer
  · exact fremd_checkB
  · rfl
  · exact scopes_checked
  · exact GuestBoundary.admissionB_nil
  · exact invariants_checked
  · exact contracts_checked

end Gabbro.Grammatik.Parser.Uebersetze
