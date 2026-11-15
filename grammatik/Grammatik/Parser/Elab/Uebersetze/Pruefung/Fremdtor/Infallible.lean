/- The infallible foreign gate: retain each checker component as its own
   kernel-checked certificate, so one conversion never retains every reduction. -/
module

public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Fremdtor.Source
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Fremdtor.Source
import Grammatik.Logik.Vertraege.Pruefer.Witness.Selection
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
set_option pp.raw true

attribute [local irreducible] checkPFremd

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem fragment_checked :
    programmImFragmentG checkPFremd (List.finRange uFremd.fns.length) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem bounds_checked :
    abgAlleB checkPFremd (List.finRange uFremd.fns.length) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem footprints_checked :
    fussWXB checkPFremd (Cover.Differenz.sperrFamilie uFremd) (List.finRange uFremd.fns.length) [] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem levels_checked :
    stufenB checkPFremd (List.finRange uFremd.fns.length) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pool_checked :
    einzelnPoolB checkPFremd (List.finRange uFremd.fns.length) [] [] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem races_checked :
    rennB checkPFremd (List.finRange uFremd.fns.length) [] [] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem answers_checked :
    antwortenB checkPFremd (List.finRange uFremd.fns.length) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem scopes_checked :
    scopesOkProgB checkPFremd (List.finRange uFremd.fns.length) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem invariants_checked :
    Invarianten.Pruefer.programInvariantsB checkPFremd (Cover.Differenz.sperrFamilie uFremd) (List.finRange uFremd.fns.length) (fun _ => none) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem contracts_checked :
    Vertraege.Pruefer.KontrakteGeprueftB checkPFremd (Cover.Differenz.sperrFamilie uFremd) (List.finRange uFremd.fns.length) = true := by
  apply Vertraege.Pruefer.SelectionWitness.contracts_success
  rintro ⟨index, bound⟩
  kernel_change index < 4 at bound
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases choices with h | h | h | h
  all_goals subst index
  all_goals cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- End-to-end acceptance from source text with a real Duty. -/
theorem fremd_akzeptiert :
    AkzeptiertX checkPFremd (Cover.Differenz.sperrFamilie uFremd)
      (List.finRange uFremd.fns.length) [] [] [] [] checkChecksFremd = true := by
  have masks : maskenB checkPFremd (List.finRange uFremd.fns.length) = true :=
    maskenB_ohne (P := checkPFremd) (by
      delta checkPFremd
      exact lowered_no_handlers uFremd uFremd_lowered (by kernel_rfl))
  foreign_exact foreign_acceptance_of_components checkPFremd (Cover.Differenz.sperrFamilie uFremd)
    (List.finRange uFremd.fns.length) checkChecksFremd
    fragment_checked bounds_checked footprints_checked levels_checked pool_checked races_checked
    answers_checked masks
    ((schnittstellenB_iff (fun g => List.mem_finRange g)).mpr (schnittstellen_standard _ _))
    fremd_checkB scopes_checked invariants_checked contracts_checked

end Gabbro.Grammatik.Parser.Uebersetze
