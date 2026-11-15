/- The fallible foreign gate: retain each checker component as its own
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

attribute [local irreducible] checkPFremdFallible

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem fragment_checked :
    programmImFragmentG checkPFremdFallible (List.finRange uFremdFallible.fns.length) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem bounds_checked :
    abgAlleB checkPFremdFallible (List.finRange uFremdFallible.fns.length) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem footprints_checked :
    fussWXB checkPFremdFallible (Cover.Differenz.sperrFamilie uFremdFallible) (List.finRange uFremdFallible.fns.length) [] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem levels_checked :
    stufenB checkPFremdFallible (List.finRange uFremdFallible.fns.length) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem pool_checked :
    einzelnPoolB checkPFremdFallible (List.finRange uFremdFallible.fns.length) [] [] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem races_checked :
    rennB checkPFremdFallible (List.finRange uFremdFallible.fns.length) [] [] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem answers_checked :
    antwortenB checkPFremdFallible (List.finRange uFremdFallible.fns.length) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem scopes_checked :
    scopesOkProgB checkPFremdFallible (List.finRange uFremdFallible.fns.length) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem invariants_checked :
    Invarianten.Pruefer.programInvariantsB checkPFremdFallible (Cover.Differenz.sperrFamilie uFremdFallible) (List.finRange uFremdFallible.fns.length) (fun _ => none) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem contracts_checked :
    Vertraege.Pruefer.KontrakteGeprueftB checkPFremdFallible (Cover.Differenz.sperrFamilie uFremdFallible) (List.finRange uFremdFallible.fns.length) = true := by
  apply Vertraege.Pruefer.SelectionWitness.contracts_success
  rintro ⟨index, bound⟩
  kernel_change index < 4 at bound
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases choices with h | h | h | h
  all_goals subst index
  all_goals cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

end Gabbro.Grammatik.Parser.Uebersetze
