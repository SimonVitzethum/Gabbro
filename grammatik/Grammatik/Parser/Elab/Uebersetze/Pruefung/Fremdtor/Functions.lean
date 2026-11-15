/- Actual function results are retained with their producer equations before
   dependent checker access. Source.lean connects them to the real assembly. -/
module
public import Grammatik.Parser.Elab.Uebersetze.Pruefung.Fremdtor.Units
public import Grammatik.Parser.Elab.UebersetzeAllg3
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
namespace Gabbro.Grammatik.Parser.Uebersetze.ForeignGateFunctions
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

-- Select the existing one-layer lowering equations instead of expanding the
-- entire mutual fuel recursion while retaining a typed function result.
private theorem foreign_seq_succ (u : UProg) (caller : Fin u.fns.length) (fuel : Nat)
    {l : Bool} (Γ : Ctx) (fn : UFn) (Λ : List (Res (declOf u)))
    (entry : AtTop u caller Λ) (statements : List UStmt) :
    lowSeqL (l := l) u caller Γ fn (fuel + 1) Λ entry statements =
      lowSeqStep u caller (lowStufe u caller fuel) Γ fn Λ entry statements := rfl

attribute [local cbv_opaque] lowStufe lowSeqL lowStructL lowEndL uFloatLimit
attribute [local cbv_eval] foreign_seq_succ lowStructL_succ lowEndL_succ
  lowStufe_seq lowStufe_struct lowStufe_ende

private def inf0 : { value : EnsTy uFremd ⟨0, by decide⟩ ×
    RumpTy uFremd ⟨0, by decide⟩ × ReqTy uFremd ⟨0, by decide⟩ //
    lowerFnAt uFremd ⟨0, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

private def inf1 : { value : EnsTy uFremd ⟨1, by decide⟩ ×
    RumpTy uFremd ⟨1, by decide⟩ × ReqTy uFremd ⟨1, by decide⟩ //
    lowerFnAt uFremd ⟨1, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

private def inf2 : { value : EnsTy uFremd ⟨2, by decide⟩ ×
    RumpTy uFremd ⟨2, by decide⟩ × ReqTy uFremd ⟨2, by decide⟩ //
    lowerFnAt uFremd ⟨2, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

private def inf3 : { value : EnsTy uFremd ⟨3, by decide⟩ ×
    RumpTy uFremd ⟨3, by decide⟩ × ReqTy uFremd ⟨3, by decide⟩ //
    lowerFnAt uFremd ⟨3, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

private def infPieces : (f : Fin 4) → EnsTy uFremd f × RumpTy uFremd f × ReqTy uFremd f :=
  Fin.cases inf0.val (Fin.cases inf1.val
    (Fin.cases inf2.val (Fin.cases inf3.val (fun f : Fin 0 => Fin.elim0 f))))

private theorem infPieces_ok (f : Fin uFremd.fns.length) :
    lowerFnAt uFremd f = .ok (infPieces f) := by
  rcases f with ⟨index, bound⟩
  have small : index < 4 := bound
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases choices with h | h | h | h
  · subst index; exact inf0.property
  · subst index; exact inf1.property
  · subst index; exact inf2.property
  · subst index; exact inf3.property

private def fall0 : { value : EnsTy uFremdFallible ⟨0, by decide⟩ ×
    RumpTy uFremdFallible ⟨0, by decide⟩ × ReqTy uFremdFallible ⟨0, by decide⟩ //
    lowerFnAt uFremdFallible ⟨0, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

private def fall1 : { value : EnsTy uFremdFallible ⟨1, by decide⟩ ×
    RumpTy uFremdFallible ⟨1, by decide⟩ × ReqTy uFremdFallible ⟨1, by decide⟩ //
    lowerFnAt uFremdFallible ⟨1, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

private def fall2 : { value : EnsTy uFremdFallible ⟨2, by decide⟩ ×
    RumpTy uFremdFallible ⟨2, by decide⟩ × ReqTy uFremdFallible ⟨2, by decide⟩ //
    lowerFnAt uFremdFallible ⟨2, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

private def fall3 : { value : EnsTy uFremdFallible ⟨3, by decide⟩ ×
    RumpTy uFremdFallible ⟨3, by decide⟩ × ReqTy uFremdFallible ⟨3, by decide⟩ //
    lowerFnAt uFremdFallible ⟨3, by decide⟩ = .ok value } := by
  refine ⟨?value, ?computed⟩
  case computed => cbv <;> (set_option smartUnfolding false in with_unfolding_all rfl)

private def fallPieces : (f : Fin 4) → EnsTy uFremdFallible f × RumpTy uFremdFallible f × ReqTy uFremdFallible f :=
  Fin.cases fall0.val (Fin.cases fall1.val
    (Fin.cases fall2.val (Fin.cases fall3.val (fun f : Fin 0 => Fin.elim0 f))))

private theorem fallPieces_ok (f : Fin uFremdFallible.fns.length) :
    lowerFnAt uFremdFallible f = .ok (fallPieces f) := by
  rcases f with ⟨index, bound⟩
  have small : index < 4 := bound
  have choices : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases choices with h | h | h | h
  · subst index; exact fall0.property
  · subst index; exact fall1.property
  · subst index; exact fall2.property
  · subst index; exact fall3.property

end Gabbro.Grammatik.Parser.Uebersetze.ForeignGateFunctions
