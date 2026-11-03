/-
  File:      Grammatik/Parser/Elab/UebersetzeAllg3.lean
  Subject:   T3 PART 7: generic lowering, third part: statement runs (`lowSeqL`: `let`, `locks`, `if`,
             `traverse`, early `return`), bodies, `lowerAllg`, and the 104/108 pins and the chain.
             Split from `UebersetzeAllg2` (which keeps the single statements and calls); same namespace.
-/
module

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
public import Grammatik.Parser.Elab.Export.ExportControl
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Parser.Namen.Oeffentlich
import all Init.Data.Repr
@[expose] public section


namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

/-! ## Returns -/

/-- The value of a return, at the current resources `Λ`. -/
def lowErg (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) : URet →
    Except String (ErgExpr (declOf u) Γ Λ (verOf u caller).erg)
  | .keins => .error "fn with a result falls off"
  | .empty =>
    match hE : (fnAt u caller).ergTy with
    | none =>
      have hV : (verOf u caller).erg = none := by
        show (vertragVon (declOf u) caller).erg = none
        rw [vErg_eq u caller, hE]
      have eK : ErgExpr (declOf u) Γ Λ (verOf u caller).erg := by
        rw [hV]
        exact ErgExpr.empty
      .ok eK
    | some _ => .error "return without value with result"
  | .val s =>
    match hE : (fnAt u caller).ergTy with
    | some (.int lo hi) =>
      match lowWertAt u Γ Λ fn lo hi s with
      | .error e => .error e
      | .ok v =>
        have eW : ErgExpr (declOf u) Γ Λ (verOf u caller).erg := by
          rw [show (verOf u caller).erg =
            (vertragVon (declOf u) caller).erg from rfl,
            vErg_eq u caller, hE]
          show ErgExpr (declOf u) Γ Λ (Option.some (.int lo hi))
          exact ErgExpr.val v
        .ok eW
    | some _ => .error "number returned for a non-number result"
    | none => .error "return with value without result"
  | .why _ => .error "reason as a value without G form"
  | .wert s =>
    match hE : (fnAt u caller).ergTy with
    | some τ =>
      match lowWertAtE u Γ Λ fn none τ s with
      | .error e => .error e
      | .ok v =>
        have eW : ErgExpr (declOf u) Γ Λ (verOf u caller).erg := by
          rw [show (verOf u caller).erg =
            (vertragVon (declOf u) caller).erg from rfl,
            vErg_eq u caller, hE]
          exact ErgExpr.val v
        .ok eW
    | none => .error "return with value without result"
  | .grund g =>
    match hE : (fnAt u caller).ergTy with
    | some (.why n) =>
      match lowGrund u Γ Λ fn n g with
      | .error e => .error e
      | .ok v =>
        have eW : ErgExpr (declOf u) Γ Λ (verOf u caller).erg := by
          rw [show (verOf u caller).erg =
            (vertragVon (declOf u) caller).erg from rfl,
            vErg_eq u caller, hE]
          exact ErgExpr.val v
        .ok eW
    | some _ => .error "reason returned for a non-reason result"
    | none => .error "return with value without result"
  | .sum v =>
    match hE : (fnAt u caller).ergTy with
    | some (.sum cs) =>
      match (fnAt u caller).resSum with
      | some (sidx, _) =>
        if hs : sidx < u.sums.length then
          if hc : (u.sums.get ⟨sidx, hs⟩).spec = cs then
            match lowSVal u Γ Λ fn 0 sidx hs v with
            | .error e => .error e
            | .ok ev =>
              have eW : ErgExpr (declOf u) Γ Λ (verOf u caller).erg := by
                rw [show (verOf u caller).erg =
                  (vertragVon (declOf u) caller).erg from rfl,
                  vErg_eq u caller, hE]
                show ErgExpr (declOf u) Γ Λ (Option.some (.sum cs))
                exact ErgExpr.val (by rw [← hc]; exact ev)
              .ok eW
          else .error "result type foreign"
        else .error "tagged type unknown"
      | none => .error "tagged result without type"
    | some _ => .error "tagged value returned for a different result"
    | none => .error "return with value without result"
  | .opt o =>
    match hE : (fnAt u caller).ergTy with
    | some (.opt n) =>
      match (fnAt u caller).resOpt with
      | some (num, _) =>
        if hnum : num < u.tabs.length then
          if hn : (declOf u).count ⟨num, hnum⟩ = n then
            match lowOpt u Γ Λ fn 0 num hnum o with
            | .error e => .error e
            | .ok v =>
              have eW : ErgExpr (declOf u) Γ Λ (verOf u caller).erg := by
                rw [show (verOf u caller).erg =
                  (vertragVon (declOf u) caller).erg from rfl,
                  vErg_eq u caller, hE]
                show ErgExpr (declOf u) Γ Λ (Option.some (.opt n))
                exact ErgExpr.val (by rw [← hn]; exact v)
              .ok eW
          else .error "option result table foreign"
        else .error "option table unknown"
      | none => .error "option result without table"
    | some _ => .error "option returned for a non-option result"
    | none => .error "return with value without result"
  | .bool b =>
    match hE : (fnAt u caller).ergTy with
    | some .bool =>
      match lowEns u Γ Λ fn none b with
      | .error e => .error e
      | .ok v =>
        have eW : ErgExpr (declOf u) Γ Λ (verOf u caller).erg := by
          rw [show (verOf u caller).erg =
            (vertragVon (declOf u) caller).erg from rfl,
            vErg_eq u caller, hE]
          exact ErgExpr.val v
        .ok eW
    | some _ => .error "truth value returned for a non-bool result"
    | none => .error "return with value without result"

/-- The return a body ends with when every path already ended (`URet.keins`, set by the elaborator only then,
    `uEndetTief`): unreachable, so any value of the result type; refused where none is at hand. -/
def keinsWert : Option Ty → Option URet
  | some (.int lo _) => some (.val (.lit lo))
  | some (.opt _) => some (.opt .nichts)
  | some .bool => some (.bool .fls)
  | _ => none

/-- The trailing return. The current resources must be the contract end up to
    order (C16): a body that consumed or produced marks ends where the flow leaves it. -/
def lowEnd (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (r0 : URet) :
    Except String (Endblock (declOf u) (verOf u caller) false Γ Λ) :=
  let r := match r0 with
    | .keins => (keinsWert (fnAt u caller).ergTy).getD .keins
    | r => r
  match r with
  | .why i =>
    if h : i < (verOf u caller).gruende then
      if hPerm : decide (Λ.Perm (verOf u caller).ende) = true then
        .ok (Endblock.retWhy (D := declOf u) ⟨i, h⟩ (of_decide_eq_true hPerm))
      else .error "lower: return without produced marks"
    else .error "reason case outside the channel"
  | _ =>
  match lowErg u caller Γ Λ fn r with
  | .error e => .error e
  | .ok e =>
    if hPerm : decide (Λ.Perm (verOf u caller).ende) = true then
      .ok (Endblock.ret e (of_decide_eq_true hPerm))
    else .error "lower: return without produced marks"

/-- Lexically acquired locks, innermost first. Signature locks are absent: a
    return must preserve them in the contract end rather than release them. -/
abbrev AtTop (u : UProg) (_caller : Fin u.fns.length) (_ : List (Res (declOf u))) : Type :=
  List (declOf u).Lock

/-- Check the exact residual resources with precisely the lexical cleanup list.
    Owner marks and inherited locks cannot be inferred as disposable resources. -/
def lowReturnResources (u : UProg) (caller : Fin u.fns.length)
    (Λ : List (Res (declOf u))) (scopes : AtTop u caller Λ) :
    Except String (RueckRessourcen (declOf u) (verOf u caller) Λ) :=
  if h : decide (Λ.Perm ((verOf u caller).ende ++ scopes.map Res.held)) = true then
    .ok ⟨scopes, of_decide_eq_true h⟩
  else .error "lower: scoped return without exact contract-end resources and lexical locks"

/-- A return keeps the ordinary exact-return form outside local lock scopes. -/
def lowRetStmt {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (pe : AtTop u caller Λ) (r : URet) :
    Except String (Stmt (declOf u) (verOf u caller) l Γ Λ Λ) :=
  match pe with
  | [] =>
    match r with
    | .why i =>
      if hi : i < (verOf u caller).gruende then
        if hPerm : decide (Λ.Perm (verOf u caller).ende) = true then
          .ok (Stmt.retWhy (D := declOf u) ⟨i, hi⟩ (of_decide_eq_true hPerm))
        else .error "lower: return without produced marks"
      else .error "reason case outside the channel"
    | _ =>
      (lowErg u caller Γ Λ fn r).bind fun erg =>
        if hPerm : decide (Λ.Perm (verOf u caller).ende) = true then
          .ok (Stmt.ret erg (of_decide_eq_true hPerm))
        else .error "lower: return without produced marks"
  | _ :: _ =>
    (lowReturnResources u caller Λ pe).bind fun resources =>
      match r with
      | .why i =>
        if hi : i < (verOf u caller).gruende then
          .ok (Stmt.retWhyScoped (D := declOf u) ⟨i, hi⟩ resources)
        else .error "reason case outside the channel"
      | _ => (lowErg u caller Γ Λ fn r).map fun erg => Stmt.retScoped erg resources

/-- The same return checks in an explicit ending branch. -/
def lowRetEnd {l : Bool} (u : UProg) (caller : Fin u.fns.length) (Γ : Ctx) (fn : UFn)
    (Λ : List (Res (declOf u))) (pe : AtTop u caller Λ) (r : URet) :
    Except String (Endblock (declOf u) (verOf u caller) l Γ Λ) :=
  match pe with
  | [] =>
    match r with
    | .why i =>
      if hi : i < (verOf u caller).gruende then
        if hPerm : decide (Λ.Perm (verOf u caller).ende) = true then
          .ok (Endblock.retWhy (D := declOf u) ⟨i, hi⟩ (of_decide_eq_true hPerm))
        else .error "lower: return without produced marks"
      else .error "reason case outside the channel"
    | _ =>
      (lowErg u caller Γ Λ fn r).bind fun erg =>
        if hPerm : decide (Λ.Perm (verOf u caller).ende) = true then
          .ok (Endblock.ret erg (of_decide_eq_true hPerm))
        else .error "lower: return without produced marks"
  | _ :: _ =>
    (lowReturnResources u caller Λ pe).bind fun resources =>
      match r with
      | .why i =>
        if hi : i < (verOf u caller).gruende then
          .ok (Endblock.retWhyScoped (D := declOf u) ⟨i, hi⟩ resources)
        else .error "reason case outside the channel"
      | _ => (lowErg u caller Γ Λ fn r).map fun erg => Endblock.retScoped erg resources

end Gabbro.Grammatik.Parser.UebersetzeAllg2
