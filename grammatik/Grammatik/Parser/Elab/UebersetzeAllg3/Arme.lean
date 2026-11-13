module

public import Grammatik.Parser.Elab.Export.ExportControl
public import Grammatik.Parser.Elab.UebersetzeSum
public import Grammatik.Bausteine.Arena.ArenaZucker
public import Grammatik.Parser.Namen.Oeffentlich
import all Init.Data.Repr
import all Init.Data.String.Defs
import all Init.Data.String.Basic
public import Grammatik.Parser.Elab.UebersetzeAllg3.Kopf

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg2

open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

set_option maxRecDepth 100000

/-- The arms of a tagged match: one block per case of the specification, the payload of a case with one bound by
    the next binder name, separated by `ifElse`; the marker that closes the match is left to the caller. -/
def lowArmsStep {l : Bool} (u : UProg) (caller : Fin u.fns.length) (R : LowStufe u caller) :
    (Γ : Ctx) → UFn → (Λ : List (Res (declOf u))) → AtTop u caller Λ →
    (cs : List (Option Ty)) → List String → List UStmt →
    Except String (Arms (declOf u) (verOf u caller) l Γ Λ Λ cs × List UStmt)
  | _, _, _, _, [], _, rest => .ok (Arms.nil, rest)
  | Γ, fn, Λ, pe, none :: cs', bs, rest =>
    (R.seq (l := l) Γ fn Λ pe rest).bind fun (⟨Λ₁, b⟩, r) => match cs' with
      | [] =>
        if h : Λ₁ = Λ then
          .ok (Arms.cons (by subst h; exact b) Arms.nil, r)
        else .error "lower: a match arm changes held marks"
      | c' :: cs'' => match r with
        | .ifElse :: r' =>
          (R.arms (l := l) Γ fn Λ pe (c' :: cs'') (bs.drop 1) r').bind fun (arms, r2) =>
            if h₁ : Λ₁ = Λ then
              .ok (Arms.cons (by subst h₁; exact b) arms, r2)
            else .error "lower: a match arm changes held marks"
        | _ => .error "lower: a match has fewer arms than cases"
  | Γ, fn, Λ, pe, some τ :: cs', bs, rest =>
    -- Retain the same option identity as the source arm; lowOpt checks this kind again.
    let scope := match τ with
      | .opt count =>
        match uOptionTabelle u.tabs count with
        | some num => fn.mitOpt (bs.headD "") num count
        | none => fn.mitTy (bs.headD "") τ
      | _ => fn.mitTy (bs.headD "") τ
    (R.seq (l := l) (τ :: Γ) scope Λ pe rest).bind fun (⟨Λ₁, b⟩, r) =>
      match cs' with
      | [] =>
        if h : Λ₁ = Λ then
          .ok (Arms.cons (by subst h; exact b) Arms.nil, r)
        else .error "lower: a match arm changes held marks"
      | c' :: cs'' => match r with
        | .ifElse :: r' =>
          (R.arms (l := l) Γ fn Λ pe (c' :: cs'') (bs.drop 1) r').bind fun (arms, r2) =>
            if h₁ : Λ₁ = Λ then
              .ok (Arms.cons (by subst h₁; exact b) arms, r2)
            else .error "lower: a match arm changes held marks"
        | _ => .error "lower: a match has fewer arms than cases"

/-- The arms of a reason match: `m` blocks, one per reason, separated by `ifElse`; the marker that closes the
    match is left to the caller. Like `Arms`, reason arms preserve the list. -/
def lowGArmsStep {l : Bool} (u : UProg) (caller : Fin u.fns.length) (R : LowStufe u caller) :
    (Γ : Ctx) → UFn → (Λ : List (Res (declOf u))) → AtTop u caller Λ → (m : Nat) → List UStmt →
    Except String (GrundArms (declOf u) (verOf u caller) l Γ Λ Λ m × List UStmt)
  | _, _, _, _, 0, rest => .ok (GrundArms.nil, rest)
  | Γ, fn, Λ, pe, m + 1, rest =>
    (R.seq (l := l) Γ fn Λ pe rest).bind fun (⟨Λ₁, b⟩, r) => match m with
      | 0 =>
        if h : Λ₁ = Λ then
          .ok (GrundArms.cons (by subst h; exact b) GrundArms.nil, r)
        else .error "lower: a match arm changes held marks"
      | m' + 1 => match r with
        | .ifElse :: r' =>
          (R.garms (l := l) Γ fn Λ pe (m' + 1) r').bind fun (arms, r2) =>
            if h₁ : Λ₁ = Λ then
              .ok (GrundArms.cons (by subst h₁; exact b) arms, r2)
            else .error "lower: a match arm changes held marks"
        | _ => .error "lower: a match has fewer arms than reasons"

end Gabbro.Grammatik.Parser.UebersetzeAllg2
