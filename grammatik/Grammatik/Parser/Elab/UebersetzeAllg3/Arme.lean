module

public import Grammatik.Parser.Elab.ExportControl
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
    (cs : List (Option (Int × Int))) → List String → List UStmt →
    Except String (Arms (declOf u) (verOf u caller) l Γ Λ Λ cs × List UStmt)
  | _, _, _, _, [], _, rest => .ok (Arms.nil, rest)
  | Γ, fn, Λ, pe, none :: cs', bs, rest =>
    (R.seq (l := l) Γ fn Λ pe rest).bind fun (b, r) => match cs' with
      | [] => .ok (Arms.cons b Arms.nil, r)
      | c' :: cs'' => match r with
        | .ifElse :: r' =>
          (R.arms (l := l) Γ fn Λ pe (c' :: cs'') (bs.drop 1) r').bind fun (arms, r2) => .ok (Arms.cons b arms, r2)
        | _ => .error "lower: a match has fewer arms than cases"
  | Γ, fn, Λ, pe, some (lo, hi) :: cs', bs, rest =>
    (R.seq (l := l) (.int lo hi :: Γ) (fn.mitBindung (bs.headD "") (lo, hi)) Λ pe rest).bind fun (b, r) =>
      match cs' with
      | [] => .ok (Arms.cons b Arms.nil, r)
      | c' :: cs'' => match r with
        | .ifElse :: r' =>
          (R.arms (l := l) Γ fn Λ pe (c' :: cs'') (bs.drop 1) r').bind fun (arms, r2) => .ok (Arms.cons b arms, r2)
        | _ => .error "lower: a match has fewer arms than cases"

/-- The arms of a reason match: `m` blocks, one per reason, separated by `ifElse`; the marker that closes the
    match is left to the caller. -/
def lowGArmsStep {l : Bool} (u : UProg) (caller : Fin u.fns.length) (R : LowStufe u caller) :
    (Γ : Ctx) → UFn → (Λ : List (Res (declOf u))) → AtTop u caller Λ → (m : Nat) → List UStmt →
    Except String (GrundArms (declOf u) (verOf u caller) l Γ Λ Λ m × List UStmt)
  | _, _, _, _, 0, rest => .ok (GrundArms.nil, rest)
  | Γ, fn, Λ, pe, m + 1, rest =>
    (R.seq (l := l) Γ fn Λ pe rest).bind fun (b, r) => match m with
      | 0 => .ok (GrundArms.cons b GrundArms.nil, r)
      | m' + 1 => match r with
        | .ifElse :: r' =>
          (R.garms (l := l) Γ fn Λ pe (m' + 1) r').bind fun (arms, r2) => .ok (GrundArms.cons b arms, r2)
        | _ => .error "lower: a match has fewer arms than reasons"

end Gabbro.Grammatik.Parser.UebersetzeAllg2
