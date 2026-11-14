module
public import Bruecke.Anweisung.Lokal.Benannt
public import Bruecke.Anweisung.Lokal.RecordScope
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

theorem schrittB_bindCall {fn fn' : UFn} {ns ns' : BodyNames}
    {x g : String} {args : List UArg} {b : Gabbro.Body.Stmt}
    (h : schrittB u fn ns (.bindCall x g args) = some (b, fn', ns')) :
    ∃ ty, namedResult u fn ns x g args = some (b, ty) ∧
      fn' = fn.mitTy x ty ∧ ns' = ns.push x := by
  simp only [schrittB] at h
  cases hr : namedResult u fn ns x g args with
  | none => rw [hr] at h; cases h
  | some p =>
    obtain ⟨st, ty⟩ := p
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨ty, rfl, rfl, rfl⟩

theorem namedResult_some {fn : UFn} {ns : BodyNames} {x g : String}
    {args : List UArg} {b : Gabbro.Body.Stmt} {ty : Ty}
    (h : namedResult u fn ns x g args = some (b, ty)) :
    ∃ gf es renamed sh, fnSuch u g = some gf ∧ gf.ergTy = some ty ∧
      shapeOfTy ty = some sh ∧ argsExpr u fn args = some es ∧
      renameStep.renameScalars (ns.lookup fn) es = some renamed ∧
      b = .bindCall (ns.fresh x) g (gf.params.map (·.1)) renamed (preExpr gf) := by
  unfold namedResult at h
  cases hgf : fnSuch u g with
  | none => simp only [hgf, bind, Option.bind_none] at h; cases h
  | some gf =>
    simp only [hgf, bind, Option.bind_some] at h
    cases ht : gf.ergTy with
    | none => simp only [ht, bind, Option.bind_none] at h; cases h
    | some t =>
      simp only [ht, bind, Option.bind_some] at h
      cases hsh : shapeOfTy t with
      | none => simp only [hsh, bind, Option.bind_none] at h; cases h
      | some sh =>
        simp only [hsh, bind, Option.bind_some] at h
        cases hes : argsExpr u fn args with
        | none => simp only [hes, bind, Option.bind_none] at h; cases h
        | some es =>
          simp only [hes, bind, Option.bind_some] at h
          cases hn : renameStep.renameScalars (ns.lookup fn) es with
          | none => simp only [hn, bind, Option.bind_none] at h; cases h
          | some renamed =>
            simp only [hn, bind, Option.bind_some, pure, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨gf, es, renamed, sh, rfl, ht, hsh, rfl, hn, rfl⟩

theorem namedResult_sicht {fn ft : UFn} (h : Sicht u ft fn) (ns : BodyNames)
    (x g : String) (args : List UArg) :
    namedResult u ft ns x g args = namedResult u fn ns x g args := by
  have hn : ns.lookup ft = ns.lookup fn := funext (BodyNames.lookup_sicht h ns)
  unfold namedResult
  rw [argsExpr_sicht h, hn]

theorem UmfangB.bindTy {Γ : Ctx} {fn : UFn} {ns : BodyNames} (h : UmfangB Γ fn ns)
    {x : String} (hx : NameFrisch (protectedNames fn.params fn.kinds) x) {ty : Ty}
    {sh : Gabbro.Body.Shape} (ht : shapeOfTy ty = some sh) :
    UmfangB (ty :: Γ) (fn.mitTy x ty) (ns.push x) := by
  cases ty
  case int lo hi => exact h.bind hx (lo, hi)
  case bool => exact h.bindB hx
  case prod id fs => exact h.bindRecord hx id fs
  all_goals cases ht

theorem Sicht.bindTy {ft fn : UFn} (h : Sicht u ft fn) (x : String) {ty : Ty}
    {sh : Gabbro.Body.Shape} (ht : shapeOfTy ty = some sh) :
    Sicht u (ft.mitTy x ty) (fn.mitTy x ty) := by
  cases ty
  case int lo hi => exact h.bind x (lo, hi) (lo, hi)
  case bool => exact h.bindB x
  case prod id fs => exact h.bindRecord x id fs
  all_goals cases ht

theorem PositionalLRel.pushTy {D : Deklaration} {Γ : Ctx} {fn : UFn} {ids : List String}
    {ρ : Env D Γ} {β : Gabbro.Body.Binding} (h : PositionalLRel fn ids 0 ρ β)
    (x id : String) (hfresh : id ∉ ids) {ty : Ty} {sh : Gabbro.Body.Shape}
    (ht : shapeOfTy ty = some sh) (v : Wert D ty) :
    PositionalLRel (fn.mitTy x ty) (id :: ids) 0 (Env.cons v ρ)
      (Gabbro.Body.bindLocal β id (valOf ty v)) := by
  cases ty
  case int lo hi => exact h.push x id (lo, hi) hfresh v
  case bool => exact h.pushB x id hfresh v
  case prod rid fs => exact h.pushRecord x id rid fs hfresh v
  all_goals cases ht

theorem PositionalLRel.tailTy {D : Deklaration} {Γ : Ctx} {fn : UFn} {ids : List String}
    {id x : String} {ty : Ty} {sh : Gabbro.Body.Shape} {ρ : Env D (ty :: Γ)}
    {β : Gabbro.Body.Binding} (ht : shapeOfTy ty = some sh)
    (h : PositionalLRel (fn.mitTy x ty) (id :: ids) 0 ρ β) :
    PositionalLRel fn ids 0 ρ.tail β := by
  cases ty
  case int => exact h.tail
  case bool => exact h.tailB
  case prod =>
    have hp : PositionalLRel (fn.mitBindung x (0, 0)) (id :: ids) 0 ρ β :=
      ⟨h.length, h.distinct, h.values⟩
    exact hp.tail
  all_goals cases ht

end Gabbro.Bruecke
