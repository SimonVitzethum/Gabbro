module
public import Bruecke.Anweisung.Ruf.Lesen
public import Bruecke.Anweisung.Zweig.Kopf
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {c : Fin u.fns.length}

theorem lowBodyF_bindCall_ok {Γ : Ctx} {fn : UFn} {n : Nat}
    {Λ : List (Res (declOf u))} {x g : String} {args : List UArg}
    {ss : List UStmt} {r : URet} {b0 : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowBodyF u c Γ fn (n + 1) Λ (.bindCall x g args :: ss) r = .ok b0) :
    ∃ (k : RufKopf u c Γ Λ) (ty : Ty) (he : (declOf u).erg k.callee = some ty)
      (hr : (declOf u).gruende k.callee = 0)
      (rest : Endblock (declOf u) (verOf u c) false (ty :: Γ) (nach (declOf u) k.callee Λ)),
      lowRufKopf u c Γ fn Λ g args = .ok k ∧
      lowBodyF u c (ty :: Γ) (mitRuf u fn x k.callee ty) n
        (nach (declOf u) k.callee Λ) ss r = .ok rest ∧
      b0 = .bindCall k.callee k.args he k.hp hr rest := by
  simp only [lowBodyF] at h
  split at h
  · cases h
  · rename_i k hk
    unfold withErg at h
    split at h
    · cases h
    · rename_i ty he
      split at h
      · rename_i hr
        simp only at h
        split at h
        · cases h
        · rename_i rest hrest
          cases h
          exact ⟨k, ty, he, hr, rest, (by first | exact hk | rfl), hrest, rfl⟩
      · simp only at h
        split at h <;> cases h

theorem lowSeq_bindCall_ok {loopMode : Bool} {Γ : Ctx} {fn : UFn} {n : Nat}
    {Λ : List (Res (declOf u))} {pe : AtTop u c Λ} {x g : String} {args : List UArg}
    {ss tail : List UStmt}
    {p : Σ Λ', Block (declOf u) (verOf u c) loopMode Γ Λ Λ'}
    (h : lowSeqL (l := loopMode) u c Γ fn (n + 1) Λ pe (.bindCall x g args :: ss) = .ok (p, tail)) :
    ∃ (k : RufKopf u c Γ Λ) (ty : Ty) (he : (declOf u).erg k.callee = some ty)
      (hr : (declOf u).gruende k.callee = 0)
      (q : Σ Λ', Block (declOf u) (verOf u c) loopMode (ty :: Γ) (nach (declOf u) k.callee Λ) Λ'),
      lowRufKopf u c Γ fn Λ g args = .ok k ∧
      lowSeqL (l := loopMode) u c (ty :: Γ) (mitRuf u fn x k.callee ty) n
        (nach (declOf u) k.callee Λ) pe ss = .ok (q, tail) ∧
      p = ⟨q.1, .bindCall k.callee k.args he k.hp hr q.2⟩ := by
  rw [lowSeqL_succ] at h
  simp only [lowSeqStep, lowStufe_seq] at h
  cases hk : lowRufKopf u c Γ fn Λ g args with
  | error e => simp only [hk, Except.bind] at h; cases h
  | ok k =>
    simp only [hk, Except.bind] at h
    unfold withErg at h
    split at h
    · cases h
    · rename_i ty he
      cases hq : lowSeqL (l := loopMode) u c (ty :: Γ) (mitRuf u fn x k.callee ty) n
          (nach (declOf u) k.callee Λ) pe ss with
      | error e => simp only [hq, Except.bind] at h; cases h
      | ok res =>
        obtain ⟨⟨Λ', b⟩, tail'⟩ := res
        simp only [hq, Except.bind] at h
        split at h
        · rename_i hr
          cases h
          exact ⟨k, ty, he, hr, ⟨Λ', b⟩, (by first | exact hk | rfl), hq, rfl⟩
        · cases h

/-- For admitted scalar result types, the canonical call scope is exactly the reader scope. -/
theorem mitRuf_scalar (fn : UFn) (x : String) (d : Fin u.fns.length)
    {ty : Ty} {sh : Gabbro.Body.Shape} (ht : shapeOfTy ty = some sh) :
    mitRuf u fn x d ty = fn.mitTy x ty := by
  cases ty
  case int | bool | prod => rfl
  all_goals cases ht

theorem protectedNames_mitTy (fn : UFn) (x : String) {ty : Ty} {sh : Gabbro.Body.Shape}
    (ht : shapeOfTy ty = some sh) :
    protectedNames (fn.mitTy x ty).params (fn.mitTy x ty).kinds =
      protectedNames fn.params fn.kinds := by
  cases ty
  case int | bool | prod => rfl
  all_goals cases ht

end Gabbro.Bruecke
