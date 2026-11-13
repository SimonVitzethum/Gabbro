module
public import Bruecke.Anweisung.Match.ReasonLesen
public import Bruecke.Anweisung.Match.Kopf
@[expose] public section
namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {c : Fin u.fns.length}

theorem lowGArms_succ {fuel n : Nat} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {ss tail : List UStmt} {arms : GrundArms (declOf u) (verOf u c) false Γ Λ Λ (n + 1)}
    (h : lowGArmsL u c Γ fn (fuel + 1) Λ [] (n + 1) ss = .ok (arms, tail)) :
    ∃ (body : Block (declOf u) (verOf u c) false Γ Λ Λ)
      (restArms : GrundArms (declOf u) (verOf u c) false Γ Λ Λ n) remaining,
      lowSeqL u c Γ fn fuel Λ [] ss = .ok (⟨Λ, body⟩, remaining) ∧
      ((n = 0 ∧ remaining = tail) ∨
       ∃ m rest, n = m + 1 ∧ remaining = .ifElse :: rest ∧
         lowGArmsL u c Γ fn fuel Λ [] n rest = .ok (restArms, tail)) ∧
      arms = .cons body restArms := by
  change lowGArmsStep u c (lowStufe u c fuel) Γ fn Λ [] (n + 1) ss = .ok (arms, tail) at h
  simp only [lowGArmsStep, lowStufe_seq, lowStufe_garms, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i out body remaining hb
    cases n with
    | zero =>
      split at h
      · rename_i same
        subst out
        cases h
        exact ⟨body, .nil, remaining, hb, .inl ⟨rfl, rfl⟩, rfl⟩
      · cases h
    | succ m =>
      split at h
      · rename_i rest hr
        split at h
        · cases h
        · rename_i restArms remaining' hrest
          split at h
          · rename_i same
            subst out
            cases h
            exact ⟨body, restArms, remaining, hb, .inr ⟨m, rest, rfl, hr, hrest⟩, rfl⟩
          · cases h
      · cases h

theorem lowBodyF_reason_ok {Γ : Ctx} {fn : UFn} {n : Nat} {Λ : List (Res (declOf u))}
    {x : String} {ss : List UStmt} {r : URet} {b0 : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowBodyF u c Γ fn (n + 1) Λ (.matchWhyBeg x :: ss) r = .ok b0) :
    ∃ Λ₁ (st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁) tail
      (rest : Endblock (declOf u) (verOf u c) false Γ Λ₁),
      lowStructL u c Γ fn blockFuel Λ [] (.matchWhyBeg x) ss = .ok (⟨Λ₁, st⟩, tail) ∧
      lowBodyF u c Γ fn n Λ₁ tail r = .ok rest ∧ b0 = .cons st rest := by
  simp only [lowBodyF] at h
  split at h
  · cases h
  · rename_i Λ₁ st tail hs
    split at h
    · cases h
    · rename_i rest hr
      cases h
      exact ⟨Λ₁, st, tail, rest, hs, hr, rfl⟩

theorem lowStruct_reason_ok {fuel count : Nat} {Γ : Ctx} {fn : UFn}
    {Λ Λ' : List (Res (declOf u))} {x : String} {ss tail : List UStmt}
    {st : Stmt (declOf u) (verOf u c) false Γ Λ Λ'}
    (ht : valueParamTy fn x = some (.why count))
    (h : lowStructL u c Γ fn (fuel + 1) Λ [] (.matchWhyBeg x) ss = .ok (⟨Λ', st⟩, tail)) :
    ∃ j (v : Var Γ (.why count))
      (arms : GrundArms (declOf u) (verOf u c) false Γ Λ Λ count),
      paramPos fn.params x = .ok j ∧ lowVar Γ j (.why count) = .ok v ∧
      lowGArmsL u c Γ fn fuel Λ [] count ss = .ok (arms, .blkEnd :: tail) ∧
      Λ' = Λ ∧ HEq st (Stmt.onWhy (Expr.var v) arms) := by
  rw [lowStructL_succ] at h
  simp only [lowStructStep] at h
  cases hj : paramPos fn.params x with
  | error err => rw [hj] at h; cases h
  | ok j =>
    rw [hj] at h
    unfold valueParamTy at ht
    rw [paramPos_find _ _ _ hj] at ht
    split at h
    · rename_i name cnt hq
      simp only [hq, Option.some.injEq, Ty.why.injEq] at ht
      subst cnt
      split at h
      · cases h
      · rename_i v hv
        simp only [lowStufe_garms] at h
        split at h
        · cases h
        · rename_i arms remaining ha
          cases h
          exact ⟨j, v, arms, hj, hv, ha, rfl, HEq.rfl⟩
      · cases h
    · cases h

end Gabbro.Bruecke
