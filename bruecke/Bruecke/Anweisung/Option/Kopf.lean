module
public import Bruecke.Anweisung.Option.Scope
public import Bruecke.Anweisung.Zweig.Kopf
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {c : Fin u.fns.length}

theorem lowBodyF_bindOpt_ok (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {n : Nat}
    {Λ : List (Res (declOf u))} {x : String} {num : Nat} {v : UOpt} {hn : num < u.tabs.length}
    {ss : List UStmt} {r : URet} {b0 : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowBodyF u c Γ fn (n + 1) Λ (.bindOpt x num v :: ss) r = .ok b0) :
    ∃ (ev : Expr (declOf u) Γ Λ (.opt ((declOf u).count ⟨num, hn⟩)))
      (e : Endblock (declOf u) (verOf u c) false (.opt ((declOf u).count ⟨num, hn⟩) :: Γ) Λ),
      lowOpt u Γ Λ fn 0 num hn v = .ok ev ∧
      lowBodyF u c (.opt ((declOf u).count ⟨num, hn⟩) :: Γ) (fn.mitOpt x num ((declOf u).count ⟨num, hn⟩)) n Λ ss r = .ok e ∧
      b0 = Endblock.bind ev e := by
  simp only [lowBodyF, hn, ↓reduceDIte] at h
  split at h
  · cases h
  · rename_i ev hev
    split at h
    · cases h
    · rename_i e he
      cases h
      exact ⟨ev, e, hev, he, rfl⟩

theorem lowSeq_bindOpt_ok {loopMode : Bool} {n : Nat} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {pe : AtTop u c Λ} {x : String} {num : Nat} {v : UOpt} {hn : num < u.tabs.length} {ss rest : List UStmt}
    {p : Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u c) loopMode Γ Λ Λ'}
    (h : lowSeqL (l := loopMode) u c Γ fn (n + 1) Λ pe (.bindOpt x num v :: ss) = .ok (p, rest)) :
    ∃ (ev : Expr (declOf u) Γ Λ (.opt ((declOf u).count ⟨num, hn⟩))) (q : Σ Λ' : List (Res (declOf u)),
        Block (declOf u) (verOf u c) loopMode (.opt ((declOf u).count ⟨num, hn⟩) :: Γ) Λ Λ'),
      lowOpt u Γ Λ fn 0 num hn v = .ok ev ∧
      lowSeqL (l := loopMode) u c (.opt ((declOf u).count ⟨num, hn⟩) :: Γ) (fn.mitOpt x num ((declOf u).count ⟨num, hn⟩)) n Λ pe ss =
        .ok (q, rest) ∧
      p = ⟨q.1, Block.bind ev q.2⟩ := by
  rw [lowSeqL_succ] at h
  simp only [lowSeqStep, lowStufe_seq, hn, ↓reduceDIte] at h
  cases hev : lowOpt u Γ Λ fn 0 num hn v with
  | error e => simp only [hev, Except.bind] at h <;> cases h
  | ok ev =>
    simp only [hev, Except.bind] at h
    cases hq : lowSeqL (l := loopMode) u c (.opt ((declOf u).count ⟨num, hn⟩) :: Γ) (fn.mitOpt x num ((declOf u).count ⟨num, hn⟩)) n Λ pe ss with
    | error e => simp only [hq] at h <;> cases h
    | ok res =>
      obtain ⟨⟨Λ', b⟩, r⟩ := res
      simp only [hq] at h
      cases h
      exact ⟨ev, ⟨Λ', b⟩, rfl, rfl, rfl⟩

end Gabbro.Bruecke
