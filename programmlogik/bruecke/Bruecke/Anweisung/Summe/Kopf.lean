module
public import Bruecke.Anweisung.Summe.Scope
public import Bruecke.Anweisung.Zweig.EndKopf
@[expose] public section

/-! # The lowering of `let x = T::C;`: its three readers -/

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {c : Fin u.fns.length}

theorem lowBodyF_bindSum_ok (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {n : Nat}
    {Λ : List (Res (declOf u))} {x : String} {sidx : Nat} {v : USVal} {hs : sidx < u.sums.length}
    {ss : List UStmt} {r : URet} {b0 : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowBodyF u c Γ fn (n + 1) Λ (.bindSum x sidx v :: ss) r = .ok b0) :
    ∃ (ev : Expr (declOf u) Γ Λ (.sum (u.sums.get ⟨sidx, hs⟩).spec))
      (e : Endblock (declOf u) (verOf u c) false (.sum (u.sums.get ⟨sidx, hs⟩).spec :: Γ) Λ),
      lowSVal u Γ Λ fn 0 sidx hs v = .ok ev ∧
      lowBodyF u c (.sum (u.sums.get ⟨sidx, hs⟩).spec :: Γ)
        (fn.mitSum x sidx (u.sums.get ⟨sidx, hs⟩).spec) n Λ ss r = .ok e ∧
      b0 = Endblock.bind ev e := by
  simp only [lowBodyF, hs, ↓reduceDIte] at h
  split at h
  · cases h
  · rename_i ev hev
    split at h
    · cases h
    · rename_i e he
      cases h
      exact ⟨ev, e, hev, he, rfl⟩

theorem lowSeq_bindSum_ok {loopMode : Bool} {n : Nat} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {pe : AtTop u c Λ} {x : String} {sidx : Nat} {v : USVal} {hs : sidx < u.sums.length}
    {ss rest : List UStmt}
    {p : Σ Λ' : List (Res (declOf u)), Block (declOf u) (verOf u c) loopMode Γ Λ Λ'}
    (h : lowSeqL (l := loopMode) u c Γ fn (n + 1) Λ pe (.bindSum x sidx v :: ss) = .ok (p, rest)) :
    ∃ (ev : Expr (declOf u) Γ Λ (.sum (u.sums.get ⟨sidx, hs⟩).spec)) (q : Σ Λ' : List (Res (declOf u)),
        Block (declOf u) (verOf u c) loopMode (.sum (u.sums.get ⟨sidx, hs⟩).spec :: Γ) Λ Λ'),
      lowSVal u Γ Λ fn 0 sidx hs v = .ok ev ∧
      lowSeqL (l := loopMode) u c (.sum (u.sums.get ⟨sidx, hs⟩).spec :: Γ)
        (fn.mitSum x sidx (u.sums.get ⟨sidx, hs⟩).spec) n Λ pe ss = .ok (q, rest) ∧
      p = ⟨q.1, Block.bind ev q.2⟩ := by
  rw [lowSeqL_succ] at h
  simp only [lowSeqStep, lowStufe_seq, hs, ↓reduceDIte] at h
  cases hev : lowSVal u Γ Λ fn 0 sidx hs v with
  | error e => simp only [hev, Except.bind] at h <;> cases h
  | ok ev =>
    simp only [hev, Except.bind] at h
    cases hq : lowSeqL (l := loopMode) u c (.sum (u.sums.get ⟨sidx, hs⟩).spec :: Γ)
        (fn.mitSum x sidx (u.sums.get ⟨sidx, hs⟩).spec) n Λ pe ss with
    | error e => simp only [hq] at h <;> cases h
    | ok res =>
      obtain ⟨⟨Λ', b⟩, r⟩ := res
      simp only [hq] at h
      cases h
      exact ⟨ev, ⟨Λ', b⟩, rfl, rfl, rfl⟩

theorem lowEndL_bindSum_ok {n : Nat} {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {x : String} {sidx : Nat} {v : USVal} {hs : sidx < u.sums.length} {ss rest : List UStmt}
    {b : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowEndL (l := false) u c Γ fn (n + 1) Λ [] (.bindSum x sidx v :: ss) = .ok (b, rest)) :
    ∃ (ev : Expr (declOf u) Γ Λ (.sum (u.sums.get ⟨sidx, hs⟩).spec))
      (q : Endblock (declOf u) (verOf u c) false (.sum (u.sums.get ⟨sidx, hs⟩).spec :: Γ) Λ),
      lowSVal u Γ Λ fn 0 sidx hs v = .ok ev ∧
      lowEndL (l := false) u c _ (fn.mitSum x sidx (u.sums.get ⟨sidx, hs⟩).spec) n Λ [] ss =
        .ok (q, rest) ∧ b = .bind ev q := by
  rw [lowEndL_succ] at h
  simp only [lowEndStep, lowStufe_ende, hs, ↓reduceDIte] at h
  cases hev : lowSVal u Γ Λ fn 0 sidx hs v with
  | error e => simp only [hev, Except.bind] at h; cases h
  | ok ev =>
    simp only [hev, Except.bind] at h
    cases hq : lowEndL (l := false) u c (.sum (u.sums.get ⟨sidx, hs⟩).spec :: Γ)
        (fn.mitSum x sidx (u.sums.get ⟨sidx, hs⟩).spec) n Λ [] ss with
    | error e => simp only [hq] at h; cases h
    | ok res =>
      obtain ⟨q, r⟩ := res
      simp only [hq] at h
      cases h
      exact ⟨ev, q, rfl, rfl, rfl⟩

end Gabbro.Bruecke
