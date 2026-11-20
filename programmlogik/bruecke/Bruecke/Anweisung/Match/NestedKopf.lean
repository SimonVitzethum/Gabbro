module
public import Bruecke.Anweisung.Match.Kopf
public import Bruecke.Anweisung.Match.NestedLesen
@[expose] public section
namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {c : Fin u.fns.length}

theorem lowSeq_option_ok {loopMode : Bool} {n : Nat} {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} {num : Nat} {v : UOpt} {x : String} {ss rest : List UStmt}
    {p : Σ Λ', Block (declOf u) (verOf u c) loopMode Γ Λ Λ'}
    (h : lowSeqL (l := loopMode) u c Γ fn (n + 1) Λ [] (.matchBeg num v x :: ss) = .ok (p, rest)) :
    ∃ Λ₁, ∃ (st : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ₁) (tail : List UStmt)
      (q : Σ Λ', Block (declOf u) (verOf u c) loopMode Γ Λ₁ Λ'),
      lowStructL (l := loopMode) u c Γ fn n Λ [] (.matchBeg num v x) ss = .ok (⟨Λ₁, st⟩, tail) ∧
      lowSeqL (l := loopMode) u c Γ fn n Λ₁ [] tail = .ok (q, rest) ∧ p = ⟨q.1, .cons st q.2⟩ := by
  rw [lowSeqL_succ] at h
  simp only [lowSeqStep, lowStufe_struct, lowStufe_seq] at h
  cases hs : lowStructL (l := loopMode) u c Γ fn n Λ [] (.matchBeg num v x) ss with
  | error e => simp only [hs, Except.bind] at h <;> cases h
  | ok pair =>
    obtain ⟨⟨Λ₁, st⟩, tail⟩ := pair
    simp only [hs, Except.bind] at h
    cases hq : lowSeqL (l := loopMode) u c Γ fn n Λ₁ [] tail with
    | error e => simp only [hq, Except.bind] at h <;> cases h
    | ok pair =>
      obtain ⟨q, rest'⟩ := pair
      simp only [hq, Except.bind] at h
      cases h
      exact ⟨Λ₁, st, tail, q, (by first | exact hs | rfl), hq, rfl⟩

theorem lowSeq_reason_ok {loopMode : Bool} {n : Nat} {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} {x : String} {ss rest : List UStmt}
    {p : Σ Λ', Block (declOf u) (verOf u c) loopMode Γ Λ Λ'}
    (h : lowSeqL (l := loopMode) u c Γ fn (n + 1) Λ [] (.matchWhyBeg x :: ss) = .ok (p, rest)) :
    ∃ Λ₁, ∃ (st : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ₁) (tail : List UStmt)
      (q : Σ Λ', Block (declOf u) (verOf u c) loopMode Γ Λ₁ Λ'),
      lowStructL (l := loopMode) u c Γ fn n Λ [] (.matchWhyBeg x) ss = .ok (⟨Λ₁, st⟩, tail) ∧
      lowSeqL (l := loopMode) u c Γ fn n Λ₁ [] tail = .ok (q, rest) ∧ p = ⟨q.1, .cons st q.2⟩ := by
  rw [lowSeqL_succ] at h
  simp only [lowSeqStep, lowStufe_struct, lowStufe_seq] at h
  cases hs : lowStructL (l := loopMode) u c Γ fn n Λ [] (.matchWhyBeg x) ss with
  | error e => simp only [hs, Except.bind] at h <;> cases h
  | ok pair =>
    obtain ⟨⟨Λ₁, st⟩, tail⟩ := pair
    simp only [hs, Except.bind] at h
    cases hq : lowSeqL (l := loopMode) u c Γ fn n Λ₁ [] tail with
    | error e => simp only [hq, Except.bind] at h <;> cases h
    | ok pair =>
      obtain ⟨q, rest'⟩ := pair
      simp only [hq, Except.bind] at h
      cases h
      exact ⟨Λ₁, st, tail, q, (by first | exact hs | rfl), hq, rfl⟩

theorem lowSeq_tag_ok {loopMode : Bool} {n : Nat} {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} {sidx : Nat} {x : String} {binders : List String} {ss rest : List UStmt}
    {p : Σ Λ', Block (declOf u) (verOf u c) loopMode Γ Λ Λ'}
    (h : lowSeqL (l := loopMode) u c Γ fn (n + 1) Λ [] (.matchTagBeg sidx x binders :: ss) = .ok (p, rest)) :
    ∃ Λ₁, ∃ (st : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ₁) (tail : List UStmt)
      (q : Σ Λ', Block (declOf u) (verOf u c) loopMode Γ Λ₁ Λ'),
      lowStructL (l := loopMode) u c Γ fn n Λ [] (.matchTagBeg sidx x binders) ss = .ok (⟨Λ₁, st⟩, tail) ∧
      lowSeqL (l := loopMode) u c Γ fn n Λ₁ [] tail = .ok (q, rest) ∧ p = ⟨q.1, .cons st q.2⟩ := by
  rw [lowSeqL_succ] at h
  simp only [lowSeqStep, lowStufe_struct, lowStufe_seq] at h
  cases hs : lowStructL (l := loopMode) u c Γ fn n Λ [] (.matchTagBeg sidx x binders) ss with
  | error e => simp only [hs, Except.bind] at h <;> cases h
  | ok pair =>
    obtain ⟨⟨Λ₁, st⟩, tail⟩ := pair
    simp only [hs, Except.bind] at h
    cases hq : lowSeqL (l := loopMode) u c Γ fn n Λ₁ [] tail with
    | error e => simp only [hq, Except.bind] at h <;> cases h
    | ok pair =>
      obtain ⟨q, rest'⟩ := pair
      simp only [hq, Except.bind] at h
      cases h
      exact ⟨Λ₁, st, tail, q, (by first | exact hs | rfl), hq, rfl⟩

end Gabbro.Bruecke
