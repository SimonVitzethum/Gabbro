module
public import Bruecke.Anweisung.Match.Lesen
public import Bruecke.Anweisung.Zweig.Kopf
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {c : Fin u.fns.length}

theorem lowBodyF_option_ok {Γ : Ctx} {fn : UFn} {n : Nat} {Λ : List (Res (declOf u))}
    {num : Nat} {v : UOpt} {x : String} {ss : List UStmt} {r : URet}
    {b0 : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowBodyF u c Γ fn (n + 1) Λ (.matchBeg num v x :: ss) r = .ok b0) :
    ∃ Λ₁, ∃ (st : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁) (tail : List UStmt)
      (rest : Endblock (declOf u) (verOf u c) false Γ Λ₁),
      lowStructL (l := false) u c Γ fn blockFuel Λ [] (.matchBeg num v x) ss = .ok (⟨Λ₁, st⟩, tail) ∧
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

theorem lowStruct_option_ok {loopMode : Bool} {n : Nat} {Γ : Ctx} {fn : UFn}
    {Λ Λ' : List (Res (declOf u))} {num : Nat} {v : UOpt} {x : String} {ss tail : List UStmt}
    {st : Stmt (declOf u) (verOf u c) loopMode Γ Λ Λ'}
    (hn : num < u.tabs.length)
    (h : lowStructL (l := loopMode) u c Γ fn (n + 1) Λ [] (.matchBeg num v x) ss =
      .ok (⟨Λ', st⟩, tail)) :
    ∃ (ev : Expr (declOf u) Γ Λ (.opt ((declOf u).count ⟨num, hn⟩)))
      (pb : Block (declOf u) (verOf u c) loopMode (.index ((declOf u).count ⟨num, hn⟩) :: Γ) Λ Λ')
      (ab : Block (declOf u) (verOf u c) loopMode Γ Λ Λ'), ∃ r1,
      lowOpt u Γ Λ fn 0 num hn v = .ok ev ∧
      lowSeqL (l := loopMode) u c (.index ((declOf u).count ⟨num, hn⟩) :: Γ)
        (fn.mitIndex x num ((declOf u).count ⟨num, hn⟩)) n Λ [] ss = .ok (⟨Λ', pb⟩, .ifElse :: r1) ∧
      lowSeqL (l := loopMode) u c Γ fn n Λ [] r1 = .ok (⟨Λ', ab⟩, .blkEnd :: tail) ∧
      st = .onOption ev pb ab := by
  rw [lowStructL_succ] at h
  simp only [lowStructStep, dif_pos hn, lowStufe_seq] at h
  cases hv : lowOpt u Γ Λ fn 0 num hn v with
  | error err => simp only [hv, Except.bind] at h <;> cases h
  | ok ev =>
    simp only [hv, Except.bind] at h
    split at h
    · cases h
    · rename_i Λp pb r1 hp
      split at h
      · cases h
      · rename_i Λa ab r2 ha
        split at h
        · rename_i heq
          subst Λa
          cases h
          exact ⟨ev, pb, ab, r1, (by first | exact hv | rfl), hp, ha, rfl⟩
        · cases h
      · cases h
    · cases h

end Gabbro.Bruecke
