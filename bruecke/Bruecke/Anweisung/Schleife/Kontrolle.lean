module
public import Bruecke.Kette.Strecke
public import Bruecke.Anweisung.Zweig.Kopf
public import Bruecke.Anweisung.Schleife.Basis
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {C : Fin u.fns.length → Prop}

def controlStmt {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (leave : Bool) (hl : l = true) : Stmt D V l Γ Λ Λ :=
  if leave then .leave hl else .next hl

theorem Strecke_G.control_append {A : List Eintrag} {s s' : Gabbro.Body.State}
    {xs : List Gabbro.Body.Stmt} {leave : Bool}
    (h : Strecke_G u C A s s' xs (controlB leave)) (ys : List Gabbro.Body.Stmt) :
    Strecke_G u C A s s' (xs ++ ys) (controlB leave) := by
  refine { gut := h.gut, oben := h.oben, unten := h.unten,
    schluessel := h.schluessel, mono := h.mono, lauf := ?_ }
  intro ρB hT hF
  rw [exec_append, h.lauf ρB hT hF]
  cases leave <;> rfl

theorem schrumpfZ_control {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {τ : Ty}
    {a : Ausgang V l (τ :: Γ)} {leave : Bool} {hl : l = true}
    {σ : World D} {ρ : Env D Γ}
    (h : a.schrumpf = controlG leave hl σ ρ) :
    ∃ ρ', a = controlG leave hl σ ρ' ∧ ρ = ρ'.tail := by
  cases leave <;> cases a <;>
    simp only [Ausgang.schrumpf, controlG, Bool.false_eq_true, ↓reduceIte,
      Ausgang.leave.injEq, Ausgang.next.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h; exact ⟨_, rfl, rfl⟩

/-- Shrinking a lexical context preserves a reason return and its exact case. -/
theorem schrumpfZ_why {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {τ : Ty}
    {a : Ausgang V l (τ :: Γ)} {σ : World D} {r : Fin V.gruende}
    (h : a.schrumpf = .why σ r) : a = .why σ r := by
  cases a <;> simp only [Ausgang.schrumpf, Ausgang.why.injEq, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem lowSeq_control_ok {c : Fin u.fns.length} {l : Bool} {n : Nat} {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} {ss rest : List UStmt} {leave : Bool} {x : String}
    {p : Σ Λ', Block (declOf u) (verOf u c) l Γ Λ Λ'}
    (h : lowSeqL (l := l) u c Γ fn (n + 1) Λ [] (controlU leave x :: ss) = .ok (p, rest)) :
    ∃ (hl : l = true) (q : Σ Λ', Block (declOf u) (verOf u c) l Γ Λ Λ'),
      lowSeqL (l := l) u c Γ fn n Λ [] ss = .ok (q, rest) ∧
      p = ⟨q.1, .cons (controlStmt leave hl) q.2⟩ := by
  cases leave <;> rw [lowSeqL_succ] at h <;>
    simp only [controlU, Bool.false_eq_true, ↓reduceIte, lowSeqStep, lowStufe_seq] at h
  all_goals
    split at h
    · rename_i hl
      cases hq : lowSeqL (l := l) u c Γ fn n Λ [] ss with
      | error e => simp only [hq, Except.bind] at h; cases h
      | ok pair =>
        obtain ⟨q, tail⟩ := pair
        simp only [hq, Except.bind] at h
        cases h
        exact ⟨hl, q, rfl, rfl⟩
    · cases h

end Gabbro.Bruecke
