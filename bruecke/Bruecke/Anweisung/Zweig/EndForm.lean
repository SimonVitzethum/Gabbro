module
public import Bruecke.Anweisung.Zweig.EndKopf
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {c : Fin u.fns.length}

theorem lowEndL_narrow_ok {Γ : Ctx} {fn : UFn} {n : Nat} {Λ : List (Res (declOf u))}
    {x : String} {lo hi : Int} {ss tail : List UStmt}
    {p : Endblock (declOf u) (verOf u c) false Γ Λ}
    (hn : numericParam fn x = true)
    (h : lowEndL (l := false) u c Γ fn (n + 1) Λ [] (.narrowBeg x lo hi :: ss) = .ok (p, tail)) :
    ∃ (j : Nat) (a b : Int) (v : Var Γ (.int a b))
      (err : Endblock (declOf u) (verOf u c) false Γ Λ) (remaining : List UStmt)
      (q : Endblock (declOf u) (verOf u c) false (.int lo hi :: Γ) Λ),
      paramPos fn.params x = .ok j ∧ lowVar Γ j (.int a b) = .ok v ∧
      lowEndL (l := false) u c Γ fn n Λ [] ss = .ok (err, .blkEnd :: remaining) ∧
      lowEndL (l := false) u c _ (fn.mitBindung x (lo, hi)) n Λ [] remaining = .ok (q, tail) ∧
      p = .narrow (.var v) lo hi err q := by
  rw [lowEndL_succ] at h
  simp only [lowEndStep, lowStufe_ende] at h
  cases hj : paramPos fn.params x with
  | error e => simp only [hj, Except.bind] at h; cases h
  | ok j =>
    simp only [hj, Except.bind] at h
    have hnum := hn
    unfold numericParam at hnum
    rw [paramPos_find _ _ _ hj] at hnum
    cases hp : fn.params[j]? with
    | none => rw [hp] at h; cases h
    | some entry =>
      obtain ⟨nm, ty⟩ := entry
      rw [hp] at hnum
      cases ty
      case int a b =>
        simp only [hp] at h
        cases hv : lowVar Γ j (.int a b) with
        | error e => simp only [hv, Except.bind] at h; cases h
        | ok v =>
          simp only [hv, Except.bind] at h
          cases herr : lowEndL (l := false) u c Γ fn n Λ [] ss with
          | error e => simp only [herr] at h; cases h
          | ok pair =>
            obtain ⟨err, ending⟩ := pair
            simp only [herr] at h
            cases ending with
            | nil => cases h
            | cons marker remaining =>
              cases marker <;> try { cases h }
              case blkEnd =>
                cases hq : lowEndL (l := false) u c (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) n Λ [] remaining with
                | error e => simp only [hq, Except.bind] at h; cases h
                | ok pair =>
                  obtain ⟨q, tail'⟩ := pair
                  simp only [hq, Except.bind] at h
                  cases h
                  exact ⟨j, a, b, v, err, remaining, q,
                    (by first | exact hj | rfl | simp_all),
                    (by first | exact hv | rfl | simp_all),
                    (by first | exact herr | rfl | simp_all), hq, rfl⟩
      all_goals cases hnum

/-- The two canonical shapes of a conditional inside an explicit ending. -/
abbrev EndIfCases (u : UProg) (c : Fin u.fns.length) (Γ : Ctx) (fn : UFn) (n : Nat)
    (Λ : List (Res (declOf u))) (cnd : UEns) (ss : List UStmt)
    (b : Endblock (declOf u) (verOf u c) false Γ Λ) (tail : List UStmt) : Prop :=
    (∃ (cv : Expr (declOf u) Γ Λ .bool)
      (t e : Endblock (declOf u) (verOf u c) false Γ Λ) (rest1 : List UStmt),
      lowEns u Γ Λ fn none cnd = .ok cv ∧
      lowEndL (l := false) u c Γ fn n Λ [] ss = .ok (t, .ifElse :: rest1) ∧
      lowEndL (l := false) u c Γ fn n Λ [] rest1 = .ok (e, .blkEnd :: tail) ∧ b = .ite cv t e) ∨
    (∃ (Λ₁ : List (Res (declOf u))) (gs : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁)
      (rest : List UStmt)
      (q : Endblock (declOf u) (verOf u c) false Γ Λ₁),
      lowStructL (l := false) u c Γ fn n Λ [] (.ifBeg cnd) ss = .ok (⟨Λ₁, gs⟩, rest) ∧
      lowEndL (l := false) u c Γ fn n Λ₁ [] rest = .ok (q, tail) ∧ b = .cons gs q)

/-- Nested ending conditionals either end both arms or use the ordinary block prefix. -/
theorem lowEndL_ifEnde_cases {Γ : Ctx} {fn : UFn} {n : Nat}
    {Λ : List (Res (declOf u))} {cnd : UEns} {ss tail : List UStmt}
    {b : Endblock (declOf u) (verOf u c) false Γ Λ} (hm : EndMarker tail)
    (h : lowEndL (l := false) u c Γ fn (n + 1) Λ [] (.ifEnde cnd :: ss) = .ok (b, tail)) :
    EndIfCases u c Γ fn n Λ cnd ss b tail := by
  rw [lowEndL_succ] at h
  simp only [lowEndStep, lowStufe_ende, lowStufe_struct] at h
  split at h
  · rename_i cv t rest1 hcv ht
    split at h
    · rename_i e rest2 he
      cases h
      exact .inl ⟨cv, t, e, rest1, hcv, ht, he, rfl⟩
    · rename_i e rest2 he
      cases h
      exact .inl ⟨cv, t, e, rest1, hcv, ht, he, rfl⟩
    · cases h
      cases hm
    · exact .inr (lowEndL_struct_result h)
  · cases h
  · exact .inr (lowEndL_struct_result h)

end Gabbro.Bruecke
