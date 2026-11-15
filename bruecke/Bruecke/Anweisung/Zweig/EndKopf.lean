module
public import Bruecke.Anweisung.Zweig.EndLesen
public import Bruecke.Anweisung.Bereich.Kopf
public import Bruecke.Anweisung.Ruf.Kopf
@[expose] public section

namespace Gabbro.Bruecke

open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg} {c : Fin u.fns.length}

theorem lowEndL_bind_ok {Γ : Ctx} {fn : UFn} {n : Nat} {Λ : List (Res (declOf u))}
    {x : String} {d : Option (Int × Int)} {v : USide} {ss tail : List UStmt}
    {b : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowEndL (l := false) u c Γ fn (n + 1) Λ [] (.bind x d v :: ss) = .ok (b, tail)) :
    ∃ (ls : LowSide u Γ Λ)
      (q : Endblock (declOf u) (verOf u c) false (.int ls.range.1 ls.range.2 :: Γ) Λ),
      lowBindWert u Γ Λ fn d v = .ok ls ∧
      lowEndL (l := false) u c _ (fn.mitBindung x ls.range) n Λ [] ss = .ok (q, tail) ∧
      b = .bind ls.term q := by
  rw [lowEndL_succ] at h
  simp only [lowEndStep, lowStufe_ende] at h
  cases hl : lowBindWert u Γ Λ fn d v with
  | error e => simp only [hl, Except.bind] at h; cases h
  | ok ls =>
    simp only [hl, Except.bind] at h
    split at h
    · rename_i e he
      simp only [he, Except.bind] at h
      cases h
    · rename_i v hv
      obtain ⟨q, tail'⟩ := v
      simp only [hv, Except.bind, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ls, q, (by first | exact hl | rfl | simp_all), (by first | exact hv | rfl | simp_all), rfl⟩

theorem lowEndL_bindMut_ok {Γ : Ctx} {fn : UFn} {n : Nat} {Λ : List (Res (declOf u))}
    {x : String} {lo hi : Int} {v : USide} {ss tail : List UStmt}
    {b : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowEndL (l := false) u c Γ fn (n + 1) Λ [] (.bindMut x lo hi v :: ss) = .ok (b, tail)) :
    ∃ (ev : Expr (declOf u) Γ Λ (.int lo hi))
      (q : Endblock (declOf u) (verOf u c) false (.int lo hi :: Γ) Λ),
      lowWertAt u Γ Λ fn lo hi v = .ok ev ∧
      lowEndL (l := false) u c _ (fn.mitBindung x (lo, hi)) n Λ [] ss = .ok (q, tail) ∧
      b = .bind ev q := by
  rw [lowEndL_succ] at h
  simp only [lowEndStep, lowStufe_ende] at h
  cases hv : lowWertAt u Γ Λ fn lo hi v with
  | error e => simp only [hv, Except.bind] at h; cases h
  | ok ev =>
    simp only [hv, Except.bind] at h
    split at h
    · rename_i e he
      simp only [he, Except.bind] at h
      cases h
    · rename_i v hv
      obtain ⟨q, tail'⟩ := v
      simp only [hv, Except.bind, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ev, q, (by first | exact hv | rfl | simp_all), (by first | exact hv | rfl | simp_all), rfl⟩

theorem lowEndL_bindB_ok {Γ : Ctx} {fn : UFn} {n : Nat} {Λ : List (Res (declOf u))}
    {x : String} {v : UEns} {ss tail : List UStmt}
    {b : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowEndL (l := false) u c Γ fn (n + 1) Λ [] (.bindB x v :: ss) = .ok (b, tail)) :
    ∃ (ev : Expr (declOf u) Γ Λ .bool)
      (q : Endblock (declOf u) (verOf u c) false (.bool :: Γ) Λ),
      lowEns u Γ Λ fn none v = .ok ev ∧
      lowEndL (l := false) u c _ (fn.mitBindungB x) n Λ [] ss = .ok (q, tail) ∧
      b = .bind ev q := by
  rw [lowEndL_succ] at h
  simp only [lowEndStep, lowStufe_ende] at h
  cases hv : lowEns u Γ Λ fn none v with
  | error e => simp only [hv, Except.bind] at h; cases h
  | ok ev =>
    simp only [hv, Except.bind] at h
    split at h
    · rename_i e he
      simp only [he, Except.bind] at h
      cases h
    · rename_i v hv
      obtain ⟨q, tail'⟩ := v
      simp only [hv, Except.bind, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨ev, q, (by first | exact hv | rfl | simp_all), (by first | exact hv | rfl | simp_all), rfl⟩

theorem lowEndL_bindCall_ok {Γ : Ctx} {fn : UFn} {n : Nat}
    {Λ : List (Res (declOf u))} {x g : String} {args : List UArg} {ss tail : List UStmt}
    {b : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowEndL (l := false) u c Γ fn (n + 1) Λ [] (.bindCall x g args :: ss) = .ok (b, tail)) :
    ∃ (head : RufKopf u c Γ Λ) (ty : Ty) (he : (declOf u).erg head.callee = some ty)
      (hr : (declOf u).gruende head.callee = 0)
      (q : Endblock (declOf u) (verOf u c) false (ty :: Γ) (nach (declOf u) head.callee Λ)),
      lowRufKopf u c Γ fn Λ g args = .ok head ∧
      lowEndL (l := false) u c _ (mitRuf u fn x head.callee ty) n
        (nach (declOf u) head.callee Λ) [] ss = .ok (q, tail) ∧
      b = .bindCall head.callee head.args he head.hp hr q := by
  rw [lowEndL_succ] at h
  simp only [lowEndStep, lowStufe_ende] at h
  cases hk : lowRufKopf u c Γ fn Λ g args with
  | error e => simp only [hk, Except.bind] at h; cases h
  | ok head =>
    simp only [hk, Except.bind] at h
    unfold withErg at h
    split at h
    · cases h
    · rename_i ty he
      cases hq : lowEndL (l := false) u c _ (mitRuf u fn x head.callee ty) n
          (nach (declOf u) head.callee Λ) [] ss with
      | error e => simp only [hq, Except.bind] at h; cases h
      | ok p =>
        obtain ⟨q, tail'⟩ := p
        simp only [hq, Except.bind] at h
        split at h
        · rename_i hr
          cases h
          exact ⟨head, ty, he, hr, q, (by first | exact hk | rfl | simp_all), hq, rfl⟩
        · cases h

/-- Invert the common structured-prefix continuation without unfolding either body. -/
theorem lowEndL_struct_result {Γ : Ctx} {fn : UFn} {n : Nat} {Λ : List (Res (declOf u))}
    {st : UStmt} {ss tail : List UStmt} {b : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : ((lowStructL (l := false) u c Γ fn n Λ [] st ss).bind (fun p =>
      (lowEndL (l := false) u c Γ fn n p.1.1 [] p.2).bind
        (fun q => .ok (.cons p.1.2 q.1, q.2)))) = .ok (b, tail)) :
    ∃ (Λ₁ : List (Res (declOf u))) (gs : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁)
      (rest : List UStmt) (q : Endblock (declOf u) (verOf u c) false Γ Λ₁),
      lowStructL (l := false) u c Γ fn n Λ [] st ss = .ok (⟨Λ₁, gs⟩, rest) ∧
      lowEndL (l := false) u c Γ fn n Λ₁ [] rest = .ok (q, tail) ∧ b = .cons gs q := by
  cases hg : lowStructL (l := false) u c Γ fn n Λ [] st ss with
  | error e => simp only [hg, Except.bind] at h; cases h
  | ok p =>
    obtain ⟨⟨Λ₁, gs⟩, rest⟩ := p
    simp only [hg, Except.bind] at h
    cases hq : lowEndL (l := false) u c Γ fn n Λ₁ [] rest with
    | error e => simp only [hq, Except.bind] at h; cases h
    | ok p =>
      obtain ⟨q, tail'⟩ := p
      simp only [hq, Except.bind] at h
      cases h
      exact ⟨Λ₁, gs, rest, q, (by first | exact hg | rfl | simp_all), hq, rfl⟩

/-- Ordinary structured prefixes use the same block lowering as nested sequences. -/
theorem lowEndL_struct_ok {Γ : Ctx} {fn : UFn} {n : Nat} {Λ : List (Res (declOf u))}
    {st : UStmt} {ss tail : List UStmt} {b : Endblock (declOf u) (verOf u c) false Γ Λ}
    (hs : (∃ cnd, st = .ifBeg cnd) ∨ (∃ x tab, st = .loopBeg x tab .tru))
    (h : lowEndL (l := false) u c Γ fn (n + 1) Λ [] (st :: ss) = .ok (b, tail)) :
    ∃ (Λ₁ : List (Res (declOf u))) (gs : Stmt (declOf u) (verOf u c) false Γ Λ Λ₁)
      (rest : List UStmt) (q : Endblock (declOf u) (verOf u c) false Γ Λ₁),
      lowStructL (l := false) u c Γ fn n Λ [] st ss = .ok (⟨Λ₁, gs⟩, rest) ∧
      lowEndL (l := false) u c Γ fn n Λ₁ [] rest = .ok (q, tail) ∧ b = .cons gs q := by
  rw [lowEndL_succ] at h
  have hd : lowEndStep (l := false) u c (lowStufe u c n) Γ fn Λ [] (st :: ss) =
      (lowStructL (l := false) u c Γ fn n Λ [] st ss).bind (fun p =>
        (lowEndL (l := false) u c Γ fn n p.1.1 [] p.2).bind
          (fun q => .ok (.cons p.1.2 q.1, q.2))) := by
    rcases hs with ⟨cnd, rfl⟩ | ⟨x, tab, rfl⟩ <;> rfl
  rw [hd] at h
  exact lowEndL_struct_result h

end Gabbro.Bruecke
