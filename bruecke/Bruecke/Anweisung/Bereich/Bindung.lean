module
public import Bruecke.Anweisung.Bereich.Lesen
public import Bruecke.Anweisung.Zweig.Kopf
@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
variable {u : UProg} {c : Fin u.fns.length}

/-- Rest agreement does not need the inferred type to agree between the two scope views. -/
theorem lowEnd_bindW_ok {l : Bool} {n : Nat} {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} {x : String} {d : Option Ty} {v : USide}
    {ss tail : List UStmt} {ending : Endblock (declOf u) (verOf u c) l Γ Λ}
    (h : lowEndL (l := l) u c Γ fn (n + 1) Λ [] (.bindW x d v :: ss) = .ok (ending, tail)) :
    ∃ (w : LowWert u Γ Λ) (rest : Endblock (declOf u) (verOf u c) l (w.ty :: Γ) Λ),
      lowBindW u Γ Λ fn d v = .ok w ∧
      lowEndL (l := l) u c (w.ty :: Γ) (fn.mitWert x w.ty) n Λ [] ss =
        .ok (rest, tail) ∧ ending = .bind w.term rest := by
  rw [lowEndL_succ] at h
  simp only [lowEndStep, lowStufe_ende] at h
  cases hw : lowBindW u Γ Λ fn d v with
  | error err => simp only [hw, Except.bind] at h; cases h
  | ok w =>
    simp only [hw, Except.bind] at h
    cases hr : lowEndL (l := l) u c (w.ty :: Γ) (fn.mitWert x w.ty) n Λ [] ss with
    | error err => simp only [hr, Except.bind] at h; cases h
    | ok p =>
      rcases p with ⟨rest, remaining⟩
      simp only [hr, Except.bind] at h
      cases h
      exact ⟨w, rest, (by first | exact hw | rfl), hr, rfl⟩

/-- Ending record locals use the canonical binder, including its inference path. -/
theorem lowEnd_bindRecord_ok {l : Bool} {n : Nat} {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} {x : String} {d : Option Ty} {v : USide}
    {id : Nat} {fs : List Ty} {ss tail : List UStmt}
    {ending : Endblock (declOf u) (verOf u c) l Γ Λ}
    (ht : recordBinderType u fn d v = some (.prod id fs))
    (h : lowEndL (l := l) u c Γ fn (n + 1) Λ [] (.bindW x d v :: ss) = .ok (ending, tail)) :
    ∃ (ev : Expr (declOf u) Γ Λ (.prod id fs))
      (rest : Endblock (declOf u) (verOf u c) l (.prod id fs :: Γ) Λ),
      lowWertAtE u Γ Λ fn none (.prod id fs) v = .ok ev ∧
      lowEndL (l := l) u c (.prod id fs :: Γ) (fn.mitWert x (.prod id fs)) n Λ [] ss =
        .ok (rest, tail) ∧ ending = .bind ev rest := by
  obtain ⟨w, rest, hw, hr, rfl⟩ := lowEnd_bindW_ok h
  obtain ⟨ev, hev, rfl⟩ := lowBindW_record ht hw
  exact ⟨ev, rest, hev, hr, rfl⟩

theorem lowEnd_bind_ok {l : Bool} {n : Nat} {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} {x : String} {d : Option (Int × Int)} {v : USide}
    {ss tail : List UStmt} {ending : Endblock (declOf u) (verOf u c) l Γ Λ}
    (h : lowEndL (l := l) u c Γ fn (n + 1) Λ [] (.bind x d v :: ss) = .ok (ending, tail)) :
    ∃ (ls : LowSide u Γ Λ)
      (rest : Endblock (declOf u) (verOf u c) l (.int ls.range.1 ls.range.2 :: Γ) Λ),
      lowBindWert u Γ Λ fn d v = .ok ls ∧
      lowEndL (l := l) u c (.int ls.range.1 ls.range.2 :: Γ) (fn.mitBindung x ls.range)
        n Λ [] ss = .ok (rest, tail) ∧ ending = .bind ls.term rest := by
  rw [lowEndL_succ] at h
  simp only [lowEndStep, lowStufe_ende] at h
  cases hv : lowBindWert u Γ Λ fn d v with
  | error err => simp only [hv, Except.bind] at h; cases h
  | ok ls =>
    simp only [hv, Except.bind] at h
    cases hr : lowEndL (l := l) u c (.int ls.range.1 ls.range.2 :: Γ)
        (fn.mitBindung x ls.range) n Λ [] ss with
    | error err => simp only [hr, Except.bind] at h; cases h
    | ok p =>
      rcases p with ⟨rest, remaining⟩
      simp only [hr, Except.bind] at h
      cases h
      exact ⟨ls, rest, (by first | exact hv | rfl), hr, rfl⟩

theorem lowEnd_bindMut_ok {l : Bool} {n : Nat} {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} {x : String} {lo hi : Int} {v : USide}
    {ss tail : List UStmt} {ending : Endblock (declOf u) (verOf u c) l Γ Λ}
    (h : lowEndL (l := l) u c Γ fn (n + 1) Λ [] (.bindMut x lo hi v :: ss) = .ok (ending, tail)) :
    ∃ (ev : Expr (declOf u) Γ Λ (.int lo hi))
      (rest : Endblock (declOf u) (verOf u c) l (.int lo hi :: Γ) Λ),
      lowWertAt u Γ Λ fn lo hi v = .ok ev ∧
      lowEndL (l := l) u c (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) n Λ [] ss =
        .ok (rest, tail) ∧ ending = .bind ev rest := by
  rw [lowEndL_succ] at h
  simp only [lowEndStep, lowStufe_ende] at h
  cases hv : lowWertAt u Γ Λ fn lo hi v with
  | error err => simp only [hv, Except.bind] at h; cases h
  | ok ev =>
    simp only [hv, Except.bind] at h
    cases hr : lowEndL (l := l) u c (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) n Λ [] ss with
    | error err => simp only [hr, Except.bind] at h; cases h
    | ok p =>
      rcases p with ⟨rest, remaining⟩
      simp only [hr, Except.bind] at h
      cases h
      exact ⟨ev, rest, (by first | exact hv | rfl), hr, rfl⟩

theorem lowEnd_bindB_ok {l : Bool} {n : Nat} {Γ : Ctx} {fn : UFn}
    {Λ : List (Res (declOf u))} {x : String} {v : UEns}
    {ss tail : List UStmt} {ending : Endblock (declOf u) (verOf u c) l Γ Λ}
    (h : lowEndL (l := l) u c Γ fn (n + 1) Λ [] (.bindB x v :: ss) = .ok (ending, tail)) :
    ∃ (ev : Expr (declOf u) Γ Λ .bool)
      (rest : Endblock (declOf u) (verOf u c) l (.bool :: Γ) Λ),
      lowEns u Γ Λ fn none v = .ok ev ∧
      lowEndL (l := l) u c (.bool :: Γ) (fn.mitBindungB x) n Λ [] ss =
        .ok (rest, tail) ∧ ending = .bind ev rest := by
  rw [lowEndL_succ] at h
  simp only [lowEndStep, lowStufe_ende] at h
  cases hv : lowEns u Γ Λ fn none v with
  | error err => simp only [hv, Except.bind] at h; cases h
  | ok ev =>
    simp only [hv, Except.bind] at h
    cases hr : lowEndL (l := l) u c (.bool :: Γ) (fn.mitBindungB x) n Λ [] ss with
    | error err => simp only [hr, Except.bind] at h; cases h
    | ok p =>
      rcases p with ⟨rest, remaining⟩
      simp only [hr, Except.bind] at h
      cases h
      exact ⟨ev, rest, (by first | exact hv | rfl), hr, rfl⟩

end Gabbro.Bruecke
