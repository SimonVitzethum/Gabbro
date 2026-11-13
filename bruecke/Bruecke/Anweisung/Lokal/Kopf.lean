module
public import Bruecke.Anweisung.Lokal.Bindung
public import Bruecke.Lauf
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz.T2.Teil1
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatG.T3.Teil1
@[expose] public section

/-!
# C5, part 1: the shape of the body reader, and one step of the run

`lowBodyF` reads `let` and `let mut` itself (`Endblock.bind`, the scope one longer) and passes a
slot write, a call or an assignment to `lowStmtL` (its last case, `Endblock.cons`). These are the
three dispatch lemmas the run follows, the G facts of `Endblock.bind` (the binder's outcome is
the rest's, `EndAusgang.schrumpf`), and the canonical execution equations used by the carried run simulation.
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. The body reader -/

/-- The statements the body reader passes one by one to `lowStmtL` and the bridge carries. -/
def LeseEinzeln : UStmt → Prop
  | .assign .. | .assignTab .. | .assignGlob .. | .call .. | .setVar .. => True
  | _ => False

theorem lowBodyF_cons_ok (c : Fin u.fns.length) (r : URet) {Γ : Ctx} {fn : UFn} (s : UStmt)
    (ss : List UStmt) (hs : LeseEinzeln s) {Λ : List (Res (declOf u))} {n : Nat}
    {b0 : Endblock (declOf u) (verOf u c) false Γ Λ}
    (hb : lowBodyF u c Γ fn (n + 1) Λ (s :: ss) r = .ok b0) :
    ∃ (Λ' : List (Res (declOf u))) (st : Stmt (declOf u) (verOf u c) false Γ Λ Λ')
      (e : Endblock (declOf u) (verOf u c) false Γ Λ'),
      lowStmtL (l := false) u c Γ fn Λ s = .ok ⟨Λ', st⟩ ∧
        lowBodyF u c Γ fn n Λ' ss r = .ok e ∧ b0 = Endblock.cons st e := by
  have dispatch : lowBodyF u c Γ fn (n + 1) Λ (s :: ss) r =
      (match lowStmtL (l := false) u c Γ fn Λ s with
      | .error error => .error error
      | .ok ⟨Λ', st⟩ =>
        match lowBodyF u c Γ fn n Λ' ss r with
        | .error error => .error error
        | .ok ending => .ok (Endblock.cons st ending)) := by
    cases s
    case assign | assignTab | assignGlob | call | setVar =>
      rw [lowBodyF] <;> try simp
      all_goals
        split <;> rename_i hread
        all_goals erw [hread]
        all_goals dsimp only
        all_goals
          split <;> rename_i hrest
          all_goals erw [hrest]
          all_goals dsimp only
        all_goals rfl
    all_goals simp [LeseEinzeln] at hs
  rw [dispatch] at hb
  cases hst : lowStmtL (l := false) u c Γ fn Λ s with
  | error error => rw [hst] at hb; cases hb
  | ok result =>
    obtain ⟨Λ', st⟩ := result
    rw [hst] at hb
    dsimp only at hb
    cases he : lowBodyF u c Γ fn n Λ' ss r with
    | error error => rw [he] at hb; cases hb
    | ok e =>
      rw [he] at hb
      cases hb
      exact ⟨Λ', st, e, rfl, he, rfl⟩

theorem lowBodyF_bind_ok (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {n : Nat}
    {Λ : List (Res (declOf u))} {x : String} {d : Option (Int × Int)} {v : USide}
    {ss : List UStmt} {r : URet} {b0 : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowBodyF u c Γ fn (n + 1) Λ (.bind x d v :: ss) r = .ok b0) :
    ∃ (ls : LowSide u Γ Λ)
      (e : Endblock (declOf u) (verOf u c) false (.int ls.range.1 ls.range.2 :: Γ) Λ),
      lowBindWert u Γ Λ fn d v = .ok ls ∧
      lowBodyF u c (.int ls.range.1 ls.range.2 :: Γ) (fn.mitBindung x ls.range) n Λ ss r = .ok e ∧
      b0 = Endblock.bind ls.term e := by
  simp only [lowBodyF] at h
  split at h
  · cases h
  · rename_i ls hls
    split at h
    · cases h
    · rename_i e he
      cases h
      exact ⟨ls, e, hls, he, rfl⟩

theorem lowBodyF_bindMut_ok (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {n : Nat}
    {Λ : List (Res (declOf u))} {x : String} {lo hi : Int} {v : USide}
    {ss : List UStmt} {r : URet} {b0 : Endblock (declOf u) (verOf u c) false Γ Λ}
    (h : lowBodyF u c Γ fn (n + 1) Λ (.bindMut x lo hi v :: ss) r = .ok b0) :
    ∃ (ev : Expr (declOf u) Γ Λ (.int lo hi))
      (e : Endblock (declOf u) (verOf u c) false (.int lo hi :: Γ) Λ),
      lowWertAt u Γ Λ fn lo hi v = .ok ev ∧
      lowBodyF u c (.int lo hi :: Γ) (fn.mitBindung x (lo, hi)) n Λ ss r = .ok e ∧
      b0 = Endblock.bind ev e := by
  simp only [lowBodyF] at h
  split at h
  · cases h
  · rename_i ev hev
    split at h
    · cases h
    · rename_i e he
      cases h
      exact ⟨ev, e, hev, he, rfl⟩

/-! ## 2. The G side of a binder and of a statement -/

theorem execEnd_bind {D : Deklaration} {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (e : Expr D Γ Λ τ) (rest : Endblock D V false (τ :: Γ) Λ) (σ : World D) (ρ : Env D Γ) :
    execEnd O passes R (Endblock.bind e rest) σ ρ =
      (execEnd O passes R rest (σ.lese Λ e.orte)
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ)).schrumpf := by
  first
    | (simp only [execEnd]; done)
    | rfl

theorem execEnd_cons_ok {D : Deklaration} {V : Vertrag D} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (st : Stmt D V false Γ Λ Λ') (rest : Endblock D V false Γ Λ') (σ σ₁ : World D)
    (ρ ρ₁ : Env D Γ) (h : execStmt O passes R st σ ρ = .ok σ₁ ρ₁) :
    execEnd O passes R (Endblock.cons st rest) σ ρ = execEnd O passes R rest σ₁ ρ₁ := by
  simp only [execEnd, h]

theorem exec_cons_running (ρB : Gabbro.Body.Env) (x : Gabbro.Body.Stmt)
    (xs : List Gabbro.Body.Stmt) (s s₁ : Gabbro.Body.State)
    (h : Gabbro.Body.step ρB x s = .running s₁) :
    Gabbro.Body.exec ρB (x :: xs) s = Gabbro.Body.exec ρB xs s₁ := by
  simp only [Gabbro.Body.exec, h]

/-- The run's outcomes of a binder are the rest's. -/
theorem bind_lauf {D : Deklaration} {V : Vertrag D} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (e : Expr D Γ Λ τ) (rest : Endblock D V false (τ :: Γ) Λ) (σ : World D) (ρ : Env D Γ) :
    (∀ err, execEnd O passes R (Endblock.bind e rest) σ ρ = .logik err →
      execEnd O passes R rest (σ.lese Λ e.orte)
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) = .logik err) ∧
    (∀ σ' v, execEnd O passes R (Endblock.bind e rest) σ ρ = .zurueck σ' v →
      execEnd O passes R rest (σ.lese Λ e.orte)
        (Env.cons (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ) ρ) = .zurueck σ' v) := by
  refine ⟨fun err h => ?_, fun σ' v h => ?_⟩
  · rw [execEnd_bind] at h
    exact EndAusgang.schrumpf_logik h
  · rw [execEnd_bind] at h
    exact endSchrumpf_zurueck h

/-- The run's outcomes of a statement that continues are the rest's. -/
theorem cons_lauf {D : Deklaration} {V : Vertrag D} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (st : Stmt D V false Γ Λ Λ') (rest : Endblock D V false Γ Λ') (σ σ₁ : World D)
    (ρ ρ₁ : Env D Γ) (h : execStmt O passes R st σ ρ = .ok σ₁ ρ₁) :
    (∀ err, execEnd O passes R (Endblock.cons st rest) σ ρ = .logik err →
      execEnd O passes R rest σ₁ ρ₁ = .logik err) ∧
    (∀ σ' v, execEnd O passes R (Endblock.cons st rest) σ ρ = .zurueck σ' v →
      execEnd O passes R rest σ₁ ρ₁ = .zurueck σ' v) := by
  have hrun := execEnd_cons_ok O passes R st rest σ σ₁ ρ ρ₁ h
  exact ⟨fun err he => by rw [← hrun]; exact he, fun σ' v he => by rw [← hrun]; exact he⟩

end Gabbro.Bruecke
