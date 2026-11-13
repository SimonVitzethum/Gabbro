module
public import Bruecke.Anweisung.Lokal.Ruf
@[expose] public section

/-!
# C4, part 3: `let`, `let mut` and assignment -- one G step, one Body step

`let x = v;` lowers to `Endblock.bind` of the side's term (`lowBindWert`), `let mut x : T = v;` to
`Endblock.bind` of the fitted term (`lowWertAt`), `x = v;` to `Stmt.assignVar` (`lowSetVarL`, at the
declared type of `x` through `lowWertAtE`). The Body statement of all three is `bindName x e`
(`schrittB`). From related states, the Body step binds `x` to the number the G term evaluates to,
and the states after it are related -- in the scope with `x` for a binder
(`lrel_mitBindung`), with the updated position for an assignment (`lrel_set`).
-/

namespace Gabbro.Bruecke

open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.UebersetzeAllg2

variable {u : UProg}

/-! ## 1. The values -/

theorem lowBindWert_side {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn}
    {d : Option (Int × Int)} {v : USide} {ls : LowSide u Γ Λ}
    (h : lowBindWert u Γ Λ fn d v = .ok ls) : lowSideVal u Γ Λ fn v = .ok ls := by
  unfold lowBindWert at h
  split at h
  · cases h
  · rename_i s' hs'
    split at h
    · cases h
      exact hs'
    · split at h
      · cases h
        exact hs'
      · cases h

/-- Fitting a number into a range (`fitW`) keeps its number. -/
theorem fitW_int_val {Γ : Ctx} {Λ : List (Res (declOf u))} {a b lo hi : Int}
    (t : Expr (declOf u) Γ Λ (.int a b)) {e : Expr (declOf u) Γ Λ (.int lo hi)}
    (h : fitW (.int lo hi) (⟨.int a b, t⟩ : LowWert u Γ Λ) = .ok e)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) :
    valOf (.int lo hi) (eval σ₀ e σ ρ) = valOf (.int a b) (eval σ₀ t σ ρ) := by
  simp only [fitW] at h
  split at h
  · rename_i hty
    cases h
    have hty' : Ty.int a b = Ty.int lo hi := hty
    injection hty' with h1 h2
    subst h1
    subst h2
    rfl
  · repeat' split at h
    all_goals first
      | (cases h; rfl)
      | (cases h; done)

/-- **A side at the declared number type of a local** (`lowWertAtE` at `.int lo hi`, the checking
    mode of an assignment) keeps its number. -/
theorem lowWertAtE_int_sim {Γ : Ctx} {Λ : List (Res (declOf u))} {fn : UFn} {lo hi : Int}
    {sd : USide} {e : Expr (declOf u) Γ Λ (.int lo hi)} {eB : Gabbro.Body.Expr}
    (h : lowWertAtE u Γ Λ fn none (.int lo hi) sd = .ok e) (hb : sideExpr u fn sd = some eB)
    (hA : ArtStimmt fn) (hT : TabEindeutig u)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ) (wW : Gabbro.Body.World)
    (β : Gabbro.Body.Binding) (hW : WRel u σ wW) (hL : LRel fn 0 ρ β) :
    Gabbro.Body.eval ⟨wW, β⟩ eB = some (valOf (.int lo hi) (eval σ₀ e σ ρ)) := by
  simp only [lowWertAtE, reduceCtorEq, false_implies, implies_true] at h
  split at h
  · rename_i lw hlw
    obtain ⟨ls, rfl, hev⟩ := lowWertE_sim (er := none) hlw hb hA hT σ₀ σ ρ wW β hW hL
    rw [hev, fitW_int_val ls.term h σ₀ σ ρ]
  · cases h

/-! ## 2. `let` -/

/-- **`let x = v;`** -- the Body step `bindName x eB` binds `x` to the number of the G term the
    binder puts first in the environment; the states after it are related in the scope with `x`. -/
theorem lowBind_sim {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))} {x : String}
    {d : Option (Int × Int)} {v : USide} {ls : LowSide u Γ Λ} {eB : Gabbro.Body.Expr}
    (h : lowBindWert u Γ Λ fn d v = .ok ls) (hb : sideExpr u fn v = some eB)
    (hU : UmfangB Γ fn) (hT : TabEindeutig u)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
    ∃ bv : Gabbro.Body.Value,
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB (.bindName x eB) s =
        .running ⟨s.world, Gabbro.Body.bindLocal s.local' x bv⟩) ∧
      WRel u (σ.lese Λ ls.term.orte) s.world ∧
      LRel (fn.mitBindung x ls.range) 0
        (Env.cons (eval (σ.lese Λ ls.term.orte) ls.term (σ.lese Λ ls.term.orte) ρ) ρ)
        (Gabbro.Body.bindLocal s.local' x bv) := by
  have hs := lowBindWert_side h
  have hWl : WRel u (σ.lese Λ ls.term.orte) s.world := wrel_slots u rfl hW
  have hv := lowSideVal_sim hs hb hU.art hT (σ.lese Λ ls.term.orte) (σ.lese Λ ls.term.orte)
    ρ s.world s.local' hWl hL
  refine ⟨valOf (.int ls.range.1 ls.range.2)
      (eval (σ.lese Λ ls.term.orte) ls.term (σ.lese Λ ls.term.orte) ρ),
    fun ρB => ?_, hWl, lrel_mitBindung hL x ls.range _ _ rfl⟩
  simp only [Gabbro.Body.step]
  rw [hv]

/-- **`let mut x : T = v;`** -- the same at the declared range. -/
theorem lowBindMut_sim {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))} {x : String}
    {lo hi : Int} {v : USide} {ev : Expr (declOf u) Γ Λ (.int lo hi)} {eB : Gabbro.Body.Expr}
    (h : lowWertAt u Γ Λ fn lo hi v = .ok ev) (hb : sideExpr u fn v = some eB)
    (hU : UmfangB Γ fn) (hT : TabEindeutig u)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
    ∃ bv : Gabbro.Body.Value,
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB (.bindName x eB) s =
        .running ⟨s.world, Gabbro.Body.bindLocal s.local' x bv⟩) ∧
      WRel u (σ.lese Λ ev.orte) s.world ∧
      LRel (fn.mitBindung x (lo, hi)) 0
        (Env.cons (eval (σ.lese Λ ev.orte) ev (σ.lese Λ ev.orte) ρ) ρ)
        (Gabbro.Body.bindLocal s.local' x bv) := by
  have hWl : WRel u (σ.lese Λ ev.orte) s.world := wrel_slots u rfl hW
  have hv := lowWertAt_sim h hb hU.art hT (σ.lese Λ ev.orte) (σ.lese Λ ev.orte)
    ρ s.world s.local' hWl hL
  refine ⟨valOf (.int lo hi) (eval (σ.lese Λ ev.orte) ev (σ.lese Λ ev.orte) ρ),
    fun ρB => ?_, hWl, lrel_mitBindung hL x (lo, hi) _ _ rfl⟩
  simp only [Gabbro.Body.step]
  rw [hv]

/-! ## 3. Assignment -/

/-- **`x = v;` on a number local** -- the G assignment writes the position of `x`, the Body
    rebinding `bindName x eB` writes the name `x`, with the same number; the world stays. -/
theorem lowSetVar_sim (c : Fin u.fns.length) {Γ : Ctx} {fn : UFn} {Λ : List (Res (declOf u))}
    {x : String} {v : USide} {g : Stmt (declOf u) (verOf u c) false Γ Λ Λ}
    {eB : Gabbro.Body.Expr}
    (h : lowSetVarL (l := false) u c Γ fn Λ x v = .ok g)
    (hn : numericParam fn x = true) (hb : sideExpr u fn v = some eB)
    (hU : UmfangB Γ fn) (hT : TabEindeutig u)
    (O : Orakel (declOf u)) (passes : Nat)
    (R : ∀ f : (declOf u).Fn, World (declOf u) → Env (declOf u) ((declOf u).params f) → RufAusgang f)
    (σ : World (declOf u)) (ρ : Env (declOf u) Γ) (s : Gabbro.Body.State)
    (hW : WRel u σ s.world) (hL : LRel fn 0 ρ s.local') :
    ∃ (σ₁ : World (declOf u)) (ρ₁ : Env (declOf u) Γ) (bv : Gabbro.Body.Value),
      execStmt O passes R g σ ρ = .ok σ₁ ρ₁ ∧ σ₁.slots = σ.slots ∧
      (∀ ρB : Gabbro.Body.Env, Gabbro.Body.step ρB (.bindName x eB) s =
        .running ⟨s.world, Gabbro.Body.bindLocal s.local' x bv⟩) ∧
      LRel fn 0 ρ₁ (Gabbro.Body.bindLocal s.local' x bv) := by
  have hA := hU.art
  unfold lowSetVarL at h
  split at h
  · cases h
  · rename_i j hj
    split at h
    · rename_i nm ty hty
      split at h
      · cases h
      · rename_i var hvar
        split at h
        · cases h
        · rename_i e he
          cases h
          have hn' := hn
          unfold numericParam at hn'
          rw [paramPos_find _ _ _ hj, hty] at hn'
          cases ty with
          | int lo hi =>
            have hWl : WRel u (σ.lese Λ e.orte) s.world := wrel_slots u rfl hW
            have hv := lowWertAtE_int_sim he hb hA hT (σ.lese Λ e.orte) (σ.lese Λ e.orte) ρ
              s.world s.local' hWl hL
            refine ⟨σ.lese Λ e.orte, ρ.set var (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ),
              valOf (.int lo hi) (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ), rfl, rfl,
              fun ρB => ?_, lrel_set hL hj var hvar _⟩
            simp only [Gabbro.Body.step]
            rw [hv]
          | _ => simp at hn'
    · cases h

end Gabbro.Bruecke
