module

public import Bruecke.Ausdruck.IntegerOps

@[expose] public section

namespace Gabbro.Bruecke
open Gabbro.Grammatik
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg

/-- On successfully evaluated integer operands, every binary expression uses `binop`.
The boolean-only operators also agree: both sides refuse integer operands. -/
theorem eval_bin_int (op : Gabbro.Body.BinOp) (s : Gabbro.Body.State)
    (a b : Gabbro.Body.Expr) (x y : Int)
    (ha : Gabbro.Body.eval s a = some (.int x))
    (hb : Gabbro.Body.eval s b = some (.int y)) :
    Gabbro.Body.eval s (.bin op a b) = Gabbro.Body.binop op (.int x) (.int y) := by
  cases op <;> simp only [Gabbro.Body.eval, ha, hb] <;> rfl

/-- The shared binary-expression simulation. The recursive hypotheses carry the operands;
the operator premise checks the actual canonical lowering, including all its refusals. -/
theorem lowZwei_sim {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    {fn : UFn} {er : Option Ty} {x y : USide} {wv : LowWert u Γ Λ}
    {eB : Gabbro.Body.Expr}
    (lower : LowSide u Γ Λ → LowSide u Γ Λ → Except String (LowSide u Γ Λ))
    (op : Gabbro.Body.BinOp)
    (σ₀ σ : World (declOf u)) (ρ : Env (declOf u) Γ)
    (w : Gabbro.Body.World) (β : Gabbro.Body.Binding)
    (hOp : ∀ {a b c}, lower a b = .ok c →
      Gabbro.Body.binop op
        (valOf (.int a.range.1 a.range.2) (eval σ₀ a.term σ ρ))
        (valOf (.int b.range.1 b.range.2) (eval σ₀ b.term σ ρ)) =
        some (valOf (.int c.range.1 c.range.2) (eval σ₀ c.term σ ρ)))
    (hx : ∀ {v e}, lowWertE u Γ Λ fn er x = .ok v →
      numericSideExprG u fn x = some e → ∃ a : LowSide u Γ Λ, v = a.wert ∧
        Gabbro.Body.eval ⟨w, β⟩ e =
          some (valOf (.int a.range.1 a.range.2) (eval σ₀ a.term σ ρ)))
    (hy : ∀ {v e}, lowWertE u Γ Λ fn er y = .ok v →
      numericSideExprG u fn y = some e → ∃ b : LowSide u Γ Λ, v = b.wert ∧
        Gabbro.Body.eval ⟨w, β⟩ e =
          some (valOf (.int b.range.1 b.range.2) (eval σ₀ b.term σ ρ)))
    (h : (lowZwei lower (zahlVon (lowWertE u Γ Λ fn er x))
      (zahlVon (lowWertE u Γ Λ fn er y))).map LowSide.wert = .ok wv)
    (hb : binE op (numericSideExprG u fn x) (numericSideExprG u fn y) = some eB) :
    ∃ c : LowSide u Γ Λ, wv = c.wert ∧ Gabbro.Body.eval ⟨w, β⟩ eB =
      some (valOf (.int c.range.1 c.range.2) (eval σ₀ c.term σ ρ)) := by
  cases hsx : numericSideExprG u fn x with
  | none => simp [hsx, binE] at hb
  | some ex =>
    cases hsy : numericSideExprG u fn y with
    | none => simp [hsx, hsy, binE] at hb
    | some ey =>
      simp only [hsx, hsy, binE, Option.some.injEq] at hb
      subst eB
      cases hlx : lowWertE u Γ Λ fn er x with
      | error err => simp [hlx, zahlVon, lowZwei, Except.map] at h
      | ok vx =>
        obtain ⟨a, rfl, ha⟩ := hx hlx hsx
        cases hly : lowWertE u Γ Λ fn er y with
        | error err => simp [hlx, hly, zahlVon, LowWert.zahl, LowSide.wert, lowZwei, Except.map] at h
        | ok vy =>
          obtain ⟨b, rfl, hb⟩ := hy hly hsy
          simp only [hlx, hly, zahlVon, LowWert.zahl, LowSide.wert, lowZwei] at h
          cases hop : lower a b with
          | error err => simp [hop, Except.map] at h
          | ok c =>
            simp only [hop, Except.map, Except.ok.injEq] at h
            subst wv
            refine ⟨c, rfl, ?_⟩
            rw [eval_bin_int op ⟨w, β⟩ ex ey _ _ ha hb]
            exact hOp hop

end Gabbro.Bruecke
