import Grammatik.Logik.WP.Ruf

/-!
# GabbroV over machine G: structural rules per construct

Each rule states the weakest precondition of one construct through the weakest preconditions of its parts (or, for a
leaf, through the outcome it produces), as an `↔`: sound and complete. A proof then follows the program step by step.
-/

namespace Gabbro.Grammatik.WP

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

section Regeln

variable (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {l : Bool} {Γ : Ctx}

/-- `if c { t } else { e }`. -/
theorem wpS_ite {Λ Λ' : List (Res D)} (c : Expr D Γ Λ .bool) (t e : Block D V l Γ Λ Λ') (Q : Ausgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ) :
    wpS O passes R (.ite c t e) Q σ ρ ↔
      if wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) then wpB O passes R t Q (σ.lese Λ c.orte) ρ
      else wpB O passes R e Q (σ.lese Λ c.orte) ρ := by
  unfold wpS wpB
  simp only [execStmt]
  rw [apply_ite Q]

/-- `return e;` as a statement. -/
theorem wpS_ret {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) (Q : Ausgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ) :
    wpS O passes R (.ret e hΛ) Q σ ρ ↔
      Q (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) := Iff.rfl

/-- `return e;` ending a body. -/
theorem wpE_ret {Λ : List (Res D)} (e : ErgExpr D Γ Λ V.erg) (hΛ : Λ.Perm V.ende) (Q : EndAusgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ) :
    wpE O passes R (.ret e hΛ) Q σ ρ ↔
      Q (.zurueck (σ.lese Λ e.orte) (evalErg (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) := Iff.rfl

/-- The postcondition a statement owes in front of the rest of an end block. -/
def weiterE {Λ' : List (Res D)} (rest : Endblock D V l Γ Λ') (Q : EndAusgang V l Γ → Prop) :
    Ausgang V l Γ → Prop
  | .ok σ' ρ' => wpE O passes R rest Q σ' ρ'
  | .zurueck σ' v => Q (.zurueck σ' v)
  | .why σ' r => Q (.why σ' r)
  | .leave h σ' ρ' => Q (.leave h σ' ρ')
  | .next h σ' ρ' => Q (.next h σ' ρ')
  | .logik e => Q (.logik e)
  | .hardware e => Q (.hardware e)

/-- **Sequence in an end block.** -/
theorem wpE_cons {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') (rest : Endblock D V l Γ Λ')
    (Q : EndAusgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpE O passes R (.cons s rest) Q σ ρ ↔ wpS O passes R s (weiterE O passes R rest Q) σ ρ := by
  unfold wpE wpS
  simp only [execEnd]
  cases execStmt O passes R s σ ρ <;> rfl

/-- `let x = narrow e to lo .. hi else { … }; rest`. -/
theorem wpB_narrow {Λ Λ' : List (Res D)} {lo hi : Int} (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int)
    (sonst : Endblock D V l Γ Λ) (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ') (Q : Ausgang V l Γ → Prop)
    (σ : World D) (ρ : Env D Γ) :
    wpB O passes R (.narrow e lo' hi' sonst rest) Q σ ρ ↔
      if h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
          (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' then
        wpB O passes R rest (fun o => Q o.schrumpf) (σ.lese Λ e.orte)
          (.cons ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h.1, h.2⟩ ρ)
      else wpE O passes R sonst (fun eo => Q eo.zuAusgang) (σ.lese Λ e.orte) ρ := by
  unfold wpB wpE
  simp only [execBlock]
  rw [apply_dite Q]

/-- What a binding call makes of the callee's outcome. -/
def bindRufB {Λ' Λ'' : List (Res D)} {τ : Ty} {f : D.Fn} (he : D.erg f = some τ) (hr : D.gruende f = 0)
    (rest : Block D V l (τ :: Γ) Λ' Λ'') (Q : Ausgang V l Γ → Prop) (ρ : Env D Γ) : RufAusgang f → Prop
  | .ok σ' v => wpB O passes R rest (fun o => Q o.schrumpf) σ' (.cons (ergWert he v) ρ)
  | .why _ r => keinGrund hr r
  | .logik e => Q (.logik e)
  | .hardware e => Q (.hardware e)

/-- **`let x = f(args); rest`**, exactly. -/
theorem wpB_bindCall {Λ Λ' : List (Res D)} {τ : Ty} (f : D.Fn) (args : Args D Γ Λ (D.params f))
    (he : D.erg f = some τ) (hp : RufPasst D V (D.signatur f) Λ) (hr : D.gruende f = 0)
    (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ') (Q : Ausgang V l Γ → Prop) (σ : World D) (ρ : Env D Γ) :
    wpB O passes R (.bindCall f args he hp hr rest) Q σ ρ ↔
      bindRufB O passes R he hr rest Q ρ
        (R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ)) := by
  unfold wpB
  simp only [execBlock]
  cases R f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) with
  | ok σ' v => rfl
  | why _ r => exact (Fin.cast hr r).elim0
  | logik e => rfl
  | hardware e => rfl

/-- **`let x = f(args); rest` against a specification.** -/
theorem wpB_bindCall_spez {S : Spez D} (hR : Erfuellt S R) {Λ Λ' : List (Res D)} {τ : Ty} (f : D.Fn)
    (args : Args D Γ Λ (D.params f)) (he : D.erg f = some τ) (hp : RufPasst D V (D.signatur f) Λ)
    (hr : D.gruende f = 0) (rest : Block D V l (τ :: Γ) (nach D f Λ) Λ') (Q : Ausgang V l Γ → Prop) (σ : World D)
    (ρ : Env D Γ)
    (h : ∀ out, S f (σ.lese Λ args.orte) (evalArgs (σ.lese Λ args.orte) args (σ.lese Λ args.orte) ρ) out →
      bindRufB O passes R he hr rest Q ρ out) :
    wpB O passes R (.bindCall f args he hp hr rest) Q σ ρ :=
  (wpB_bindCall O passes R f args he hp hr rest Q σ ρ).2 (h _ (hR f _ _))

end Regeln

end Gabbro.Grammatik.WP
