module

public import Grammatik.Kern.Semantik.Semantik.T2

@[expose] public section

namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx}

/-- Bounded while uses retry's recursion, including its final condition read and
    propagation of returns, reasons, logic failures and named hardware outcomes.
    Negation changes only the test result; the recorded world is retained. -/
def whileLauf (schritt : World D → Env D Γ → Ausgang V true Γ)
    (cond : World D → Env D Γ → World D × Bool)
    (ueberlauf : World D → Env D Γ → Ausgang V l Γ) :
    Nat → World D → Env D Γ → Ausgang V l Γ :=
  retryLauf schritt (fun σ ρ => ((cond σ ρ).1, !(cond σ ρ).2)) ueberlauf

/-- At zero fuel a false condition succeeds; a true condition runs the handler
    from the world produced by the condition read. -/
theorem whileLauf_zero (schritt : World D → Env D Γ → Ausgang V true Γ)
    (cond : World D → Env D Γ → World D × Bool)
    (ueberlauf : World D → Env D Γ → Ausgang V l Γ) (σ : World D) (ρ : Env D Γ) :
    whileLauf schritt cond ueberlauf 0 σ ρ =
      if (cond σ ρ).2 = false then .ok (cond σ ρ).1 ρ
      else ueberlauf (cond σ ρ).1 ρ := by
  cases h : (cond σ ρ).2 <;> simp [whileLauf, retryLauf, h]

/-- Both normal fallthrough and `next` consume a pass and re-evaluate the
    condition. `leave` exits without another read or running the handler. -/
theorem whileLauf_succ (schritt : World D → Env D Γ → Ausgang V true Γ)
    (cond : World D → Env D Γ → World D × Bool)
    (ueberlauf : World D → Env D Γ → Ausgang V l Γ) (n : Nat)
    (σ : World D) (ρ : Env D Γ) :
    whileLauf schritt cond ueberlauf (n + 1) σ ρ =
      if (cond σ ρ).2 = false then .ok (cond σ ρ).1 ρ else
      match schritt (cond σ ρ).1 ρ with
      | .ok σ' ρ' => whileLauf schritt cond ueberlauf n σ' ρ'
      | .next _ σ' ρ' => whileLauf schritt cond ueberlauf n σ' ρ'
      | .leave _ σ' ρ' => .ok σ' ρ'
      | .zurueck σ' value => .zurueck σ' value
      | .why σ' reason => .why σ' reason
      | .logik e => .logik e
      | .hardware e => .hardware e := by
  cases h : (cond σ ρ).2 <;> simp [whileLauf, retryLauf, h] <;> rfl

/-- The actual model statement runs this recursion, with the same read-world
    threading as retry. This identity also applies to nonempty footprints. -/
theorem execStmt_wloop (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Λ : List (Res D)} (n : Nat) (c : Expr D Γ Λ .bool)
    (body : Block D V true Γ Λ Λ) (ueberlauf : Block D V l Γ Λ Λ)
    (σ : World D) (ρ : Env D Γ) :
    execStmt O passes R (.wloop n c body ueberlauf) σ ρ =
      whileLauf (fun σ ρ => execBlock O passes R body σ ρ)
        (fun σ ρ => let σ := σ.lese Λ c.orte; (σ, wahr? (eval σ c σ ρ)))
        (fun σ ρ => execBlock O passes R ueberlauf σ ρ) n σ ρ := rfl

end Gabbro.Grammatik
