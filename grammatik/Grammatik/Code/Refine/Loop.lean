import Grammatik.Code.Refine.Stmt

/-
  File:      Grammatik/Code/Refine/Loop.lean
  Subject:   TRACK L, PHASE L1 -- THE LOOP REFINEMENTS: what the source says about a loop, from what
             the IR says about one pass of its body.

  Each loop theorem takes, as a hypothesis, the refinement of the BODY (`IHb`: what `lowerB_ok`
  says for the body, with the loop's `leave` and `next` targets), and proves the refinement of the
  whole loop by induction on the loop's own measure:
    * `forever_ok` -- `forever`: induction on the fuel `passes`;
  The loop invariants of the source (`inv`) are facts the IR never evaluates: a failed invariant is
  the source outcome `logik`, which relates to no IR run, so the IR needs no test.
-/

namespace Gabbro.Code.Lower

variable [Conf]

open Gabbro.Grammatik (Deklaration World Env Wert Ctx Res Vertrag Orakel Ausgang EndAusgang RufAusgang
  ErgVal ErgExpr execStmt execBlock execEnd eval evalErg Zahl foreverLauf wahr?)

variable {D : Deklaration} {V : Vertrag D}

/-- **`forever`.** The body is lowered at the loop's entry label `lb`, falls through to `lb`
    (`next` and the end of the body both jump to `lb`), and `leave` jumps to the continuation
    `k`. If the body refines its source (`IHb`, with targets `(k, lb)`), the loop does for every
    fuel. -/
theorem forever_ok {lay : Layout D} {cenv : List Reg} {lv : Lbl × Lbl} {O : Orakel D} {passes : Nat}
    {R : (f : D.Fn) → World D → Env D (D.params f) → RufAusgang f} {M : Modl} {S : Sees} {fn : Nat}
    {lb k : Lbl} {st st' : St} {ks : List Frame} {dst : Option Reg} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (a : D.Annahme) (inv : Gabbro.Grammatik.Expr D Γ Λ .bool)
    (body : Gabbro.Grammatik.Block D V true Γ Λ Λ)
    (IHb : ∀ (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ →
      WfL lay m → (∀ x ∈ cenv, x < st.r) →
      OutOk lay cenv (k, lb) M S fn lb lb st' m rs ks dst (execBlock O passes R body σ ρ)) :
    ∀ (n : Nat) (σ : World D) (ρ : Env D Γ) (m : Mem) (rs : Regs), Rep lay σ m → EnvRep lay rs m cenv ρ →
      WfL lay m → (∀ x ∈ cenv, x < st.r) →
      OutOk lay cenv lv M S fn lb k st' m rs ks dst
        (foreverLauf a (fun σ ρ => execBlock O passes R body σ ρ)
          (fun σ ρ => (σ.lese Λ inv.orte, wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ)))
          n σ ρ : Ausgang V l Γ) := by
  intro n
  induction n with
  | zero =>
      intro σ ρ m rs hR hE hW hc
      simp only [foreverLauf, OutOk]
  | succ n ih =>
      intro σ ρ m rs hR hE hW hc
      simp only [foreverLauf]
      by_cases hi : wahr? (eval (σ.lese Λ inv.orte) inv (σ.lese Λ inv.orte) ρ) = false
      · simp [hi, OutOk]
      · rw [if_neg hi]
        have IH1 := IHb (σ.lese Λ inv.orte) ρ m rs hR hE hW hc
        rcases hx : execBlock O passes R body (σ.lese Λ inv.orte) ρ with ⟨σ1, ρ1⟩ | ⟨σ1, v1⟩ | ⟨σ1, r1⟩ |
          ⟨h1, σ1, ρ1⟩ | ⟨h1, σ1, ρ1⟩ | e1 | e1
        · rw [hx] at IH1
          obtain ⟨m1, rs1, hr1, hP1⟩ := IH1
          obtain ⟨hRp, hEp, hWp, hcp⟩ := hP1
          simp only [hx]
          exact outok_lift hr1 _ (ih σ1 ρ1 m1 rs1 hRp hEp hWp hc)
        · rw [hx] at IH1
          simp only [hx]
          exact IH1
        · simp only [hx, OutOk]
        · rw [hx] at IH1
          simp only [hx]
          exact IH1
        · rw [hx] at IH1
          obtain ⟨m1, rs1, hr1, hP1⟩ := IH1
          obtain ⟨hRp, hEp, hWp, hcp⟩ := hP1
          simp only [hx]
          exact outok_lift hr1 _ (ih σ1 ρ1 m1 rs1 hRp hEp hWp hc)
        · simp only [hx, OutOk]
        · simp only [hx, OutOk]

end Gabbro.Code.Lower
