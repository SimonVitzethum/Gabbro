module
public import Grammatik.Zielsatz.ZielOrt.Grundlage.ZielOrtGanz.T1
@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- Required narrowing at a block head passes in the actual read world. This is a fact derived
    from replay and KeineLogik, rather than a new premise for the program's caller. -/
def RequiredRangePrueftG (M : RufMaschineG D) (t : Faden) : Prop :=
  ∀ (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res D)) (ρ : Env D Γ) (lo hi lo' hi' : Int)
    (e : Expr D Γ Λ (.int lo hi))
    (rest : Block D (vertragVon D (M.faeden t).kopf.f) l (.int lo' hi' :: Γ) Λ Λ')
    (k : GRest D (vertragVon D (M.faeden t).kopf.f) l Γ Λ'),
    (M.faeden t).kopf.rest = ⟨l, Γ, Λ, ρ, .dann (.narrowRequired e lo' hi' rest) k⟩ →
    lo' ≤ (eval ((M.weltVon t).lese Λ e.orte) e ((M.weltVon t).lese Λ e.orte) ρ).n ∧
      (eval ((M.weltVon t).lese Λ e.orte) e ((M.weltVon t).lese Λ e.orte) ρ).n ≤ hi'

section Semantics
variable (O : Orakel D) (passes : Nat)
  (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
  {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {lo hi : Int}

/-- The success equation is the canonical read/eval followed by a typed binding and shrink. -/
theorem semV_narrowRequired_ok (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int)
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (h : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi') :
    semV O passes R (.dann (.narrowRequired e lo' hi' rest) k) σ ρ =
      semV O passes R (.dann rest (.schrumpf k)) (σ.lese Λ e.orte)
        (.cons (τ := .int lo' hi')
          ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n, h.1, h.2⟩ ρ) := by
  rw [semV_dann]
  simp only [execBlock]
  rw [dif_pos h]
  rfl

/-- A failed required range remains a logical capacity outcome through every continuation. -/
theorem semV_narrowRequired_falsch (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int)
    (rest : Block D V l (.int lo' hi' :: Γ) Λ Λ') (k : GRest D V l Γ Λ')
    (σ : World D) (ρ : Env D Γ)
    (h : ¬ (lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')) :
    semV O passes R (.dann (.narrowRequired e lo' hi' rest) k) σ ρ = .logik .kapazitaet := by
  rw [semV_dann]
  simp only [execBlock]
  rw [dif_neg h]
  exact weiterZ_logik O passes R k .kapazitaet
end Semantics

/-- Replay carries the required-range pass fact from the existing whole-body KeineLogik duty. -/
theorem fadenR_requiredRange {P : Programm D} {O : Orakel D} {passes : Nat} {Q : AxEns D}
    (hO : GutO O) (hRL : RegLokal O) (hQ : AxVertragO Q O)
    (hL : ∀ f, KeineLogik P passes Q f) {M : RufMaschineG D} (t : Faden)
    (hF : FadenR P O passes Q (M.faeden t) (M.weltVon t)) : RequiredRangePrueftG M t := by
  intro l Γ Λ Λ' ρ lo hi lo' hi' e rest k hr
  obtain ⟨H, HA, σ, hg, hok, hno⟩ := kopfR_keineLogik' hO hRL hQ hL hF.1 hr
  apply Classical.byContradiction
  intro failed
  apply hno .kapazitaet
  apply semV_narrowRequired_falsch
  intro passed
  apply failed
  have same := eval_gleichAuf e
    (fun _ member => hok.2.1 (List.mem_append_left _ member))
    (hg.lese Λ Λ e.orte e.orte) ρ
  rw [same] at passed
  exact passed

end Gabbro.Grammatik
