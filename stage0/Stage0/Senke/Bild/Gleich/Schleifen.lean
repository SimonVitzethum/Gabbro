/-
  File:      stage0/Stage0/Senke/Bild/Gleich/Schleifen.lean
  Subject:   Package P1 of the closed calls of the image theorem, part 2: the loop combinators and the indirect call
             dispatch keep outcomes related up to read events. The loop bodies are related on `≈` worlds (the
             induction hypothesis of the substitution), and the world-reading tests of the loops (invariant, selection,
             measure: `FunLG`) answer the same value and `≈` worlds on `≈` worlds -- each is a read followed by an
             expression, which does not see the trace (`funLG_lese`, `funLG_verbrauchSel`).
-/
module
public import Stage0.Senke.Bild.Gleich.Ausgang
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## 1. World-reading tests -/

/-- A world-reading function that answers the same value and `≈` worlds on `≈` worlds. -/
def FunLG {Γ : Ctx} {α : Type} (k : World D → Env D Γ → World D × α) : Prop :=
  ∀ (σ σ' : World D) (ρ : Env D Γ), WeltGleich σ σ' → WeltGleich (k σ ρ).1 (k σ' ρ).1 ∧ (k σ ρ).2 = (k σ' ρ).2

/-- A read of an expression's places followed by its value. -/
theorem funLG_lese {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {α : Type} (e : Expr D Γ Λ τ) (F : Wert D τ → α) :
    FunLG (fun (σ : World D) (ρ : Env D Γ) =>
      (σ.lese Λ e.orte, F (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ))) :=
  fun _ _ ρ h => ⟨h.lese Λ e.orte, congrArg F ((h.lese Λ e.orte).wert' e ρ)⟩

/-- The selection of a consuming traversal. -/
theorem funLG_verbrauchSel {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab)
    (member : Expr D (.index (D.count t) :: Γ) Λ .bool)
    (edge : Expr D (.index (D.count t) :: .index (D.count t) :: Γ) Λ .bool) :
    FunLG (verbrauchSel t member edge) := by
  intro σ σ' ρ h
  have h' := h.lese Λ (member.orte ++ edge.orte)
  have hm : ∀ ρ', eval (σ.lese Λ (member.orte ++ edge.orte)) member (σ.lese Λ (member.orte ++ edge.orte)) ρ' =
      eval (σ'.lese Λ (member.orte ++ edge.orte)) member (σ'.lese Λ (member.orte ++ edge.orte)) ρ' :=
    fun ρ' => h'.wert' member ρ'
  have he : ∀ ρ', eval (σ.lese Λ (member.orte ++ edge.orte)) edge (σ.lese Λ (member.orte ++ edge.orte)) ρ' =
      eval (σ'.lese Λ (member.orte ++ edge.orte)) edge (σ'.lese Λ (member.orte ++ edge.orte)) ρ' :=
    fun ρ' => h'.wert' edge ρ'
  refine ⟨h', ?_⟩
  simp only [verbrauchSel, hm, he]

/-! ## 2. The loops -/

section Schleifen

variable {V : Vertrag D} {Er : Fehlermarke D → Prop}

theorem traverseLauf_lg {l : Bool} {Γ : Ctx} {τ : Ty}
    {s₁ s₂ : World D → Env D (τ :: Γ) → Ausgang V true (τ :: Γ)} {inv : World D → Env D Γ → World D × Bool}
    (hs : ∀ σ σ' ρ, WeltGleich σ σ' → AusLG Er (s₁ σ ρ) (s₂ σ' ρ)) (hinv : FunLG inv) :
    ∀ (ks : List (Wert D τ)) (σ σ' : World D) (ρ : Env D Γ), WeltGleich σ σ' →
      AusLG Er (traverseLauf (l := l) s₁ inv ks σ ρ) (traverseLauf (l := l) s₂ inv ks σ' ρ)
  | [], σ, σ', ρ, h => by
      obtain ⟨hw, hb⟩ := hinv σ σ' ρ h
      simp only [traverseLauf]
      exact AusLG.ite_eq hb (.ok hw) (.logik _)
  | k :: ks, σ, σ', ρ, h => by
      obtain ⟨hw, hb⟩ := hinv σ σ' ρ h
      simp only [traverseLauf]
      rw [hb]
      by_cases hc : (inv σ' ρ).2 = false
      · rw [if_pos hc, if_pos hc]; exact .logik _
      · rw [if_neg hc, if_neg hc]
        have hst := hs _ _ (.cons k ρ) hw
        generalize s₁ (inv σ ρ).1 (.cons k ρ) = o₁ at hst ⊢
        generalize s₂ (inv σ' ρ).1 (.cons k ρ) = o₂ at hst ⊢
        cases hst with
        | ok hw' => exact traverseLauf_lg hs hinv ks _ _ _ hw'
        | next hw' => exact traverseLauf_lg hs hinv ks _ _ _ hw'
        | @leave _ σa σb ρa hw' =>
            obtain ⟨hw2, hb2⟩ := hinv σa σb ρa.tail hw'
            exact AusLG.ite_eq hb2 (.ok hw2) (.logik _)
        | zurueck hw' => exact .zurueck hw'
        | why hw' => exact .why hw'
        | logik e => exact .logik e
        | hardware e => exact .hardware e
        | frueh hE => exact .frueh hE
        | fruehH hE => exact .fruehH hE

theorem retryLauf_lg {l : Bool} {Γ : Ctx} {s₁ s₂ : World D → Env D Γ → Ausgang V true Γ}
    {bis : World D → Env D Γ → World D × Bool} {u₁ u₂ : World D → Env D Γ → Ausgang V l Γ}
    (hs : ∀ σ σ' ρ, WeltGleich σ σ' → AusLG Er (s₁ σ ρ) (s₂ σ' ρ)) (hbis : FunLG bis)
    (hu : ∀ σ σ' ρ, WeltGleich σ σ' → AusLG Er (u₁ σ ρ) (u₂ σ' ρ)) :
    ∀ (n : Nat) (σ σ' : World D) (ρ : Env D Γ), WeltGleich σ σ' →
      AusLG Er (retryLauf s₁ bis u₁ n σ ρ) (retryLauf s₂ bis u₂ n σ' ρ)
  | 0, σ, σ', ρ, h => by
      obtain ⟨hw, hb⟩ := hbis σ σ' ρ h
      simp only [retryLauf]
      exact AusLG.ite_eq hb (.ok hw) (hu _ _ ρ hw)
  | n + 1, σ, σ', ρ, h => by
      obtain ⟨hw, hb⟩ := hbis σ σ' ρ h
      simp only [retryLauf]
      rw [hb]
      by_cases hc : (bis σ' ρ).2 = true
      · rw [if_pos hc, if_pos hc]; exact .ok hw
      · rw [if_neg hc, if_neg hc]
        have hst := hs _ _ ρ hw
        generalize s₁ (bis σ ρ).1 ρ = o₁ at hst ⊢
        generalize s₂ (bis σ' ρ).1 ρ = o₂ at hst ⊢
        cases hst with
        | ok hw' => exact retryLauf_lg hs hbis hu n _ _ _ hw'
        | next hw' => exact retryLauf_lg hs hbis hu n _ _ _ hw'
        | leave hw' => exact .ok hw'
        | zurueck hw' => exact .zurueck hw'
        | why hw' => exact .why hw'
        | logik e => exact .logik e
        | hardware e => exact .hardware e
        | frueh hE => exact .frueh hE
        | fruehH hE => exact .fruehH hE

theorem foreverLauf_lg {l : Bool} {Γ : Ctx} (a : D.Annahme) {s₁ s₂ : World D → Env D Γ → Ausgang V true Γ}
    {inv : World D → Env D Γ → World D × Bool}
    (hs : ∀ σ σ' ρ, WeltGleich σ σ' → AusLG Er (s₁ σ ρ) (s₂ σ' ρ)) (hinv : FunLG inv) :
    ∀ (n : Nat) (σ σ' : World D) (ρ : Env D Γ), WeltGleich σ σ' →
      AusLG Er (foreverLauf (l := l) a s₁ inv n σ ρ) (foreverLauf (l := l) a s₂ inv n σ' ρ)
  | 0, _, _, _, _ => .hardware _
  | n + 1, σ, σ', ρ, h => by
      obtain ⟨hw, hb⟩ := hinv σ σ' ρ h
      simp only [foreverLauf]
      rw [hb]
      by_cases hc : (inv σ' ρ).2 = false
      · rw [if_pos hc, if_pos hc]; exact .logik _
      · rw [if_neg hc, if_neg hc]
        have hst := hs _ _ ρ hw
        generalize s₁ (inv σ ρ).1 ρ = o₁ at hst ⊢
        generalize s₂ (inv σ' ρ).1 ρ = o₂ at hst ⊢
        cases hst with
        | ok hw' => exact foreverLauf_lg a hs hinv n _ _ _ hw'
        | next hw' => exact foreverLauf_lg a hs hinv n _ _ _ hw'
        | leave hw' => exact .ok hw'
        | zurueck hw' => exact .zurueck hw'
        | why hw' => exact .why hw'
        | logik e => exact .logik e
        | hardware e => exact .hardware e
        | frueh hE => exact .frueh hE
        | fruehH hE => exact .fruehH hE

end Schleifen

/-! ## 3. The indirect call dispatch -/

section Indirekt

variable {V : Vertrag D} {Er : Fehlermarke D → Prop}
  {R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f}

theorem indSonst_lg (hR : HandlerLG Er R₁ R₂) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hr : 0 < (D.sigNr n).gruende) {s₁ s₂ : World D} (h : WeltGleich s₁ s₂)
    (ρ : Env D Γ) {ok₁ ok₂ : World D → Wert D τ → Ausgang V l Γ}
    {why₁ why₂ : World D → Fin (D.sigNr n).gruende → Ausgang V l Γ}
    (hok : ∀ σ σ' v, WeltGleich σ σ' → AusLG Er (ok₁ σ v) (ok₂ σ' v))
    (hwhy : ∀ σ σ' r, WeltGleich σ σ' → AusLG Er (why₁ σ r) (why₂ σ' r)) :
    AusLG Er (indSonst R₁ p args he hr s₁ ρ ok₁ why₁) (indSonst R₂ p args he hr s₂ ρ ok₂ why₂) := by
  simp only [indSonst]
  rw [h.wert' p ρ, h.werte args ρ]
  generalize eval s₂ p s₂ ρ = w
  obtain ⟨g, hg⟩ := w
  dsimp only
  have hc := hR g s₁ s₂ (umsig hg (evalArgs s₂ args s₂ ρ)) h
  generalize R₁ g s₁ (umsig hg (evalArgs s₂ args s₂ ρ)) = a₁ at hc ⊢
  generalize R₂ g s₂ (umsig hg (evalArgs s₂ args s₂ ρ)) = a₂ at hc ⊢
  cases hc with
  | ok hw => exact hok _ _ _ hw
  | why hw => exact hwhy _ _ _ hw
  | logik e => exact .logik e
  | hardware e => exact .hardware e
  | frueh hE => exact .frueh hE
  | fruehH hE => exact .fruehH hE

theorem indSonstE_lg (hR : HandlerLG Er R₁ R₂) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hr : 0 < (D.sigNr n).gruende) {s₁ s₂ : World D} (h : WeltGleich s₁ s₂)
    (ρ : Env D Γ) {ok₁ ok₂ : World D → Wert D τ → EndAusgang V l Γ}
    {why₁ why₂ : World D → Fin (D.sigNr n).gruende → EndAusgang V l Γ}
    (hok : ∀ σ σ' v, WeltGleich σ σ' → EndLG Er (ok₁ σ v) (ok₂ σ' v))
    (hwhy : ∀ σ σ' r, WeltGleich σ σ' → EndLG Er (why₁ σ r) (why₂ σ' r)) :
    EndLG Er (indSonstE R₁ p args he hr s₁ ρ ok₁ why₁) (indSonstE R₂ p args he hr s₂ ρ ok₂ why₂) := by
  simp only [indSonstE]
  rw [h.wert' p ρ, h.werte args ρ]
  generalize eval s₂ p s₂ ρ = w
  obtain ⟨g, hg⟩ := w
  dsimp only
  have hc := hR g s₁ s₂ (umsig hg (evalArgs s₂ args s₂ ρ)) h
  generalize R₁ g s₁ (umsig hg (evalArgs s₂ args s₂ ρ)) = a₁ at hc ⊢
  generalize R₂ g s₂ (umsig hg (evalArgs s₂ args s₂ ρ)) = a₂ at hc ⊢
  cases hc with
  | ok hw => exact hok _ _ _ hw
  | why hw => exact hwhy _ _ _ hw
  | logik e => exact .logik e
  | hardware e => exact .hardware e
  | frueh hE => exact .frueh hE
  | fruehH hE => exact .fruehH hE

end Indirekt

end Gabbro.Stage0.Senke.BildLauf
