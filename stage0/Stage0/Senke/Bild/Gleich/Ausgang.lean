/-
  File:      stage0/Stage0/Senke/Bild/Gleich/Ausgang.lean
  Subject:   Package P1 of the closed calls of the image theorem, part 1: outcomes up to read events, and the one
             premise on the oracle. `AusLG`/`EndLG`/`RufLG` relate two outcomes of the same shape whose worlds are
             `≈` (`WeltGleich`) and whose other data are equal -- or the FIRST outcome is an error whose mark lies
             in `Er` (the first side may fail early, as in `HandlerKongruenz`). `HandlerLG Er R₁ R₂` says that two
             handlers answer `≈`-related worlds with related outcomes.

             **The oracle premise** (`Leseblind`). The oracle `O` answers foreign calls, register reads and
             visibility questions from the WHOLE world, trace included. Two runs whose worlds differ by read events
             stay related only if the oracle does not look at read events: its answers agree, and its effect
             worlds are `≈`, on `≈` worlds. Without it the statement is false (an oracle that counts reads tells
             `rufAt`'s run from machine G's). It holds for every oracle that ignores the trace
             (`leseblind_still`, `Zeuge.lean`), and for the witness oracle of the call fixture.
-/
module
public import Stage0.Senke.Bild.Gleich.Lesegleich
public import Grammatik.Logik.Vertraege.HandlerKongruenz.Teil1
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration}

/-! ## 1. The oracle -/

/-- **A read-blind oracle**: on `≈` worlds its answers agree and its effect worlds are `≈`. -/
structure Leseblind (O : Orakel D) : Prop where
  wirkt : ∀ (a : D.Ax) (σ σ' : World D) (ρ : Env D (D.aparams a)), WeltGleich σ σ' →
    WeltGleich (O.wirkt a σ ρ).1 (O.wirkt a σ' ρ).1 ∧ (O.wirkt a σ ρ).2 = (O.wirkt a σ' ρ).2
  regLies : ∀ (r : D.Reg) (σ σ' : World D), WeltGleich σ σ' → O.regLies r σ = O.regLies r σ'
  sichtbar : ∀ (g : D.Glob) (σ σ' : World D), WeltGleich σ σ' → O.sichtbar g σ = O.sichtbar g σ'

/-- Two answers with `≈` worlds and the same value. -/
inductive PaarLG {α : Type} : World D × α → World D × α → Prop
  | mk {σ σ' : World D} {x : α} : WeltGleich σ σ' → PaarLG (σ, x) (σ', x)

/-- Two pairs with `≈` first and equal second components. -/
theorem PaarLG.of {α : Type} {p q : World D × α} (h1 : WeltGleich p.1 q.1) (h2 : p.2 = q.2) : PaarLG p q := by
  obtain ⟨σ, x⟩ := p
  obtain ⟨σ', y⟩ := q
  change WeltGleich σ σ' at h1
  change x = y at h2
  subst h2
  exact PaarLG.mk h1

/-- A foreign call of a read-blind oracle on `≈` worlds. -/
theorem paarLG_axiomAntwort {O : Orakel D} (hO : Leseblind O) (a : D.Ax) {σ σ' : World D}
    (h : WeltGleich σ σ') (x : Env D (D.aparams a)) :
    PaarLG (axiomAntwort O a σ x) (axiomAntwort O a σ' x) := by
  have hw := hO.wirkt a (σ.fragt (.inl a)) (σ'.fragt (.inl a)) x (h.fragt (.inl a))
  unfold axiomAntwort
  generalize O.wirkt a (σ.fragt (.inl a)) x = A at hw ⊢
  generalize O.wirkt a (σ'.fragt (.inl a)) x = B at hw ⊢
  obtain ⟨σA, rA⟩ := A
  obtain ⟨σB, rB⟩ := B
  obtain ⟨h1, h2⟩ := hw
  change WeltGleich σA σB at h1
  change rA = rB at h2
  subst h2
  exact PaarLG.mk h1

/-- A fallible foreign call of a read-blind oracle on `≈` worlds. -/
theorem paarLG_axiomAntwortSonst {O : Orakel D} (hO : Leseblind O) (a : D.Ax) {σ σ' : World D}
    (h : WeltGleich σ σ') (x : Env D (D.aparams a)) :
    PaarLG (axiomAntwortSonst O a σ x) (axiomAntwortSonst O a σ' x) := by
  have hw := hO.wirkt a (σ.fragt (.inl a)) (σ'.fragt (.inl a)) x (h.fragt (.inl a))
  unfold axiomAntwortSonst
  generalize O.wirkt a (σ.fragt (.inl a)) x = A at hw ⊢
  generalize O.wirkt a (σ'.fragt (.inl a)) x = B at hw ⊢
  obtain ⟨σA, rA⟩ := A
  obtain ⟨σB, rB⟩ := B
  obtain ⟨h1, h2⟩ := hw
  change WeltGleich σA σB at h1
  change rA = rB at h2
  subst h2
  exact PaarLG.mk h1

/-! ## 2. Outcomes up to read events -/

/-- **Two call outcomes up to read events**, or the first fails early with a mark in `Er`. -/
inductive RufLG (Er : Fehlermarke D → Prop) {f : D.Fn} : RufAusgang f → RufAusgang f → Prop
  | ok {σ σ' : World D} {v : ErgVal D (D.erg f)} : WeltGleich σ σ' → RufLG Er (.ok σ v) (.ok σ' v)
  | why {σ σ' : World D} {r : Fin (D.gruende f)} : WeltGleich σ σ' → RufLG Er (.why σ r) (.why σ' r)
  | logik (e : Logik D) : RufLG Er (.logik e) (.logik e)
  | hardware (e : Hardware D) : RufLG Er (.hardware e) (.hardware e)
  | frueh {e : Logik D} {a : RufAusgang f} : Er (.logik e) → RufLG Er (.logik e) a
  | fruehH {e : Hardware D} {a : RufAusgang f} : Er (.hardware e) → RufLG Er (.hardware e) a

/-- **Two statement outcomes up to read events** (same environments), or the first fails early in `Er`. -/
inductive AusLG (Er : Fehlermarke D → Prop) {V : Vertrag D} {l : Bool} {Γ : Ctx} :
    Ausgang V l Γ → Ausgang V l Γ → Prop
  | ok {σ σ' : World D} {ρ : Env D Γ} : WeltGleich σ σ' → AusLG Er (.ok σ ρ) (.ok σ' ρ)
  | zurueck {σ σ' : World D} {v : ErgVal D V.erg} : WeltGleich σ σ' → AusLG Er (.zurueck σ v) (.zurueck σ' v)
  | why {σ σ' : World D} {r : Fin V.gruende} : WeltGleich σ σ' → AusLG Er (.why σ r) (.why σ' r)
  | leave {h : l = true} {σ σ' : World D} {ρ : Env D Γ} : WeltGleich σ σ' →
      AusLG Er (.leave h σ ρ) (.leave h σ' ρ)
  | next {h : l = true} {σ σ' : World D} {ρ : Env D Γ} : WeltGleich σ σ' →
      AusLG Er (.next h σ ρ) (.next h σ' ρ)
  | logik (e : Logik D) : AusLG Er (.logik e) (.logik e)
  | hardware (e : Hardware D) : AusLG Er (.hardware e) (.hardware e)
  | frueh {e : Logik D} {o : Ausgang V l Γ} : Er (.logik e) → AusLG Er (.logik e) o
  | fruehH {e : Hardware D} {o : Ausgang V l Γ} : Er (.hardware e) → AusLG Er (.hardware e) o

/-- **Two terminal-block outcomes up to read events**, or the first fails early in `Er`. -/
inductive EndLG (Er : Fehlermarke D → Prop) {V : Vertrag D} {l : Bool} {Γ : Ctx} :
    EndAusgang V l Γ → EndAusgang V l Γ → Prop
  | zurueck {σ σ' : World D} {v : ErgVal D V.erg} : WeltGleich σ σ' → EndLG Er (.zurueck σ v) (.zurueck σ' v)
  | why {σ σ' : World D} {r : Fin V.gruende} : WeltGleich σ σ' → EndLG Er (.why σ r) (.why σ' r)
  | leave {h : l = true} {σ σ' : World D} {ρ : Env D Γ} : WeltGleich σ σ' →
      EndLG Er (.leave h σ ρ) (.leave h σ' ρ)
  | next {h : l = true} {σ σ' : World D} {ρ : Env D Γ} : WeltGleich σ σ' →
      EndLG Er (.next h σ ρ) (.next h σ' ρ)
  | logik (e : Logik D) : EndLG Er (.logik e) (.logik e)
  | hardware (e : Hardware D) : EndLG Er (.hardware e) (.hardware e)
  | frueh {e : Logik D} {o : EndAusgang V l Γ} : Er (.logik e) → EndLG Er (.logik e) o
  | fruehH {e : Hardware D} {o : EndAusgang V l Γ} : Er (.hardware e) → EndLG Er (.hardware e) o

/-- **THE HANDLER PREMISE**: on `≈` worlds the two handlers give related call outcomes. -/
def HandlerLG (Er : Fehlermarke D → Prop)
    (R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f) : Prop :=
  ∀ (g : D.Fn) (σ σ' : World D) (ρ : Env D (D.params g)), WeltGleich σ σ' → RufLG Er (R₁ g σ ρ) (R₂ g σ' ρ)

/-- Reading before the second handler keeps the relation (the second side sees more read events). -/
theorem HandlerLG.lese_vorn {Er : Fehlermarke D → Prop}
    {R₁ R₂ : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f} (hR : HandlerLG Er R₁ R₂)
    (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    HandlerLG Er R₁ (fun g σ ρ => R₂ g (σ.lese Λ os) ρ) :=
  fun g σ σ' ρ h => hR g σ (σ'.lese Λ os) ρ (h.trans (weltGleich_lese σ' Λ os))

/-! ## 3. The outcome wrappers keep the relation -/

section Huellen

variable {Er : Fehlermarke D → Prop} {V : Vertrag D} {l : Bool} {Γ : Ctx}

theorem AusLG.schrumpf {τ : Ty} {o₁ o₂ : Ausgang V l (τ :: Γ)} (h : AusLG Er o₁ o₂) :
    AusLG Er o₁.schrumpf o₂.schrumpf := by
  cases h with
  | ok hw => exact .ok hw
  | zurueck hw => exact .zurueck hw
  | why hw => exact .why hw
  | leave hw => exact .leave hw
  | next hw => exact .next hw
  | logik e => exact .logik e
  | hardware e => exact .hardware e
  | frueh hE => exact .frueh hE
  | fruehH hE => exact .fruehH hE

theorem AusLG.schrumpfArm {c : Option Ty} {o₁ o₂ : Ausgang V l (ArmCtx Γ c)} (h : AusLG Er o₁ o₂) :
    AusLG Er (Ausgang.schrumpfArm c o₁) (Ausgang.schrumpfArm c o₂) := by
  cases c with
  | none => exact h
  | some p => exact h.schrumpf

theorem AusLG.weiterOpt (e : Option Ty) {o₁ o₂ : Ausgang V l (ErgCtx Γ e)} (h : AusLG Er o₁ o₂) :
    AusLG Er (Ausgang.weiterOpt e o₁) (Ausgang.weiterOpt e o₂) := by
  cases e with
  | none => exact h
  | some τ => exact h.schrumpf

theorem AusLG.mapWelt {F : World D → World D} (hF : ∀ σ σ', WeltGleich σ σ' → WeltGleich (F σ) (F σ'))
    {o₁ o₂ : Ausgang V l Γ} (h : AusLG Er o₁ o₂) : AusLG Er (o₁.mapWelt F) (o₂.mapWelt F) := by
  cases h with
  | ok hw => exact .ok (hF _ _ hw)
  | zurueck hw => exact .zurueck (hF _ _ hw)
  | why hw => exact .why (hF _ _ hw)
  | leave hw => exact .leave (hF _ _ hw)
  | next hw => exact .next (hF _ _ hw)
  | logik e => exact .logik e
  | hardware e => exact .hardware e
  | frueh hE => exact .frueh hE
  | fruehH hE => exact .fruehH hE

theorem AusLG.ite {c : Prop} [Decidable c] {a₁ a₂ b₁ b₂ : Ausgang V l Γ}
    (ha : AusLG Er a₁ a₂) (hb : AusLG Er b₁ b₂) :
    AusLG Er (if c then a₁ else b₁) (if c then a₂ else b₂) := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact ha
  · rw [if_neg h, if_neg h]; exact hb

/-- Two Boolean tests with equal values. -/
theorem AusLG.ite_eq {c₁ c₂ : Bool} (hc : c₁ = c₂) {a₁ a₂ b₁ b₂ : Ausgang V l Γ}
    (ha : AusLG Er a₁ a₂) (hb : AusLG Er b₁ b₂) :
    AusLG Er (if c₁ = true then a₁ else b₁) (if c₂ = true then a₂ else b₂) := by
  subst hc
  exact AusLG.ite ha hb

theorem AusLG.dite {c : Prop} [Decidable c] {a₁ a₂ : c → Ausgang V l Γ} {b₁ b₂ : ¬c → Ausgang V l Γ}
    (ha : ∀ h, AusLG Er (a₁ h) (a₂ h)) (hb : ∀ h, AusLG Er (b₁ h) (b₂ h)) :
    AusLG Er (dite c a₁ b₁) (dite c a₂ b₂) := by
  by_cases h : c
  · rw [dif_pos h, dif_pos h]; exact ha h
  · rw [dif_neg h, dif_neg h]; exact hb h

theorem EndLG.schrumpf {τ : Ty} {o₁ o₂ : EndAusgang V l (τ :: Γ)} (h : EndLG Er o₁ o₂) :
    EndLG Er o₁.schrumpf o₂.schrumpf := by
  cases h with
  | zurueck hw => exact .zurueck hw
  | why hw => exact .why hw
  | leave hw => exact .leave hw
  | next hw => exact .next hw
  | logik e => exact .logik e
  | hardware e => exact .hardware e
  | frueh hE => exact .frueh hE
  | fruehH hE => exact .fruehH hE

theorem EndLG.weiterOpt (e : Option Ty) {o₁ o₂ : EndAusgang V l (ErgCtx Γ e)} (h : EndLG Er o₁ o₂) :
    EndLG Er (EndAusgang.weiterOpt e o₁) (EndAusgang.weiterOpt e o₂) := by
  cases e with
  | none => exact h
  | some τ => exact h.schrumpf

theorem EndLG.zuAusgang {o₁ o₂ : EndAusgang V l Γ} (h : EndLG Er o₁ o₂) :
    AusLG Er o₁.zuAusgang o₂.zuAusgang := by
  cases h with
  | zurueck hw => exact .zurueck hw
  | why hw => exact .why hw
  | leave hw => exact .leave hw
  | next hw => exact .next hw
  | logik e => exact .logik e
  | hardware e => exact .hardware e
  | frueh hE => exact .frueh hE
  | fruehH hE => exact .fruehH hE

theorem EndLG.ite {c : Prop} [Decidable c] {a₁ a₂ b₁ b₂ : EndAusgang V l Γ}
    (ha : EndLG Er a₁ a₂) (hb : EndLG Er b₁ b₂) :
    EndLG Er (if c then a₁ else b₁) (if c then a₂ else b₂) := by
  by_cases h : c
  · rw [if_pos h, if_pos h]; exact ha
  · rw [if_neg h, if_neg h]; exact hb

theorem EndLG.ite_eq {c₁ c₂ : Bool} (hc : c₁ = c₂) {a₁ a₂ b₁ b₂ : EndAusgang V l Γ}
    (ha : EndLG Er a₁ a₂) (hb : EndLG Er b₁ b₂) :
    EndLG Er (if c₁ = true then a₁ else b₁) (if c₂ = true then a₂ else b₂) := by
  subst hc
  exact EndLG.ite ha hb

theorem EndLG.dite {c : Prop} [Decidable c] {a₁ a₂ : c → EndAusgang V l Γ} {b₁ b₂ : ¬c → EndAusgang V l Γ}
    (ha : ∀ h, EndLG Er (a₁ h) (a₂ h)) (hb : ∀ h, EndLG Er (b₁ h) (b₂ h)) :
    EndLG Er (dite c a₁ b₁) (dite c a₂ b₂) := by
  by_cases h : c
  · rw [dif_pos h, dif_pos h]; exact ha h
  · rw [dif_neg h, dif_neg h]; exact hb h

end Huellen

end Gabbro.Stage0.Senke.BildLauf
