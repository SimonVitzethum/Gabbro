module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiVoll
public import Grammatik.Zielsatz.ZielOrt.Rahmen.ZielOrtMehrfaden
public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiOrte.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Ev
variable {C W : D.Tab ⊕ D.Glob → Bool}

theorem schreibBytes_ev (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255)
    (Λ : List (Res D)) (hw : W (.inl t) = true) :
    ∀ (bs : List Byte) (σ : World D) (k : Int),
      ∃ X, (σ.schreibBytes t f hf Λ k bs).spur = X ++ σ.spur ∧ EvOk C W X := by
  intro bs
  induction bs with
  | nil => intro σ k; exact ⟨[], rfl, evOk_nil⟩
  | cons b bs ih =>
      intro σ k
      simp only [World.schreibBytes]
      obtain ⟨X, hX, hok⟩ := ih (σ.schreibSlot t Λ k f
        (cast (congrArg (Wert D) hf).symm (b : Wert D (.int 0 255)))) (k + 1)
      refine ⟨X ++ [Ereignis.zugriff t true Λ σ.haelt], ?_, evOk_append hok (evOk_schreibT hw)⟩
      rw [hX, List.append_assoc]
      rfl

theorem axiomSpur_ev {tabs : List D.Tab} {globs : List D.Glob} {a : D.Ax} {Λ : List (Res D)}
    {h : List D.Lock} (hw : ∀ t, D.aschreibt a t = true → W (.inl t) = true)
    (hg : ∀ g, D.agschreibt a g = true → W (.inr g) = true) :
    EvOk C W (axiomSpur tabs globs a Λ h) := by
  intro e he c w hz
  rcases axiomSpur_mem he with ⟨t, _, ht, rfl⟩ | ⟨g, _, hgg, rfl⟩
  · simp only [zugriffVon, Option.some.injEq, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl⟩ := hz
    exact ⟨fun h => (by cases h), fun _ => hw t ht⟩
  · simp only [zugriffVon, Option.some.injEq, Prod.mk.injEq] at hz
    obtain ⟨rfl, rfl⟩ := hz
    exact ⟨fun h => (by cases h), fun _ => hg g hgg⟩

/-- The trace of an axiom answer under held guards: the declared writes. -/
theorem axiom_ev (O : Orakel D) (hO : GutO O) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a))
    {Λ : List (Res D)} (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ) (hh : HeldIn Λ σ.haelt)
    (hw : ∀ t, D.aschreibt a t = true → W (.inl t) = true)
    (hg : ∀ g, D.agschreibt a g = true → W (.inr g) = true) :
    ∃ X, (O.wirkt a σ ρ).1.spur = X ++ σ.spur ∧ EvOk C W X := by
  have hgt : ∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t → L ∈ σ.haelt :=
    fun t hwr L hL => hh L (hd t hwr _ hL)
  have hgg : ∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g → L ∈ σ.haelt :=
    fun g hwr L hL => hh L (hgd g hwr _ hL)
  obtain ⟨_, _, hcond⟩ := hO a σ ρ
  obtain ⟨tabs, globs, Λe, _, _, _, _, _, _, hspur⟩ := hcond hgt hgg
  exact ⟨_, hspur, axiomSpur_ev hw hg⟩

end Ev

end Gabbro.Grammatik
