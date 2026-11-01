module

public import Grammatik.Kern.Syntax.Satz.T3

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

section Rumpf
variable (O : Orakel D)

/-- The oracle's effect of a foreign body is a good step (`GutO`), in whatever world it is asked. -/
theorem wirkt_gut (hO : GutO O) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a))
    {Λ : List (Res D)}
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (hh : HeldIn Λ σ.haelt) :
    Gut (D.aschreibt a) (D.agschreibt a) σ (O.wirkt a σ ρ).1 := by
  have hgt : ∀ t, D.aschreibt a t = true → ∀ L, Sum.inl L ∈ D.braucht t → L ∈ σ.haelt :=
    fun t hwr L hL => hh L (hd t hwr _ hL)
  have hgg : ∀ g, D.agschreibt a g = true → ∀ L, Sum.inl L ∈ D.gbraucht g → L ∈ σ.haelt :=
    fun g hwr L hL => hh L (hgd g hwr _ hL)
  obtain ⟨hr, hhaelt, hcond⟩ := hO a σ ρ
  obtain ⟨tabs, globs, Λe, _, _, hdt, hdg, _, hhi, hspur⟩ := hcond hgt hgg
  refine ⟨hr, hhaelt, fun e he => ?_, fun k => ?_⟩
  · have he' : e ∈ (O.wirkt a σ ρ).1.spur := he
    rw [hspur, List.mem_append] at he'
    rcases he' with hnew | hold
    · exact .inr (axiomSpur_gut tabs globs a Λe σ.haelt hdt hdg hhi e hnew)
    · exact .inl hold
  · have hc := konsistent_merke σ.haelt (axiomSpur tabs globs a Λe σ.haelt) σ.spur
      (fun e he => axiomSpur_zugriffMit tabs globs a Λe σ.haelt e he) rfl k
    exact hspur ▸ hc

theorem axiomAntwort_gut (hO : GutO O) (a : D.Ax) (σ : World D) (ρ : Env D (D.aparams a))
    {Λ : List (Res D)}
    (hd : ∀ t, D.aschreibt a t = true → darf D t Λ)
    (hgd : ∀ g, D.agschreibt a g = true → gdarf D g Λ)
    (hh : HeldIn Λ σ.haelt) :
    Gut (D.aschreibt a) (D.agschreibt a) σ (axiomAntwort O a σ ρ).1 :=
  (gut_fragt σ (.inl a)).trans (wirkt_gut O hO a (σ.fragt (.inl a)) ρ hd hgd hh)

variable (passes : Nat)
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable (hR : GutR R) (hO : GutO O)
include hR hO
set_option linter.unusedSectionVars false

end Rumpf
end Gabbro.Grammatik
