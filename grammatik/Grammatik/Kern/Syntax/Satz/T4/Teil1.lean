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

/-- Joint frame for the two exits of an indirect else-call («C07»): the pointer is
    evaluated once in the recorded world `s0`, the actual conforming function runs
    under its transported caller duty, and both continuations see the transported
    value (`runOk`) or reason (`runWhy`). The three `*_gutB` cases instantiate it
    with their runners; the branch inventories stay shared, never rolled back. -/
theorem indSonst_gutB (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : GutR R) (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
    (σ s0 : World D) (ρ : Env D Γ) (hh : HeldB bo Λ σ.haelt)
    (hl : Gut V.schreibt V.gschreibt σ s0)
    (ok : World D → Wert D τ → Ausgang V l Γ)
    (why : World D → Fin (D.sigNr n).gruende → Ausgang V l Γ)
    (runOk : ∀ σ1 (v : Wert D τ) (hh1 : HeldB bo (nachSig D (D.sigNr n) Λ) σ1.haelt),
      GutAusgang V.schreibt V.gschreibt σ1 (ok σ1 v))
    (runWhy : ∀ σ1 (r : Fin (D.sigNr n).gruende) (hh1 : HeldB bo (nachSig D (D.sigNr n) Λ) σ1.haelt),
      GutAusgang V.schreibt V.gschreibt σ1 (why σ1 r))
    (σ' : World D) (h : (indSonst R p args he hr s0 ρ ok why).welt = some σ') :
    Gut V.schreibt V.gschreibt σ σ' := by
  simp only [indSonst] at h
  generalize hpv : eval s0 p s0 ρ = pv at h
  obtain ⟨f, hf⟩ := pv
  simp only at h
  split at h
  · rename_i σ1 v hR1
    replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
    have g1 := hl.trans (Gut.weiter hp.hw hp.hg
      (hR f s0 _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
    exact g1.trans (runOk σ1 (ergWert (ergSig hf he) v)
      (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh) σ' h)
  · rename_i σ1 r hR1
    replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
    have g1 := hl.trans (Gut.weiter hp.hw hp.hg
      (hR f s0 _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
    exact g1.trans (runWhy σ1 (grundSig hf r)
      (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh) σ' h)
  · simp only [Ausgang.welt, reduceCtorEq] at h
  · simp only [Ausgang.welt, reduceCtorEq] at h

/-- Joint frame for the two exits of an indirect else-call at the end of a body («C07»):
    the `GutEnd` variant of `indSonst_gutB`, for the `end_gutB` case. -/
theorem indSonstE_gutB (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (hR : GutR R) (bo : Option Int) (hbV : BodenUnter bo V.boden)
    {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {n : Nat} {τ : Ty}
    (p : Expr D Γ Λ (.fnptr n)) (args : Args D Γ Λ (D.sigNr n).params)
    (he : (D.sigNr n).erg = some τ) (hp : RufPasst D V (D.sigNr n) Λ) (hr : 0 < (D.sigNr n).gruende)
    (σ s0 : World D) (ρ : Env D Γ) (hh : HeldB bo Λ σ.haelt)
    (hl : Gut V.schreibt V.gschreibt σ s0)
    (ok : World D → Wert D τ → EndAusgang V l Γ)
    (why : World D → Fin (D.sigNr n).gruende → EndAusgang V l Γ)
    (runOk : ∀ σ1 (v : Wert D τ) (hh1 : HeldB bo (nachSig D (D.sigNr n) Λ) σ1.haelt),
      GutEnd V.schreibt V.gschreibt σ1 (ok σ1 v))
    (runWhy : ∀ σ1 (r : Fin (D.sigNr n).gruende) (hh1 : HeldB bo (nachSig D (D.sigNr n) Λ) σ1.haelt),
      GutEnd V.schreibt V.gschreibt σ1 (why σ1 r))
    (σ' : World D) (h : (indSonstE R p args he hr s0 ρ ok why).welt = some σ') :
    Gut V.schreibt V.gschreibt σ σ' := by
  simp only [indSonstE] at h
  generalize hpv : eval s0 p s0 ρ = pv at h
  obtain ⟨f, hf⟩ := pv
  simp only at h
  split at h
  · rename_i σ1 v hR1
    replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
    have g1 := hl.trans (Gut.weiter hp.hw hp.hg
      (hR f s0 _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
    exact g1.trans (runOk σ1 (ergWert (ergSig hf he) v)
      (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh) σ' h)
  · rename_i σ1 r hR1
    replace hp := RufPasst.vonPasst (D.passt_sig hf) hp
    have g1 := hl.trans (Gut.weiter hp.hw hp.hg
      (hR f s0 _ (heldB_ruf hp hbV (hl.heldB hh)) σ1 (by rw [hR1]; rfl)))
    exact g1.trans (runWhy σ1 (grundSig hf r)
      (heldB_weiter (fun L => held_nachSig_iff _ _ L) g1 hh) σ' h)
  · simp only [EndAusgang.welt, reduceCtorEq] at h
  · simp only [EndAusgang.welt, reduceCtorEq] at h

end Gabbro.Grammatik
