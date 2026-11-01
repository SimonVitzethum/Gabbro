module

public import Grammatik.Nebenlaeufigkeit.Sperren.SperreBeweis
public import Grammatik.Nebenlaeufigkeit.Sperren.SperreMaschine.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}
section Freigabe
variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **How one step moves the held locks of the acting thread, with the
    releasing rules named**: the held set stays or grows (every rule but
    three), or the head is a release marker `frei L` (`freiGib`), or a
    `leave`/`next` leaves a `locks` body (`peelFreiLeave`, `peelFreiNext`)
    -- and then memory is untouched and exactly one entry of `L` leaves the
    held set. -/
theorem freigabe_schrittG (hO : GutO O) {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M') :
    (∀ L, L ∈ offen (M.faeden u).spur → L ∈ offen (M'.faeden u).spur) ∨
    (∃ (l : Bool) (Γ : Ctx) (Λ : List (Res D)) (L : D.Lock)
      (k : GRest D (vertragVon D (M.faeden u).kopf.f) l Γ Λ) (ρ : Env D Γ),
      (M.faeden u).kopf.rest = ⟨l, Γ, Res.held L :: Λ, ρ, .frei L k⟩ ∧
      M'.speicher = M.speicher ∧
      offen (M'.faeden u).spur = (offen (M.faeden u).spur).erase L) ∨
    (∃ (Γ : Ctx) (Λ Λ1 : List (Res D)) (L : D.Lock)
      (rest : Block D (vertragVon D (M.faeden u).kopf.f) true Γ Λ (Res.held L :: Λ1))
      (k : GRest D (vertragVon D (M.faeden u).kopf.f) true Γ Λ1) (ρ : Env D Γ) (h : true = true)
      (x : Bool),
      (M.faeden u).kopf.rest =
        ⟨true, Γ, Λ, ρ, .dann (.cons (if x then .leave h else .next h) rest) (.frei L k)⟩ ∧
      M'.speicher = M.speicher ∧
      offen (M'.faeden u).spur = (offen (M.faeden u).spur).erase L) := by
  have hgross : ∀ {a b : List D.Lock}, a = b → ∀ L, L ∈ b → L ∈ a := fun e L h => e ▸ h
  cases hs with
  | g1 hs =>
    cases hs with
    | blatt l Γ Λ Λ' s rest ρ hleaf _ hΛ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        exact Or.inl (hgross (blatt_offen hO s hleaf _ ρ hΛ σ' ρ' hstep))
    | dannBlatt l Γ Λ Λ' Λ'' s rest k ρ hleaf _ hΛ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        exact Or.inl (hgross (blatt_offen hO s hleaf _ ρ hΛ σ' ρ' hstep))
    | endeBindAxiom l Γ Λ τ a args he hw hg hd hgd rest ρ _ σ₁ hs₁ σ₂ v hax =>
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        rw [axiom_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        first
          | exact trivial
          | rfl
          | exact lese_offen _ _ _
  | g2 hs =>
    cases hs with
    | dannLocks l Γ Λ Λ'' L _ _ _ _ _ _ _ _ hfrei =>
        simp only [rufUpdateG_self]
        exact Or.inl fun K hK => List.mem_cons_of_mem _ hK
    | freiGib l Γ Λ L k ρ hhead =>
        refine Or.inr (Or.inl ⟨l, Γ, Λ, L, k, ρ, hhead, rfl, ?_⟩)
        simp only [rufUpdateG_self]
        rfl
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        first
          | exact trivial
          | rfl
          | exact lese_offen _ _ _
  | g3 hs =>
    cases hs with
    | dannLeaveTrav l Γ Λ t inv body is k rest i ρ hl _ σ' ρ' _ hstep _ _ σ₁ hs₁ =>
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        rw [hs₁, lese_offen, leave_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | dannNextTrav l Γ Λ t inv body is k rest i ρ hl _ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | dannLeaveWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | dannNextWieder l Γ Λ n bis body ueber k rest ρ hl _ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | dannLeaveEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        rw [leave_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        first
          | exact trivial
          | rfl
          | exact lese_offen _ _ _
  | g4 hs =>
    cases hs with
    | peelFreiLeave l Γ Λ L rest k ρ hl hhead =>
        refine Or.inr (Or.inr ⟨Γ, Λ, _, L, rest, k, ρ, hl, true, hhead, rfl, ?_⟩)
        simp only [rufUpdateG_self]
        rfl
    | peelFreiNext l Γ Λ L rest k ρ hl hhead =>
        refine Or.inr (Or.inr ⟨Γ, Λ, _, L, rest, k, ρ, hl, false, hhead, rfl, ?_⟩)
        simp only [rufUpdateG_self]
        rfl
    | dannNextEwig l Γ Λ a n inv body k rest ρ hl _ σ' ρ' _ hstep =>
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        rw [next_welt' _ _ _ _ _ _ _ _ hstep]
        rfl
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        first
          | exact trivial
          | rfl
          | exact lese_offen _ _ _
  | g5 hs =>
    cases hs with
    | dannExchange l Γ Λ Λ' g neuE hw hL rest k ρ _ σ₁ hs₁ σ₂ hs₂ =>
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        rw [hs₂, hs₁]
        exact lese_offen _ _ _
    | dannBindAxiom l Γ Λ Λ' τ a args he hw hg hd hgd rest k ρ _ σ₁ hs₁ σ₂ v hax =>
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        rw [axiom_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
    | dannBindAxiomElseOk l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ _ σ₁ hs₁ σ₂ v hax =>
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
    | dannBindAxiomElseGrund l Γ Λ Λ' τ a args he hr hw hg hd hgd err rest k ρ _ σ₁ hs₁ σ₂ r hax =>
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
    | _ =>
        subst_vars
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        first
          | exact trivial
          | rfl
          | exact lese_offen _ _ _
  | g6 hs =>
    cases hs with
    | endeBindAxiomElseOk l Γ Λ τ a args he hr hw hg hd hgd err rest ρ _ σ₁ hs₁ σ₂ v hax =>
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _
    | endeBindAxiomElseGrund l Γ Λ τ a args he hr hw hg hd hgd err rest ρ _ σ₁ hs₁ σ₂ r hax =>
        simp only [rufUpdateG_self]
        refine Or.inl (hgross ?_)
        rw [axiomSonst_offen' hO _ _ _ _ _ hax, hs₁]
        exact lese_offen _ _ _

end Freigabe

/-! ## 4. The invariant of every free lock holds in the machine -/

/-- **The machine lock invariant**: every lock that no thread holds has its
    invariant at the live memory. -/
def SperrInvG (S : SperrInv D) (M : RufMaschineG D) : Prop :=
  ∀ L : D.Lock, (∀ t : Faden, L ∉ offen (M.faeden t).spur) → S.inv L M.speicher = true

theorem sperrInvG_start (P : Programm D) (S : SperrInv D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (hsp : ∀ L, S.inv L sp = true) :
    SperrInvG S (RufStartG P sp init) :=
  fun L _ => hsp L

section SperrInvG

variable {P : Programm D} {O : Orakel D} {passes : Nat} {S : SperrInv D}

/-- **A step keeps the machine lock invariant**, given that every lock the
    step releases has its invariant at the new memory (the replay's side,
    `ZielOrtSperre.lean`). A lock free before the step keeps its protected
    carriers (every write needs all guards of its carrier held), so its
    invariant stays; a lock that becomes free was held by the acting thread
    alone and is released by the step. -/
theorem sperrInvG_schritt (hO : GutO O) (hS : SperrInvOk S) {M M' : RufMaschineG D} {u : Faden}
    (hs : RufSchrittG P O passes M u M') (hSG : SperrInvG S M)
    (hfrei : ∀ L, L ∈ offen (M.faeden u).spur → L ∉ offen (M'.faeden u).spur →
      S.inv L M'.speicher = true) :
    SperrInvG S M' := by
  intro L hL
  by_cases hM : ∀ t, L ∉ offen (M.faeden t).spur
  · -- free before: its protected carriers are untouched
    rw [← hSG L hM]
    refine hS.2 L _ _ fun c hc => ?_
    exact schritt_traeger hO hs c (Or.inl ⟨L, hS.1 L c hc, hM u⟩)
  · -- held before by some thread: it can only be the acting thread
    have ⟨t, ht⟩ : ∃ t, L ∈ offen (M.faeden t).spur := by
      refine Classical.byContradiction fun hn => hM fun t ht => hn ⟨t, ht⟩
    by_cases htu : t = u
    · subst htu
      exact hfrei L ht (hL t)
    · exact absurd (by rw [rufSchrittG_fremd hs t htu]; exact ht) (hL t)

end SperrInvG

#print axioms Gabbro.Grammatik.stabilS_rely
#print axioms Gabbro.Grammatik.rufG_rahmenS
#print axioms Gabbro.Grammatik.freigabe_schrittG
#print axioms Gabbro.Grammatik.sperrInvG_schritt

end Gabbro.Grammatik
