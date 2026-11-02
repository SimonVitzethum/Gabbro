/-
  File:      Grammatik/Speichermodell/Atomar/AtomarGleich.lean
  Subject:   **Two atomic environments that answer alike on what a body reads run it alike**
             (`Stmt/Block/Endblock/Arms/GrundArms.execHA_gleich`), and the consequence for a
             library proved against a smaller rely: only bodies that read a carrier of the grown
             rely need a new proof (`koerperGutSA_wachs`).

  The proofs follow `execHA_frei` (AtomarSem.lean) read for read: where that one rewrites a read
  outside `T` into a read without havoc, this one rewrites it into the other environment's read.
-/
module
public import Grammatik.Speichermodell.Atomar.Invariants.AtomarGleichBasis
public import Grammatik.Speichermodell.Atomar.Invariants.AtomarRec
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}
/-! ## A grown rely -/

section Wachs

/-- The environment restricted to the carriers of `T₁`: elsewhere it answers the world as it is. -/
noncomputable def einschraenken (T₁ : D.Tab ⊕ D.Glob → Prop) (A : AUmwelt D) : AUmwelt D :=
  fun X σ => mischT T₁ X σ (A X σ).speicher

theorem havocA_einschraenken (T₁ : D.Tab ⊕ D.Glob → Prop) (A : AUmwelt D) :
    HavocA T₁ (einschraenken T₁ A) :=
  fun X σ => ⟨mischT_spur T₁ X σ _, fun _ hc => mischT_aussen σ _ hc⟩

private theorem tg_symm {s s' : Speicher D} {c : D.Tab ⊕ D.Glob} (h : TraegerGleich s s' c) :
    TraegerGleich s' s c := by
  cases c <;> exact h.symm

private theorem tg_trans {s s' s'' : Speicher D} {c : D.Tab ⊕ D.Glob} (h1 : TraegerGleich s s' c)
    (h2 : TraegerGleich s' s'' c) : TraegerGleich s s'' c := by
  cases c <;> exact h1.trans h2

/-- On a read list with no carrier of `T₂` outside `T₁`, an environment of the class `T₂` answers as
    its restriction to `T₁`. -/
theorem lese_einschraenken {T₁ T₂ : D.Tab ⊕ D.Glob → Prop} {A : AUmwelt D} (hA : HavocA T₂ A) :
    ∀ X : List (D.Tab ⊕ D.Glob), (∀ c ∈ X, ¬ (T₂ c ∧ ¬ T₁ c)) → ∀ (σ : World D) (Λ : List (Res D)),
      leseA A σ Λ X = leseA (einschraenken T₁ A) σ Λ X := by
  intro X hX σ Λ
  unfold leseA einschraenken
  refine world_ext (fun c => ?_) ((hA X _).1.trans (mischT_spur T₁ X _ _).symm)
  by_cases h : c ∈ X ∧ T₁ c
  · exact tg_symm (mischT_innen _ _ h)
  · have h2 : ¬ (c ∈ X ∧ T₂ c) := fun ⟨hm, ht⟩ => h ⟨hm, Classical.byContradiction fun hn => hX c hm ⟨ht, hn⟩⟩
    exact tg_trans ((hA X _).2 c h2) (tg_symm (mischT_aussen _ _ h))

variable {P : Programm D} {passes : Nat} {Q : AxEns D} {S : SperrInv D} {T₁ T₂ : D.Tab ⊕ D.Glob → Prop}
  {f : D.Fn}

/-- **A grown rely asks a new proof only of a body that reads a carrier of the growth.** A body
    proved against the shared atomics `T₁` keeps its obligation against any `T₂` when none of its
    reads is a carrier of `T₂` outside `T₁` (`LiestNicht`). -/
theorem koerperGutSA_wachs (h : KoerperGutSA P passes Q S T₁ f)
    (hl : ∀ c ∈ endblockOrteP P (P.rumpf f), ¬ (T₂ c ∧ ¬ T₁ c)) : KoerperGutSA P passes Q S T₂ f := by
  refine ⟨fun O' a b c U hU A hA R hR hOV σ ρ hreq => ?_, fun O' a b c U hU A hA R hR hOL σ ρ hreq => ?_⟩
  · have e := fun R' => Endblock.execHA_gleich P S O' U A passes R' (einschraenken T₁ A) (lese_einschraenken hA)
      (P.rumpf f) hl σ ρ
    obtain ⟨h1, h2⟩ := h.1 O' a b c U hU _ (havocA_einschraenken T₁ A) R hR hOV σ ρ hreq
    refine ⟨fun σ' v hr => h1 σ' v ((e R).symm.trans hr), fun g hr => h2 g ((e _).symm.trans hr)⟩
  · have e := Endblock.execHA_gleich P S O' U A passes R (einschraenken T₁ A) (lese_einschraenken hA) (P.rumpf f) hl σ ρ
    exact fun e' hr => h.2 O' a b c U hU _ (havocA_einschraenken T₁ A) R hR hOL σ ρ hreq e'
      ((e).symm.trans hr)

theorem invGutSA_wachs (h : InvGutSA P passes Q S T₁ f)
    (hl : ∀ c ∈ endblockOrteP P (P.rumpf f), ¬ (T₂ c ∧ ¬ T₁ c)) : InvGutSA P passes Q S T₂ f :=
  fun O' a b c U hU A hA R hR hOV σ ρ hreq σ' v hr =>
    h O' a b c U hU _ (havocA_einschraenken T₁ A) R hR hOV σ ρ hreq σ' v
      ((Endblock.execHA_gleich P S O' U A passes R (einschraenken T₁ A) (lese_einschraenken hA) (P.rumpf f) hl σ ρ).symm.trans hr)

theorem invGutGrundA_wachs (h : InvGutGrundA P passes Q S T₁ f)
    (hl : ∀ c ∈ endblockOrteP P (P.rumpf f), ¬ (T₂ c ∧ ¬ T₁ c)) : InvGutGrundA P passes Q S T₂ f :=
  fun O' a b c U hU A hA R hR hOV σ ρ hreq σ' r hr =>
    h O' a b c U hU _ (havocA_einschraenken T₁ A) R hR hOV σ ρ hreq σ' r
      ((Endblock.execHA_gleich P S O' U A passes R (einschraenken T₁ A) (lese_einschraenken hA) (P.rumpf f) hl σ ρ).symm.trans hr)

end Wachs

#print axioms koerperGutSA_wachs

end Gabbro.Grammatik
