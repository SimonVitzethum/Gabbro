/-
  Coarse and fine cell observations and accepted-program compiler coverage. Full acceptance retains explicit invariant and contract gates.
-/
module
public import Grammatik.Gen.Fein.Satz
public import Grammatik.Gen.Abdeckung.Satz.Neutral
@[expose] public section


namespace Gabbro.Grammatik.Gen.Fein

open Gabbro.Grammatik Gabbro.Grammatik.Gen Gabbro.Grammatik.Adaequanz

/-- The cells of both kinds. -/
abbrev ZelleF : Type := Zelle ⊕ FZelle

/-- A program has a cell of either kind. -/
def HatZ (e : Einsatz) : ZelleF → Prop
  | .inl z => e.Hat z
  | .inr c => e.HatF c

/-- The model's table over both kinds: a coarse cell is admitted when it is not bad, a fine cell always (the model's
    verdict does not depend on the fine cells). -/
def gutZ : ZelleF → Bool
  | .inl z => gutTafel z
  | .inr _ => true

/-- Fine cells add no refusal; full acceptance still requires both semantic gates. -/
theorem akzeptiert_Z (e : Einsatz) : e.gueltig = true ↔
    akzeptiert HatZ gutZ e ∧
      @Invarianten.Pruefer.programInvariantsB e.D e.P e.S e.fs e.lockSources {} e.ls = true ∧
      @Vertraege.Pruefer.KontrakteGeprueftB e.D e.P e.S e.fs e.lockSources {} (fun _ => none) none = true := by
  rw [einsatz_akzeptiert e]
  have structural : akzeptiert HatZ gutZ e ↔ akzeptiert Einsatz.Hat gutTafel e := by
    constructor
    · intro h z hz
      exact h (.inl z) hz
    · intro h w hw
      cases w with
      | inl z => exact h z hw
      | inr c => rfl
  rw [structural]

/-- **The fine table**: every witness is valid, and every allowed fine cell has a witness or no valid program has it. -/
structure FeinTafel (MF : List Einsatz) : Prop where
  gut : ∀ m ∈ MF, m.gueltig = true
  deckt : ∀ c ∈ uF, (∃ m ∈ MF, m.HatF c) ∨ ∀ e : Einsatz, e.HatF c → e.gueltig = false


/-- **A checker neutral over both kinds of cells**: its answer is one fixed table read over the program's coarse and
    fine cells. -/
def NeutralF (C : Einsatz → Bool) : Prop := ∃ φ : ZelleF → Bool, ∀ e, C e = true ↔ akzeptiert HatZ φ e

/-- A neutral checker is neutral over both kinds: the weaker assumption. -/
theorem neutral_neutralF {C : Einsatz → Bool} (h : Neutral C) : NeutralF C := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨fun | .inl z => φ z | .inr _ => true, fun e => (hφ e).trans ⟨fun h w hw => ?_, fun h z hz => h (.inl z) hz⟩⟩
  cases w with
  | inl z => exact h z hw
  | inr c => rfl


/-- **A compiler neutral over both kinds of cells**: correct on a program exactly when correct on each of its cells. -/
def NeutralKorrektF (K : Einsatz → Prop) : Prop := ∃ ψ : ZelleF → Prop, ∀ e, K e ↔ ∀ w, HatZ e w → ψ w

theorem neutralKorrekt_F {K : Einsatz → Prop} (h : NeutralKorrekt K) : NeutralKorrektF K := by
  obtain ⟨ψ, hψ⟩ := h
  refine ⟨fun | .inl z => ψ z | .inr _ => True, fun e => (hψ e).trans ⟨fun h w hw => ?_, fun h z hz => h (.inl z) hz⟩⟩
  cases w with
  | inl z => exact h z hw
  | inr c => trivial

/-- **The compiler theorem over both kinds of cells.** -/
theorem compiler_fein {M N MF : List Einsatz} (t : Tafel M N) (tf : FeinTafel MF) (K : Einsatz → Prop)
    (hK : NeutralKorrektF K) (hM : ∀ m ∈ M ++ MF, K m) (e : Einsatz) (hv : e.gueltig = true) : K e := by
  obtain ⟨ψ, hψ⟩ := hK
  refine (hψ e).2 fun w hw => ?_
  cases w with
  | inl z =>
    obtain ⟨m, hm, hmz⟩ := zellen_deckt t.gut e hv z hw
    exact (hψ m).1 (hM m (List.mem_append_left _ hm)) (.inl z) hmz
  | inr c =>
    rcases tf.deckt c (feinZellen_uF e hw) with ⟨m, hm, hmc⟩ | h
    · exact (hψ m).1 (hM m (List.mem_append_right _ hm)) (.inr c) hmc
    · rw [h e hw] at hv
      cases hv

end Gabbro.Grammatik.Gen.Fein
