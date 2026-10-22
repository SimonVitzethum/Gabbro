/-
  File:      Grammatik/Gen/Fein/Neutral.lean
  Subject:   WHAT THE FINE CELLS BUY: a checker or a compiler may read the program's coarse cells (the components of
             `AkzeptiertX`) AND its fine cells (constructor, loop context, child classes, child constructors). Such an
             implementation is still neutral -- one table over the cells, no branch on a particular program -- but it
             may treat every construct and every pair of directly nested constructs differently. The assumption is
             weaker than `Neutral` (`neutral_neutralF`), so the theorems are stronger:

    * `pruefer_fein`   a checker neutral over both kinds of cells that answers like the model on M, the fine witnesses
                       and N answers like the model on every program of the source;
    * `compiler_fein`  a compiler correct on a program exactly when it is correct on each of its cells of both kinds,
                       correct on M and the fine witnesses, is correct on every valid program of the source.

  Both rest on the coarse table (`Tafel`) and the fine table (`FeinTafel`): every allowed fine cell (`uF`, which
  holds every fine cell of every program, `feinZellen_uF`) has a valid witness or occurs in no valid program.
-/
import Grammatik.Gen.Fein.Satz
import Grammatik.Gen.Abdeckung.Satz.Neutral

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

theorem akzeptiert_Z (e : Einsatz) : akzeptiert HatZ gutZ e ↔ e.gueltig = true := by
  rw [← einsatz_akzeptiert e]
  constructor
  · intro h z hz
    exact h (.inl z) hz
  · intro h w hw
    cases w with
    | inl z => exact h z hw
    | inr c => rfl

/-- **The fine table**: every witness is valid, and every allowed fine cell has a witness or no valid program has it. -/
structure FeinTafel (MF : List Einsatz) : Prop where
  gut : ∀ m ∈ MF, m.gueltig = true
  deckt : ∀ c ∈ uF, (∃ m ∈ MF, m.HatF c) ∨ ∀ e : Einsatz, e.HatF c → e.gueltig = false

/-- **The two tables give Theorem 5's condition over both kinds of cells**, when the fine cells of the tests of N are
    witnessed (a refused test may only fail on its coarse cell). -/
theorem vollstaendig_fein {M N MF : List Einsatz} (t : Tafel M N) (tf : FeinTafel MF)
    (hNF : ∀ n ∈ N, ∀ c, n.HatF c → ∃ m ∈ MF, m.HatF c) : Vollstaendig HatZ gutZ (M ++ MF) N where
  gut_m m hm := by
    rcases List.mem_append.1 hm with h | h
    · exact (akzeptiert_Z m).2 (t.gut_m m h)
    · exact (akzeptiert_Z m).2 (tf.gut m h)
  gut p w hw hp := by
    have hv := (akzeptiert_Z p).1 hp
    cases w with
    | inl z =>
      obtain ⟨m, hm, hmz⟩ := (vollstaendig_aus_tafel t).gut p z hw ((einsatz_akzeptiert p).2 hv)
      exact ⟨m, List.mem_append_left _ hm, hmz⟩
    | inr c =>
      rcases tf.deckt c (feinZellen_uF p hw) with ⟨m, hm, hmc⟩ | h
      · exact ⟨m, List.mem_append_right _ hm, hmc⟩
      · rw [h p hw] at hv
        cases hv
  n_schlecht n hn ha := by
    have := (akzeptiert_Z n).1 ha
    rw [t.n_schlecht n hn] at this
    cases this
  schlecht p hp := by
    have hp' : ¬ akzeptiert Einsatz.Hat gutTafel p := fun h => hp ((akzeptiert_Z p).2 ((einsatz_akzeptiert p).1 h))
    obtain ⟨n, hn, hw⟩ := (vollstaendig_aus_tafel t).schlecht p hp'
    refine ⟨n, hn, fun w hnw => ?_⟩
    cases w with
    | inl z =>
      rcases hw z hnw with h | ⟨m, hm, hmz⟩
      · exact Or.inl h
      · exact Or.inr ⟨m, List.mem_append_left _ hm, hmz⟩
    | inr c =>
      obtain ⟨m, hm, hmc⟩ := hNF n hn c hnw
      exact Or.inr ⟨m, List.mem_append_right _ hm, hmc⟩

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

/-- **Theorem 5 over both kinds of cells, for a checker.** -/
theorem pruefer_fein {M N MF : List Einsatz} (t : Tafel M N) (tf : FeinTafel MF)
    (hNF : ∀ n ∈ N, ∀ c, n.HatF c → ∃ m ∈ MF, m.HatF c) (C : Einsatz → Bool) (hC : NeutralF C)
    (hM : ∀ m ∈ M ++ MF, C m = m.gueltig) (hN : ∀ n ∈ N, C n = n.gueltig) (e : Einsatz) : C e = e.gueltig := by
  obtain ⟨φ, hφ⟩ := hC
  have h := vollstaendig_hinreichend HatZ (vollstaendig_fein t tf hNF) φ
    (fun m hm => by rw [← hφ m, hM m hm, akzeptiert_Z m])
    (fun n hn => by rw [← hφ n, hN n hn, akzeptiert_Z n]) e
  rw [Bool.eq_iff_iff, hφ e, h, akzeptiert_Z e]

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
    obtain ⟨m, hm, hmz⟩ := (vollstaendig_aus_tafel t).gut e z hw ((einsatz_akzeptiert e).2 hv)
    exact (hψ m).1 (hM m (List.mem_append_left _ hm)) (.inl z) hmz
  | inr c =>
    rcases tf.deckt c (feinZellen_uF e hw) with ⟨m, hm, hmc⟩ | h
    · exact (hψ m).1 (hM m (List.mem_append_right _ hm)) (.inr c) hmc
    · rw [h e hw] at hv
      cases hv

end Gabbro.Grammatik.Gen.Fein
