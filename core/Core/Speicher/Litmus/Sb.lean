/-
  File:      core/Core/Speicher/Litmus/Sb.lean
  Subject:   STORE BUFFERING (SB) catalogue entry: the two-thread shape
             `x := 1; r1 := y ‖ y := 1; r2 := x` with both reads observing the initial value.

  Source: Lahav et al., "Repairing Sequential Consistency in C/C++11" (PLDI 2017), the standard
  SB test, and the RC11 model the paper repairs (fence-free fragment: the language has no fence
  form; the order of an access is the mode of its location).
  Modes: every access `sc` (forbidden half); every access `.ra` (allowed half -- the same graph
  is consistent for every non-`seq_cst` mode by `sb_ohne_sc_erlaubt`, so `rlx` and `na` behave
  like `ra` here).
  Expected: FORBIDDEN for `sc` (no consistent all-`seq_cst` graph shows the outcome), ALLOWED
  below `seq_cst` (a consistent and complete graph shows it). The pair keeps the forbidden half
  non-vacuous: the outcome is excluded by the strength of the mode, not by impossibility.
-/
module

public import Core.Speicher.Trennung
public import Core.Speicher.Einbettung

@[expose] public section

namespace Gabbro.Core.Speicher

open SbEv

/-- **Store buffering is forbidden for `seq_cst`.** No consistent graph in which every access is
    `seq_cst` has thread 1 write `a₁` then read `b₁` and thread 2 write `a₂` then read `b₂` with
    both reads missing the other thread's write. Feeds: `Graph.sb_sc_verboten`. -/
def SbScVerbotenAussage : Prop :=
  ¬ ∃ (E Ort Wert : Type) (G : Graph E Ort Wert),
    G.Konsistent ∧ (∀ a, G.sc a) ∧
      ∃ a₁ b₁ a₂ b₂ : E, G.po a₁ b₁ ∧ G.po a₂ b₂ ∧ G.rb b₁ a₂ ∧ G.rb b₂ a₁

theorem sb_sc_verboten_kat : SbScVerbotenAussage := by
  rintro ⟨E, Ort, Wert, G, hk, hsc, a₁, b₁, a₂, b₂, p₁, p₂, r₁, r₂⟩
  exact Graph.sb_sc_verboten hk (hsc a₁) (hsc b₁) (hsc a₂) (hsc b₂) p₁ p₂ r₁ r₂

/-- Every read of the store-buffering graph has a reads-from source (the two reads observe the
    initial writes). -/
theorem sb_vollstaendig (m : Modus) : (sbGraph m).Vollstaendig := by
  intro r hr
  cases r with
  | ix => exact (hr : False).elim
  | iy => exact (hr : False).elim
  | a1 => exact (hr : False).elim
  | b1 => exact ⟨iy, Or.inl ⟨rfl, rfl⟩⟩
  | a2 => exact (hr : False).elim
  | b2 => exact ⟨ix, Or.inr ⟨rfl, rfl⟩⟩

/-- **The same store-buffering outcome is allowed below `seq_cst`.** Some consistent and
    complete graph (all accesses `.ra`) has the two writes with their program-order reads and
    both reads-before edges. Feeds: `sb_ohne_sc_erlaubt` (consistency and the four shape edges),
    `sb_vollstaendig` (every read has a source). -/
def SbRaErlaubtAussage : Prop :=
  ∃ (E Ort Wert : Type) (G : Graph E Ort Wert),
    G.Konsistent ∧ G.Vollstaendig ∧
      ∃ a₁ b₁ a₂ b₂ : E, G.po a₁ b₁ ∧ G.po a₂ b₂ ∧ G.rb b₁ a₂ ∧ G.rb b₂ a₁

theorem sb_ra_erlaubt_kat : SbRaErlaubtAussage := by
  obtain ⟨hk, p₁, p₂, r₁, r₂⟩ := sb_ohne_sc_erlaubt .ra (by decide)
  exact ⟨SbEv, Bool, Nat, sbGraph .ra, hk, sb_vollstaendig .ra, a1, b1, a2, b2, p₁, p₂, r₁, r₂⟩

end Gabbro.Core.Speicher
