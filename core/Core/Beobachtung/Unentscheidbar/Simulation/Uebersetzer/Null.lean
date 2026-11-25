module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Grundlagen

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The constant block: write zero into the output slot and fall through. -/
def zeroBlk (ein aus frei : Nat) : List Befehl :=
  [.literal aus 0]

theorem zeroBlkLaenge (ein aus frei : Nat) : (zeroBlk ein aus frei).length = 1 := by
  rfl

def frameZero (r : Rahmen) (aus : Nat) : Rahmen :=
  { r with pc := r.pc + 1, temp := Function.update r.temp aus (some (natVal 0)) }

theorem schrittZero (ein aus frei : Nat) (r : Rahmen) (hpc : r.pc = 0) :
    Schritt (zeroBlk ein aus frei) (some r) = some (frameZero r aus) := by
  have hget : (zeroBlk ein aus frei)[r.pc]? = some (.literal aus 0) := by
    rw [hpc]
    rfl
  simp only [Schritt, hget]
  rfl

theorem blockZero (ein aus frei : Nat) (hein : ein < frei) (haus : aus < frei)
    (hunters : ein ≠ aus) :
    BlockKorrekt (zeroBlk ein aus frei) .zero ein aus frei := by
  unfold BlockKorrekt
  apply And.intro hein
  apply And.intro haus
  apply And.intro hunters
  intro n r hpc hr
  refine ⟨?_, ?_⟩
  · intro a ha
    have ha0 : a = 0 := by
      have h0 : Part.some 0 = Part.some a := by
        change Part.some 0 = Part.some a at ha
        exact ha
      exact (Part.some_injective h0).symm
    refine ⟨1, frameZero r aus, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Schritt (zeroBlk ein aus frei) (some r) = some (frameZero r aus)
      exact schrittZero ein aus frei r hpc
    · show (frameZero r aus).pc = (zeroBlk ein aus frei).length
      rw [zeroBlkLaenge]
      show r.pc + 1 = 1
      omega
    · show (frameZero r aus).temp aus = some (natVal a)
      rw [ha0]
      exact updateHit _ _ _
    · intro s hs hne
      show Function.update r.temp aus _ s = r.temp s
      exact updateMiss _ _ _ _ hne
    · rfl
    · rfl
    · rfl
  · intro k r' hk hpc'
    rcases k with _ | _ | t
    · have h0 : (Schritt (zeroBlk ein aus frei))^[0] (some r) = some r := rfl
      rw [h0] at hk
      have hrr := Option.some.inj hk
      subst r'
      have hlen : (zeroBlk ein aus frei).length = 1 := zeroBlkLaenge _ _ _
      omega
    · have e1 : (Schritt (zeroBlk ein aus frei))^[1] (some r) = some (frameZero r aus) := by
        show Schritt (zeroBlk ein aus frei) (some r) = some (frameZero r aus)
        exact schrittZero ein aus frei r hpc
      rw [e1] at hk
      have hrr := Option.some.inj hk
      subst r'
      refine ⟨0, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · show (frameZero r aus).temp aus = some (natVal 0)
        exact updateHit _ _ _
      · intro s hs hne
        show Function.update r.temp aus _ s = r.temp s
        exact updateMiss _ _ _ _ hne
      · rfl
      · rfl
      · rfl
    · have e2 : (Schritt (zeroBlk ein aus frei))^[2] (some r) = none := by
        have e1 : (Schritt (zeroBlk ein aus frei))^[1] (some r) = some (frameZero r aus) := by
          show Schritt (zeroBlk ein aus frei) (some r) = some (frameZero r aus)
          exact schrittZero ein aus frei r hpc
        have e : (Schritt (zeroBlk ein aus frei))^[2] (some r) =
            Schritt (zeroBlk ein aus frei) ((Schritt (zeroBlk ein aus frei))^[1] (some r)) := rfl
        rw [e, e1]
        exact schrittAmEnde _ _ (by rw [zeroBlkLaenge]; show r.pc + 1 = 1; omega)
      have hk' : (Schritt (zeroBlk ein aus frei))^[2 + t] (some r) = some r' := by
        simpa only [show t + 1 + 1 = 2 + t by omega] using hk
      rw [show 2 + t = t + 2 by omega, Function.iterate_add_apply, e2, laufKein] at hk'
      cases hk'

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
