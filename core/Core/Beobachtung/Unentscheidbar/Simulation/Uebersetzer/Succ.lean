module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.SuccSchritt

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

theorem blockSucc (ein aus frei : Nat) (hein : ein < frei) (haus : aus < frei)
    (hunters : ein ≠ aus) :
    BlockKorrekt (succBlk ein aus frei) .succ ein aus frei := by
  unfold BlockKorrekt
  apply And.intro hein
  apply And.intro haus
  apply And.intro hunters
  intro n r hpc hr
  refine ⟨?_, ?_⟩
  · intro a ha
    have ha1 : a = n + 1 := by
      have h0 : Part.some (n + 1) = Part.some a := by
        change Part.some (n + 1) = Part.some a at ha
        exact ha
      exact (Part.some_injective h0).symm
    have h1 : frei ≠ frei + 1 := by omega
    have h2 : aus ≠ frei := by omega
    have h3 : aus ≠ frei + 1 := by omega
    have hF8t : (frameSucc8 r ein aus frei n).temp = (frameSucc7 r ein aus frei n).temp := rfl
    have hF7a : (frameSucc7 r ein aus frei n).temp aus =
        (frameSucc6 r ein aus frei n).temp frei := updateHit _ _ _
    have hF6t : (frameSucc6 r ein aus frei n).temp = (frameSucc5 r ein aus frei n).temp := rfl
    have hF5f : (frameSucc5 r ein aus frei n).temp frei =
        some (Ganzzahl.pack ⟨_, _, Arith.auswerten .add (Zahl.literal (n : Int)) (Zahl.literal ((1 : Nat) : Int))⟩) :=
      updateHit _ _ _
    refine ⟨8, frameSucc8 r ein aus frei n, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[7] (some r)) =
        some (frameSucc8 r ein aus frei n)
      have g1 : (Schritt (succBlk ein aus frei))^[1] (some r) = some (frameSucc1 r ein frei) := by
        show Schritt (succBlk ein aus frei) (some r) = some (frameSucc1 r ein frei)
        exact succSchritt0 ein aus frei r hpc
      have g2 : (Schritt (succBlk ein aus frei))^[2] (some r) = some (frameSucc2 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[2] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[1] (some r)) := rfl
        rw [e, g1]
        exact succSchritt1 ein aus frei r hpc
      have g3 : (Schritt (succBlk ein aus frei))^[3] (some r) = some (frameSucc3 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[3] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[2] (some r)) := rfl
        rw [e, g2]
        exact succSchritt2 ein aus frei r hpc
      have g4 : (Schritt (succBlk ein aus frei))^[4] (some r) = some (frameSucc4 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[4] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[3] (some r)) := rfl
        rw [e, g3]
        exact succSchritt3 ein aus frei r hpc
      have g5 : (Schritt (succBlk ein aus frei))^[5] (some r) = some (frameSucc5 r ein aus frei n) := by
        have e : (Schritt (succBlk ein aus frei))^[5] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[4] (some r)) := rfl
        rw [e, g4]
        exact succSchritt4 ein aus frei r hr hpc hein
      have g6 : (Schritt (succBlk ein aus frei))^[6] (some r) = some (frameSucc6 r ein aus frei n) := by
        have e : (Schritt (succBlk ein aus frei))^[6] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[5] (some r)) := rfl
        rw [e, g5]
        exact succSchritt5 ein aus frei r n hpc
      have g7 : (Schritt (succBlk ein aus frei))^[7] (some r) = some (frameSucc7 r ein aus frei n) := by
        have e : (Schritt (succBlk ein aus frei))^[7] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[6] (some r)) := rfl
        rw [e, g6]
        exact succSchritt6 ein aus frei r n hpc
      rw [g7]
      exact succSchritt7 ein aus frei r n hpc
    · show (frameSucc8 r ein aus frei n).pc = (succBlk ein aus frei).length
      rw [succBlkLaenge]
      show r.pc + 8 = 8
      omega
    · show (frameSucc8 r ein aus frei n).temp aus = some (natVal a)
      rw [hF8t, hF7a, hF6t, hF5f, ha1]
      have hcast : (Ganzzahl.pack ⟨_, _, Arith.auswerten .add (Zahl.literal (n : Int)) (Zahl.literal ((1 : Nat) : Int))⟩) =
          natVal (n + 1) := by
        rfl
      rw [hcast]
    · intro s hs hne
      have hnef : s ≠ frei := by omega
      have hnef1 : s ≠ frei + 1 := by omega
      show (frameSucc8 r ein aus frei n).temp s = r.temp s
      rw [hF8t]
      show (frameSucc7 r ein aus frei n).temp s = r.temp s
      have e7 : (frameSucc7 r ein aus frei n).temp s = (frameSucc6 r ein aus frei n).temp s := by
        show Function.update _ aus _ s = _
        exact updateMiss _ _ _ _ hne
      rw [e7, hF6t]
      show (frameSucc5 r ein aus frei n).temp s = r.temp s
      have e5 : (frameSucc5 r ein aus frei n).temp s = (frameSucc4 r ein frei).temp s := by
        show Function.update _ frei _ s = _
        exact updateMiss _ _ _ _ hnef
      rw [e5]
      show (frameSucc4 r ein frei).temp s = r.temp s
      have e4 : (frameSucc4 r ein frei).temp s = (frameSucc3 r ein frei).temp s := by
        show Function.update _ (frei + 1) _ s = _
        exact updateMiss _ _ _ _ hnef1
      rw [e4]
      show (frameSucc3 r ein frei).temp s = r.temp s
      have e3 : (frameSucc3 r ein frei).temp = (frameSucc2 r ein frei).temp := rfl
      rw [e3]
      show (frameSucc2 r ein frei).temp s = r.temp s
      have e2 : (frameSucc2 r ein frei).temp s = (frameSucc1 r ein frei).temp s := by
        show Function.update _ frei _ s = _
        exact updateMiss _ _ _ _ hnef
      rw [e2]
      rfl
    · rfl
    · rfl
    · rfl
  · intro k r' hk hpc'
    have h9 : (Schritt (succBlk ein aus frei))^[9] (some r) = none := by
      have g8 : (Schritt (succBlk ein aus frei))^[8] (some r) = some (frameSucc8 r ein aus frei n) := by
        have g1 : (Schritt (succBlk ein aus frei))^[1] (some r) = some (frameSucc1 r ein frei) := by
          show Schritt (succBlk ein aus frei) (some r) = some (frameSucc1 r ein frei)
          exact succSchritt0 ein aus frei r hpc
        have g2 : (Schritt (succBlk ein aus frei))^[2] (some r) = some (frameSucc2 r ein frei) := by
          have e : (Schritt (succBlk ein aus frei))^[2] (some r) =
              Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[1] (some r)) := rfl
          rw [e, g1]
          exact succSchritt1 ein aus frei r hpc
        have g3 : (Schritt (succBlk ein aus frei))^[3] (some r) = some (frameSucc3 r ein frei) := by
          have e : (Schritt (succBlk ein aus frei))^[3] (some r) =
              Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[2] (some r)) := rfl
          rw [e, g2]
          exact succSchritt2 ein aus frei r hpc
        have g4 : (Schritt (succBlk ein aus frei))^[4] (some r) = some (frameSucc4 r ein frei) := by
          have e : (Schritt (succBlk ein aus frei))^[4] (some r) =
              Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[3] (some r)) := rfl
          rw [e, g3]
          exact succSchritt3 ein aus frei r hpc
        have g5 : (Schritt (succBlk ein aus frei))^[5] (some r) = some (frameSucc5 r ein aus frei n) := by
          have e : (Schritt (succBlk ein aus frei))^[5] (some r) =
              Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[4] (some r)) := rfl
          rw [e, g4]
          exact succSchritt4 ein aus frei r hr hpc hein
        have g6 : (Schritt (succBlk ein aus frei))^[6] (some r) = some (frameSucc6 r ein aus frei n) := by
          have e : (Schritt (succBlk ein aus frei))^[6] (some r) =
              Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[5] (some r)) := rfl
          rw [e, g5]
          exact succSchritt5 ein aus frei r n hpc
        have g7 : (Schritt (succBlk ein aus frei))^[7] (some r) = some (frameSucc7 r ein aus frei n) := by
          have e : (Schritt (succBlk ein aus frei))^[7] (some r) =
              Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[6] (some r)) := rfl
          rw [e, g6]
          exact succSchritt6 ein aus frei r n hpc
        have e : (Schritt (succBlk ein aus frei))^[8] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[7] (some r)) := rfl
        rw [e, g7]
        exact succSchritt7 ein aus frei r n hpc
      have e : (Schritt (succBlk ein aus frei))^[9] (some r) =
          Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[8] (some r)) := rfl
      rw [e, g8]
      exact schrittAmEnde _ _ (by rw [succBlkLaenge]; show r.pc + 8 = 8; omega)
    have h1 : frei ≠ frei + 1 := by omega
    have h2 : aus ≠ frei := by omega
    have h3 : aus ≠ frei + 1 := by omega
    have hF8t : (frameSucc8 r ein aus frei n).temp = (frameSucc7 r ein aus frei n).temp := rfl
    have hF7a : (frameSucc7 r ein aus frei n).temp aus =
        (frameSucc6 r ein aus frei n).temp frei := updateHit _ _ _
    have hF6t : (frameSucc6 r ein aus frei n).temp = (frameSucc5 r ein aus frei n).temp := rfl
    have hF5f : (frameSucc5 r ein aus frei n).temp frei =
        some (Ganzzahl.pack ⟨_, _, Arith.auswerten .add (Zahl.literal (n : Int)) (Zahl.literal ((1 : Nat) : Int))⟩) :=
      updateHit _ _ _
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | t
    · have h0 : (Schritt (succBlk ein aus frei))^[0] (some r) = some r := rfl
      rw [h0] at hk
      have hrr := Option.some.inj hk
      subst r'
      have hlen : (succBlk ein aus frei).length = 8 := succBlkLaenge _ _ _
      omega
    · have g1 : (Schritt (succBlk ein aus frei))^[1] (some r) = some (frameSucc1 r ein frei) := by
        show Schritt (succBlk ein aus frei) (some r) = some (frameSucc1 r ein frei)
        exact succSchritt0 ein aus frei r hpc
      rw [g1] at hk
      have hrr := Option.some.inj hk
      subst r'
      have hlen : (succBlk ein aus frei).length = 8 := succBlkLaenge _ _ _
      have hpc1 : (frameSucc1 r ein frei).pc = 8 := by
        rw [succBlkLaenge] at hpc'
        exact hpc'
      have hF1pc : (frameSucc1 r ein frei).pc = r.pc + 1 := rfl
      omega
    · have g1 : (Schritt (succBlk ein aus frei))^[1] (some r) = some (frameSucc1 r ein frei) := by
        show Schritt (succBlk ein aus frei) (some r) = some (frameSucc1 r ein frei)
        exact succSchritt0 ein aus frei r hpc
      have g2 : (Schritt (succBlk ein aus frei))^[2] (some r) = some (frameSucc2 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[2] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[1] (some r)) := rfl
        rw [e, g1]
        exact succSchritt1 ein aus frei r hpc
      rw [g2] at hk
      have hrr := Option.some.inj hk
      subst r'
      have hpc2 : (frameSucc2 r ein frei).pc = 8 := by
        rw [succBlkLaenge] at hpc'
        exact hpc'
      have hF2pc : (frameSucc2 r ein frei).pc = r.pc + 2 := rfl
      omega
    · have g1 : (Schritt (succBlk ein aus frei))^[1] (some r) = some (frameSucc1 r ein frei) := by
        show Schritt (succBlk ein aus frei) (some r) = some (frameSucc1 r ein frei)
        exact succSchritt0 ein aus frei r hpc
      have g2 : (Schritt (succBlk ein aus frei))^[2] (some r) = some (frameSucc2 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[2] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[1] (some r)) := rfl
        rw [e, g1]
        exact succSchritt1 ein aus frei r hpc
      have g3 : (Schritt (succBlk ein aus frei))^[3] (some r) = some (frameSucc3 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[3] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[2] (some r)) := rfl
        rw [e, g2]
        exact succSchritt2 ein aus frei r hpc
      rw [g3] at hk
      have hrr := Option.some.inj hk
      subst r'
      have hpc3 : (frameSucc3 r ein frei).pc = 8 := by
        rw [succBlkLaenge] at hpc'
        exact hpc'
      have hF3pc : (frameSucc3 r ein frei).pc = r.pc + 3 := rfl
      omega
    · have g1 : (Schritt (succBlk ein aus frei))^[1] (some r) = some (frameSucc1 r ein frei) := by
        show Schritt (succBlk ein aus frei) (some r) = some (frameSucc1 r ein frei)
        exact succSchritt0 ein aus frei r hpc
      have g2 : (Schritt (succBlk ein aus frei))^[2] (some r) = some (frameSucc2 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[2] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[1] (some r)) := rfl
        rw [e, g1]
        exact succSchritt1 ein aus frei r hpc
      have g3 : (Schritt (succBlk ein aus frei))^[3] (some r) = some (frameSucc3 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[3] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[2] (some r)) := rfl
        rw [e, g2]
        exact succSchritt2 ein aus frei r hpc
      have g4 : (Schritt (succBlk ein aus frei))^[4] (some r) = some (frameSucc4 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[4] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[3] (some r)) := rfl
        rw [e, g3]
        exact succSchritt3 ein aus frei r hpc
      rw [g4] at hk
      have hrr := Option.some.inj hk
      subst r'
      have hpc4 : (frameSucc4 r ein frei).pc = 8 := by
        rw [succBlkLaenge] at hpc'
        exact hpc'
      have hF4pc : (frameSucc4 r ein frei).pc = r.pc + 4 := rfl
      omega
    · have g1 : (Schritt (succBlk ein aus frei))^[1] (some r) = some (frameSucc1 r ein frei) := by
        show Schritt (succBlk ein aus frei) (some r) = some (frameSucc1 r ein frei)
        exact succSchritt0 ein aus frei r hpc
      have g2 : (Schritt (succBlk ein aus frei))^[2] (some r) = some (frameSucc2 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[2] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[1] (some r)) := rfl
        rw [e, g1]
        exact succSchritt1 ein aus frei r hpc
      have g3 : (Schritt (succBlk ein aus frei))^[3] (some r) = some (frameSucc3 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[3] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[2] (some r)) := rfl
        rw [e, g2]
        exact succSchritt2 ein aus frei r hpc
      have g4 : (Schritt (succBlk ein aus frei))^[4] (some r) = some (frameSucc4 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[4] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[3] (some r)) := rfl
        rw [e, g3]
        exact succSchritt3 ein aus frei r hpc
      have g5 : (Schritt (succBlk ein aus frei))^[5] (some r) = some (frameSucc5 r ein aus frei n) := by
        have e : (Schritt (succBlk ein aus frei))^[5] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[4] (some r)) := rfl
        rw [e, g4]
        exact succSchritt4 ein aus frei r hr hpc hein
      rw [g5] at hk
      have hrr := Option.some.inj hk
      subst r'
      have hpc5 : (frameSucc5 r ein aus frei n).pc = 8 := by
        rw [succBlkLaenge] at hpc'
        exact hpc'
      have hF5pc : (frameSucc5 r ein aus frei n).pc = r.pc + 5 := rfl
      omega
    · have g1 : (Schritt (succBlk ein aus frei))^[1] (some r) = some (frameSucc1 r ein frei) := by
        show Schritt (succBlk ein aus frei) (some r) = some (frameSucc1 r ein frei)
        exact succSchritt0 ein aus frei r hpc
      have g2 : (Schritt (succBlk ein aus frei))^[2] (some r) = some (frameSucc2 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[2] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[1] (some r)) := rfl
        rw [e, g1]
        exact succSchritt1 ein aus frei r hpc
      have g3 : (Schritt (succBlk ein aus frei))^[3] (some r) = some (frameSucc3 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[3] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[2] (some r)) := rfl
        rw [e, g2]
        exact succSchritt2 ein aus frei r hpc
      have g4 : (Schritt (succBlk ein aus frei))^[4] (some r) = some (frameSucc4 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[4] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[3] (some r)) := rfl
        rw [e, g3]
        exact succSchritt3 ein aus frei r hpc
      have g5 : (Schritt (succBlk ein aus frei))^[5] (some r) = some (frameSucc5 r ein aus frei n) := by
        have e : (Schritt (succBlk ein aus frei))^[5] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[4] (some r)) := rfl
        rw [e, g4]
        exact succSchritt4 ein aus frei r hr hpc hein
      have g6 : (Schritt (succBlk ein aus frei))^[6] (some r) = some (frameSucc6 r ein aus frei n) := by
        have e : (Schritt (succBlk ein aus frei))^[6] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[5] (some r)) := rfl
        rw [e, g5]
        exact succSchritt5 ein aus frei r n hpc
      rw [g6] at hk
      have hrr := Option.some.inj hk
      subst r'
      have hpc6 : (frameSucc6 r ein aus frei n).pc = 8 := by
        rw [succBlkLaenge] at hpc'
        exact hpc'
      have hF6pc : (frameSucc6 r ein aus frei n).pc = r.pc + 6 := rfl
      omega
    · have g1 : (Schritt (succBlk ein aus frei))^[1] (some r) = some (frameSucc1 r ein frei) := by
        show Schritt (succBlk ein aus frei) (some r) = some (frameSucc1 r ein frei)
        exact succSchritt0 ein aus frei r hpc
      have g2 : (Schritt (succBlk ein aus frei))^[2] (some r) = some (frameSucc2 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[2] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[1] (some r)) := rfl
        rw [e, g1]
        exact succSchritt1 ein aus frei r hpc
      have g3 : (Schritt (succBlk ein aus frei))^[3] (some r) = some (frameSucc3 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[3] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[2] (some r)) := rfl
        rw [e, g2]
        exact succSchritt2 ein aus frei r hpc
      have g4 : (Schritt (succBlk ein aus frei))^[4] (some r) = some (frameSucc4 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[4] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[3] (some r)) := rfl
        rw [e, g3]
        exact succSchritt3 ein aus frei r hpc
      have g5 : (Schritt (succBlk ein aus frei))^[5] (some r) = some (frameSucc5 r ein aus frei n) := by
        have e : (Schritt (succBlk ein aus frei))^[5] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[4] (some r)) := rfl
        rw [e, g4]
        exact succSchritt4 ein aus frei r hr hpc hein
      have g6 : (Schritt (succBlk ein aus frei))^[6] (some r) = some (frameSucc6 r ein aus frei n) := by
        have e : (Schritt (succBlk ein aus frei))^[6] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[5] (some r)) := rfl
        rw [e, g5]
        exact succSchritt5 ein aus frei r n hpc
      have g7 : (Schritt (succBlk ein aus frei))^[7] (some r) = some (frameSucc7 r ein aus frei n) := by
        have e : (Schritt (succBlk ein aus frei))^[7] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[6] (some r)) := rfl
        rw [e, g6]
        exact succSchritt6 ein aus frei r n hpc
      rw [g7] at hk
      have hrr := Option.some.inj hk
      subst r'
      have hpc7 : (frameSucc7 r ein aus frei n).pc = 8 := by
        rw [succBlkLaenge] at hpc'
        exact hpc'
      have hF7pc : (frameSucc7 r ein aus frei n).pc = r.pc + 7 := rfl
      omega
    · have g1 : (Schritt (succBlk ein aus frei))^[1] (some r) = some (frameSucc1 r ein frei) := by
        show Schritt (succBlk ein aus frei) (some r) = some (frameSucc1 r ein frei)
        exact succSchritt0 ein aus frei r hpc
      have g2 : (Schritt (succBlk ein aus frei))^[2] (some r) = some (frameSucc2 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[2] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[1] (some r)) := rfl
        rw [e, g1]
        exact succSchritt1 ein aus frei r hpc
      have g3 : (Schritt (succBlk ein aus frei))^[3] (some r) = some (frameSucc3 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[3] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[2] (some r)) := rfl
        rw [e, g2]
        exact succSchritt2 ein aus frei r hpc
      have g4 : (Schritt (succBlk ein aus frei))^[4] (some r) = some (frameSucc4 r ein frei) := by
        have e : (Schritt (succBlk ein aus frei))^[4] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[3] (some r)) := rfl
        rw [e, g3]
        exact succSchritt3 ein aus frei r hpc
      have g5 : (Schritt (succBlk ein aus frei))^[5] (some r) = some (frameSucc5 r ein aus frei n) := by
        have e : (Schritt (succBlk ein aus frei))^[5] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[4] (some r)) := rfl
        rw [e, g4]
        exact succSchritt4 ein aus frei r hr hpc hein
      have g6 : (Schritt (succBlk ein aus frei))^[6] (some r) = some (frameSucc6 r ein aus frei n) := by
        have e : (Schritt (succBlk ein aus frei))^[6] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[5] (some r)) := rfl
        rw [e, g5]
        exact succSchritt5 ein aus frei r n hpc
      have g7 : (Schritt (succBlk ein aus frei))^[7] (some r) = some (frameSucc7 r ein aus frei n) := by
        have e : (Schritt (succBlk ein aus frei))^[7] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[6] (some r)) := rfl
        rw [e, g6]
        exact succSchritt6 ein aus frei r n hpc
      have g8 : (Schritt (succBlk ein aus frei))^[8] (some r) = some (frameSucc8 r ein aus frei n) := by
        have e : (Schritt (succBlk ein aus frei))^[8] (some r) =
            Schritt (succBlk ein aus frei) ((Schritt (succBlk ein aus frei))^[7] (some r)) := rfl
        rw [e, g7]
        exact succSchritt7 ein aus frei r n hpc
      rw [g8] at hk
      have hrr := Option.some.inj hk
      subst r'
      refine ⟨n + 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · show (frameSucc8 r ein aus frei n).temp aus = some (natVal (n + 1))
        rw [hF8t, hF7a, hF6t, hF5f]
        have hcast : (Ganzzahl.pack ⟨_, _,
            Arith.auswerten .add (Zahl.literal (n : Int)) (Zahl.literal ((1 : Nat) : Int))⟩) = natVal (n + 1) := by
          rfl
        rw [hcast]
      · intro s hs hne
        have hnef : s ≠ frei := by omega
        have hnef1 : s ≠ frei + 1 := by omega
        show (frameSucc8 r ein aus frei n).temp s = r.temp s
        rw [hF8t]
        show (frameSucc7 r ein aus frei n).temp s = r.temp s
        have e7 : (frameSucc7 r ein aus frei n).temp s = (frameSucc6 r ein aus frei n).temp s := by
          show Function.update _ aus _ s = _
          exact updateMiss _ _ _ _ hne
        rw [e7, hF6t]
        show (frameSucc5 r ein aus frei n).temp s = r.temp s
        have e5 : (frameSucc5 r ein aus frei n).temp s = (frameSucc4 r ein frei).temp s := by
          show Function.update _ frei _ s = _
          exact updateMiss _ _ _ _ hnef
        rw [e5]
        show (frameSucc4 r ein frei).temp s = r.temp s
        have e4 : (frameSucc4 r ein frei).temp s = (frameSucc3 r ein frei).temp s := by
          show Function.update _ (frei + 1) _ s = _
          exact updateMiss _ _ _ _ hnef1
        rw [e4]
        show (frameSucc3 r ein frei).temp s = r.temp s
        have e3 : (frameSucc3 r ein frei).temp = (frameSucc2 r ein frei).temp := rfl
        rw [e3]
        show (frameSucc2 r ein frei).temp s = r.temp s
        have e2 : (frameSucc2 r ein frei).temp s = (frameSucc1 r ein frei).temp s := by
          show Function.update _ frei _ s = _
          exact updateMiss _ _ _ _ hnef
        rw [e2]
        rfl
      · rfl
      · rfl
      · rfl
    · have hk' : (Schritt (succBlk ein aus frei))^[9 + t] (some r) = some r' := by
        simpa only [show t + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 9 + t by omega] using hk
      rw [show 9 + t = t + 9 by omega, Function.iterate_add_apply, h9, laufKein] at hk'
      cases hk'

end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
