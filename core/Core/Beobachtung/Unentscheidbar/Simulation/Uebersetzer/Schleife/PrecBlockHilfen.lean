module

public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecBlock
public import Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer.Schleife.PrecSchleifeStark

@[expose] public section

namespace Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer

open Gabbro.Core.Ast
open Gabbro.Core.Ast.Semantik

/-- The left projection segment of the recursion block, opaque so that its
    fifty-instruction body is never unfolded while checking a proof. -/
@[irreducible] def precBlkLinks (ein frei freiL : Nat) : List Befehl :=
  leftBlk ein (frei + 0) freiL

theorem precBlkLinksGleich (ein frei freiL : Nat) :
    precBlkLinks ein frei freiL = leftBlk ein (frei + 0) freiL := by
  unfold precBlkLinks
  rfl

theorem precBlkLinksLaenge (ein frei freiL : Nat) : (precBlkLinks ein frei freiL).length = 50 := by
  rw [precBlkLinksGleich, leftBlkLaenge]

theorem precBlkLinksBleibt (ein frei freiL : Nat) : BleibtImBlock (precBlkLinks ein frei freiL) := by
  rw [precBlkLinksGleich]
  exact bleibtImBlockLeft ein (frei + 0) freiL

theorem precBlkLinksKorrekt (ein frei freiL : Nat) (hein : ein < freiL)
    (hzwei : frei + 0 < freiL) (hne : ein ≠ frei + 0) :
    BlockKorrekt (precBlkLinks ein frei freiL) .left ein (frei + 0) freiL := by
  rw [precBlkLinksGleich]
  exact blockLeft ein (frei + 0) freiL hein hzwei hne

/-- The right projection segment, opaque for the same reason. -/
@[irreducible] def precBlkRechts (ein frei freiL : Nat) : List Befehl :=
  rightBlk ein (frei + 1) freiL

theorem precBlkRechtsGleich (ein frei freiL : Nat) :
    precBlkRechts ein frei freiL = rightBlk ein (frei + 1) freiL := by
  unfold precBlkRechts
  rfl

theorem precBlkRechtsLaenge (ein frei freiL : Nat) : (precBlkRechts ein frei freiL).length = 57 := by
  rw [precBlkRechtsGleich, rightBlkLaenge]

theorem precBlkRechtsBleibt (ein frei freiL : Nat) : BleibtImBlock (precBlkRechts ein frei freiL) := by
  rw [precBlkRechtsGleich]
  exact bleibtImBlockRight ein (frei + 1) freiL

theorem precBlkRechtsVerschiebbar (ein frei freiL : Nat) :
    VerschiebbaresProgramm (precBlkRechts ein frei freiL) := by
  rw [precBlkRechtsGleich]
  exact verschiebbarRight ein (frei + 1) freiL

theorem precBlkRechtsKorrekt (ein frei freiL : Nat) (hein : ein < freiL)
    (hzwei : frei + 1 < freiL) (hne : ein ≠ frei + 1) :
    BlockKorrekt (precBlkRechts ein frei freiL) .right ein (frei + 1) freiL := by
  rw [precBlkRechtsGleich]
  exact blockRight ein (frei + 1) freiL hein hzwei hne

/-- A standalone run that reaches the end of a prefix is also a run of the
    concatenation with any suffix. -/
theorem laufImAnhang (pre post : List Befehl) (r : Rahmen) (k : Nat) (r' : Rahmen)
    (h : (Schritt pre)^[k] (some r) = some r') (hpc : r'.pc = pre.length) :
    (Schritt (pre ++ post))^[k] (some r) = some r' := by
  have hbleib := laufBleibtVorEnde pre r k r' h hpc
  exact (laufAnhang pre post r k hbleib).trans h
end Gabbro.Core.Beobachtung.Unentscheidbar.Simulation.Uebersetzer
