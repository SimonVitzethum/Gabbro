/-
  File:      Grammatik/Zielsatz/Eigenschaften/BudgetZeuge.lean
  Subject:   WITNESS OF THE LEG `budgetUnecht` (2026-10-22): the stop on budget happens, and one budget higher the
             same thread steps on.

  The declaration has one function and nothing else; its body is `forever { }` followed by `return`. From the start
  machine, two steps of machine G at budget `0` (`endeEntf`, `dannForever`) reach a machine at which thread `0`
  stands at a spent budget (`bz_halt`): the premise of the leg is met on a reached machine. At budget `1` the shifted
  machine is reached as well (`bz_erreicht1`, from `rufErreichbarG_plus`), and thread `0` takes its next
  pass there (`bz_weiter`, the step `ewigWeiter`).
-/
import Grammatik.Zielsatz.Atomar.BeweisAtomar
import Grammatik.Kern.Syntax.Satz

namespace Gabbro.Grammatik.Zielsatz.BudgetZeuge

open Gabbro.Grammatik

/-- One function, no carriers, no locks. -/
@[reducible] def bD : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun t => t.elim
  Feld := fun t => t.elim
  decFeld := fun t => t.elim
  typ := fun t => t.elim
  erlaubt := fun t => t.elim
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun g => g.elim
  nutzlast := fun g => g.elim
  atomar := fun g => g.elim
  geteilt := fun t => t.elim
  ggeteilt := fun g => g.elim
  Lock := Empty
  decLock := inferInstance
  rang := fun L => L.elim
  maskiert := fun L => L.elim
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => m.elim
  braucht := fun t => t.elim
  gbraucht := fun g => g.elim
  eigner := fun t => t.elim
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => ⟨[], none, 0, [], fun t => t.elim, fun g => g.elim, [], [], none⟩
  eigner_nie_erzeugt := fun _ t => t.elim
  Inv := Empty
  traeger := fun i => i.elim
  invs := []
  Ax := Empty
  aparams := fun a => a.elim
  aerg := fun a => a.elim
  aschreibt := fun a => a.elim
  agschreibt := fun a => a.elim
  Reg := Empty
  rtyp := fun r => r.elim
  rklasse := fun r => r.elim
  spiegel := fun r => r.elim
  rzusage := fun r => r.elim
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => t.elim
  invarianten_gehalten := fun _ i => i.elim
  ggeteilt_bewacht := fun g => g.elim

/-- `forever { } return;` -/
def bR : Endblock bD (vertragVon bD ()) false (bD.params ()) (Signatur.anfang bD (bD.signatur ())) :=
  .cons (.forever () Expr.tru .nil) (.ret .empty (List.Perm.refl _))

def bP : Programm bD where
  invariante := fun i => i.elim
  requires := fun _ => Expr.tru
  ensures := fun _ => Expr.tru
  rumpf := fun _ => bR

def bS : Speicher bD := ⟨fun t => t.elim, fun g => g.elim⟩

def bInit : Faden → Σ f : bD.Fn, Env bD (bD.params f) := fun _ => ⟨(), .nil⟩

/-- The oracle answers nothing (there is nothing to answer). -/
def bO : Orakel bD := ⟨fun a => a.elim, fun r => r.elim, fun r => r.elim, fun g => g.elim, fun _ => none⟩

def bM0 : RufMaschineG bD := RufStartG bP bS bInit

/-- After `endeEntf`: the loop as a block. -/
def bM1 : RufMaschineG bD :=
  ⟨bM0.speicher, rufUpdateG bM0.faeden 0
    ⟨(bM0.faeden 0).stapel, ⟨(), .nil, (bM0.faeden 0).kopf.s0,
      ⟨false, [], [], .nil, .dann (.cons (.forever () Expr.tru .nil) .nil) (.ende (.ret .empty (List.Perm.refl _)))⟩⟩,
     (bM0.faeden 0).spur, (bM0.faeden 0).log⟩, bM0.lauf, bM0.start⟩

/-- After `dannForever` at budget `p`: the loop with `p` passes. -/
def bM2 (p : Nat) : RufMaschineG bD :=
  ⟨bM1.speicher, rufUpdateG bM1.faeden 0
    ⟨(bM1.faeden 0).stapel, ⟨(), .nil, (bM1.faeden 0).kopf.s0,
      ⟨false, [], [], .nil, .ewig () p Expr.tru .nil (.dann .nil (.ende (.ret .empty (List.Perm.refl _))))⟩⟩,
     (bM1.faeden 0).spur, (bM1.faeden 0).log⟩, bM1.lauf, bM1.start⟩

theorem bz_schritt1 (p : Nat) : RufSchrittG bP bO p bM0 0 bM1 :=
  RufSchrittG.endeEntf bM0 0 false [] [] [] (.forever () Expr.tru .nil) (.ret .empty (List.Perm.refl _)) .nil
    rfl rfl

theorem bz_schritt2 (p : Nat) : RufSchrittG bP bO p bM1 0 (bM2 p) :=
  RufSchrittG.dannForever bM1 0 false [] [] [] [] () Expr.tru .nil .nil (.ende (.ret .empty (List.Perm.refl _))) .nil
    rfl

/-- The machine with the spent budget is reached at budget `0`. -/
theorem bz_erreicht : RufErreichbarG bP bO 0 bM0 (bM2 0) :=
  .schritt _ _ 0 (.schritt _ _ 0 .start (bz_schritt1 0)) (bz_schritt2 0)

/-- **The premise of the leg is met**: thread `0` stands at a spent budget. -/
theorem bz_halt : Zielsatz.HaltBenannt bO 0 (bM2 0) .budget 0 :=
  ⟨false, [], [], .nil, _, rfl, trivial⟩

/-- The shifted machine is the machine with one pass left, and it is reached at budget `1`. -/
theorem bz_plus : (bM2 0).plus 1 = bM2 1 := by
  simp only [bM2, bM1, bM0, RufMaschineG.plus, rufUpdateG_plus]
  rfl

theorem bz_erreicht1 : RufErreichbarG bP bO 1 bM0 (bM2 1) := by
  have h := rufErreichbarG_plus 1 bz_erreicht
  rwa [show bM0.plus 1 = bM0 from rufStartG_plus 1 bP bS bInit, bz_plus] at h

/-- **One budget higher the thread steps on** (`ewigWeiter`). -/
theorem bz_weiter : ∃ M', RufSchrittG bP bO (0 + 1) ((bM2 0).plus 1) 0 M' := by
  rw [bz_plus]
  exact ⟨_, RufSchrittG.ewigWeiter (bM2 1) 0 false [] [] () 0 Expr.tru .nil _ .nil rfl _ rfl rfl [] rfl
    (fun _ h => nomatch h)⟩

end Gabbro.Grammatik.Zielsatz.BudgetZeuge
