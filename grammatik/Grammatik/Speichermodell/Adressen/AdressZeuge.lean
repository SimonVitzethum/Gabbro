/-
  File:      Grammatik/Speichermodell/Adressen/AdressZeuge.lean
  Subject:   WITNESS OF THE LEG `speicherAdressen` (2026-10-22): one table `T` of two elements with one field.

  * (A) `t[1].x = 5;` -- one step of machine G changes the cell `(T, 1, x)` (`az_aendert`); under the layout `aL`
    (base 100, element 8 bytes, field 4 bytes at offset 0; `aL_ok`) its byte (0, 108) lies in the table's region, as the
    leg says (`az_bereich`).
  * (B) a foreign call whose oracle writes `T[7]` (`oB`) -- one step changes a cell OUTSIDE the declared extent
    (`ab_aussen`): the named assumption `ImBereichO` of the leg is not idle (`oB_nicht`), and a good oracle meets it
    (`oG_gut`).
-/
import Grammatik.Speichermodell.Adressen.Layout
import Grammatik.Kern.Syntax.Satz

namespace Gabbro.Grammatik.AdressZeuge

open Gabbro.Grammatik

/-- One table `T` (`count 2`, one field of type `0 .. 9`), two functions, one foreign body that may write `T`. -/
@[reducible] def aD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 9
  erlaubt := fun _ _ _ _ => true
  tabNr := fun _ => none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun g => g.elim
  nutzlast := fun g => g.elim
  atomar := fun g => g.elim
  geteilt := fun _ => false
  ggeteilt := fun g => g.elim
  Lock := Empty
  decLock := inferInstance
  rang := fun L => L.elim
  maskiert := fun L => L.elim
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => m.elim
  braucht := fun _ => []
  gbraucht := fun g => g.elim
  eigner := fun _ => []
  Fn := Bool
  sig := fun _ => 0
  sigNr := fun _ => ⟨[], none, 0, [], fun _ => true, fun g => g.elim, [], [], none⟩
  eigner_nie_erzeugt := fun _ _ _ _ h => nomatch h
  Inv := Empty
  traeger := fun i => i.elim
  invs := []
  Ax := Unit
  aparams := fun _ => []
  aerg := fun _ => none
  aschreibt := fun _ _ => true
  agschreibt := fun _ g => g.elim
  Reg := Empty
  rtyp := fun r => r.elim
  rklasse := fun r => r.elim
  spiegel := fun r => r.elim
  rzusage := fun r => r.elim
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ h => nomatch h
  invarianten_gehalten := fun _ i => i.elim
  ggeteilt_bewacht := fun g => g.elim

/-- `t[1].x = 5; return;` (function `true`) and `a(); return;` (function `false`). -/
def rA : Endblock aD (vertragVon aD true) false (aD.params true) (Signatur.anfang aD (aD.signatur true)) :=
  .cons (.assignSlot () () (.widen (by decide) (by decide) (.lit 1)) (.widen (by decide) (by decide) (.lit 5))
    rfl (fun _ h => nomatch h)) (.ret .empty (List.Perm.refl _))

def rB : Endblock aD (vertragVon aD false) false (aD.params false) (Signatur.anfang aD (aD.signatur false)) :=
  .cons (.axiomCall () .nil rfl (fun _ _ => rfl) (fun g => g.elim) (fun _ _ _ h => nomatch h) (fun g => g.elim))
    (.ret .empty (List.Perm.refl _))

def aP : Programm aD where
  invariante := fun i => i.elim
  requires := fun _ => Expr.tru
  ensures := fun _ => Expr.tru
  rumpf := fun b => match b with
    | true => rA
    | false => rB

def aS : Speicher aD := ⟨fun _ _ _ => ⟨0, by decide, by decide⟩, fun g => g.elim⟩

/-- A foreign body that writes nothing. -/
def oG : Orakel aD := ⟨fun _ σ _ => (σ, 0), fun r => r.elim, fun r => r.elim, fun g => g.elim, fun _ => none⟩

/-- A foreign body that writes `T[7]`, outside the declared extent `0 .. 1`. -/
def oB : Orakel aD :=
  ⟨fun _ σ _ => (σ.storeSlot () 7 () ⟨5, by decide, by decide⟩, 0), fun r => r.elim, fun r => r.elim,
    fun g => g.elim, fun _ => none⟩

theorem oG_gut : ImBereichO oG := fun _ _ _ _ _ _ _ => rfl

theorem oB_nicht : ¬ ImBereichO oB := by
  intro h
  have := h () (aS.welt []) .nil () 7 () (by simp [ImBereich])
  simp [oB, World.storeSlot] at this
  have := congrArg Zahl.n this
  simp [aS, Speicher.welt] at this

/-! ## (A) a write inside the extent -/

def aM0 : RufMaschineG aD := RufStartG aP aS (fun _ => ⟨true, .nil⟩)

theorem az_schritt : ∃ M1, RufSchrittG aP oG 0 aM0 0 M1 ∧ (M1.speicher.slots () 1 ()).n = 5 := by
  refine ⟨_, RufSchrittG.blatt aM0 0 false [] [] [] _ (.ret .empty (List.Perm.refl _)) .nil rfl rfl
    (fun _ h => nomatch h) _ _ [Ereignis.zugriff () true [] (offen (aM0.faeden 0).spur)] rfl rfl
    (by simp), ?_⟩
  rfl

/-- The cell `(T, 1, x)` changed, from `0` to `5`. -/
theorem az_aendert : ∃ M1, RufErreichbarGX aP oG 0 (fun _ => False) aM0 M1 ∧
    M1.speicher.slots () 1 () ≠ aM0.speicher.slots () 1 () := by
  obtain ⟨M1, hs, h5⟩ := az_schritt
  refine ⟨M1, gx_aus_g_lauf (.schritt _ _ 0 .start hs), fun e => ?_⟩
  rw [e] at h5
  exact absurd h5 (by decide)

/-- The layout: table in space 0 at 100, elements of 8 bytes, the field 4 bytes at offset 0. -/
def aL : AdressLayout aD := ⟨fun _ => 0, fun _ => 100, fun _ => 8, fun _ _ => 0, fun _ _ => 4, fun g => g.elim, fun g => g.elim⟩

theorem aL_ok : LayoutOk aL where
  geschlossen := fun _ _ => rfl
  offen := fun _ h => by simp at h
  feld := fun _ _ => by simp [aL]
  felder := fun _ _ _ h => absurd rfl h
  tabellen := fun _ _ _ h => absurd rfl h
  tabGlob := fun _ g => g.elim
  globale := fun g => g.elim

/-- **The leg on (A)**: the changed cell is in its extent, and its byte 108 lies in the region of `T`. -/
theorem az_bereich : ∃ M1, RufErreichbarGX aP oG 0 (fun _ => False) aM0 M1 ∧
    M1.speicher.slots () 1 () ≠ aM0.speicher.slots () 1 () ∧ ImBereich aD () 1 ∧ aL.inZelle () 1 () (0, 108) ∧
    aL.inTabelle () (0, 108) := by
  obtain ⟨M1, hr, hne⟩ := az_aendert
  have h := geaendert_im_bereich (rufErreichbarGX_aussen (fun _ h => h) oG_gut hr) aL_ok hne
  have hz : aL.inZelle () 1 () (0, 108) := by
    simp [AdressLayout.inZelle, AdressLayout.adresse, aL]
  exact ⟨M1, hr, hne, h.1, hz, h.2 (0, 108) hz⟩

/-! ## (B) a foreign write outside the extent -/

def bM0 : RufMaschineG aD := RufStartG aP aS (fun _ => ⟨false, .nil⟩)

/-- **Without `ImBereichO` the conclusion fails**: one step changes the cell `(T, 7, x)`, outside the extent. -/
theorem ab_aussen : ∃ M1, RufErreichbarGX aP oB 0 (fun _ => False) bM0 M1 ∧ ¬ ImBereich aD () 7 ∧
    M1.speicher.slots () 7 () ≠ bM0.speicher.slots () 7 () := by
  refine ⟨_, gx_aus_g_lauf (.schritt _ _ 0 .start (RufSchrittG.blatt bM0 0 false [] [] [] _
    (.ret .empty (List.Perm.refl _)) .nil rfl rfl (fun _ h => nomatch h) _ _ [] rfl rfl (by simp))),
    by simp [ImBereich], ?_⟩
  intro e
  have := congrArg Zahl.n e
  revert this
  decide

end Gabbro.Grammatik.AdressZeuge
