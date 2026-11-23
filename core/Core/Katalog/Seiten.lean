module
public import Core.Katalog.Ziel

@[expose] public section

namespace Gabbro.Core.Katalog

/-- A half-open physical extent. Authority for the extent is carried separately by its grant. -/
structure Strecke where
  von : Nat
  bis : Nat
  deriving DecidableEq, Repr

def Strecke.drin (r : Strecke) (a : Nat) : Prop := r.von ≤ a ∧ a < r.bis

def Strecke.getrennt (r s : Strecke) : Prop := r.bis ≤ s.von ∨ s.bis ≤ r.von

theorem Strecke.getrennt_symm {r s : Strecke} (h : r.getrennt s) : s.getrennt r :=
  h.elim Or.inr Or.inl

def Strecke.enthaelt (r s : Strecke) : Prop := r.von ≤ s.von ∧ s.von < s.bis ∧ s.bis ≤ r.bis

def Strecke.seiten (z : ZielDaten) (r : Strecke) : Prop :=
  r.von < r.bis ∧ r.bis ≤ 2 ^ z.physicalBits ∧
  r.von % z.seitengranule = 0 ∧ r.bis % z.seitengranule = 0

/-- Installed reservation and committed RAM pages. Reservation alone creates no usable RAM. -/
structure Seitenbestand where
  reserviert : List Strecke
  anwesend : Nat → Bool

def Seitenbestand.leer : Seitenbestand := ⟨[], fun _ => false⟩

inductive SeitenEreignis where
  | hole (r : Strecke)
  | fuell (r : Strecke)
  | zurueck (r : Strecke)
  | gib (r : Strecke)
  deriving DecidableEq, Repr

def Seitenbestand.setAnwesend (s : Seitenbestand) (r : Strecke) (wert : Bool) : Nat → Bool :=
  fun a => if r.von ≤ a ∧ a < r.bis then wert else s.anwesend a

/-- The extent has aligned endpoints and a representable physical limit in the selected target row. -/
inductive SeitenSchritt (z : ZielDaten) : Seitenbestand → SeitenEreignis → Seitenbestand → Prop where
  | hole {s r} (gueltig : r.seiten z) (frisch : ∀ r' ∈ s.reserviert, r.getrennt r') :
      SeitenSchritt z s (.hole r) { s with reserviert := r :: s.reserviert }
  | fuell {s r parent} (gueltig : r.seiten z) (vorhanden : parent ∈ s.reserviert)
      (darin : parent.enthaelt r) :
      SeitenSchritt z s (.fuell r) { s with anwesend := s.setAnwesend r true }
  | zurueck {s r parent} (gueltig : r.seiten z) (vorhanden : parent ∈ s.reserviert)
      (darin : parent.enthaelt r) :
      SeitenSchritt z s (.zurueck r) { s with anwesend := s.setAnwesend r false }
  | gib {s r} (vorhanden : r ∈ s.reserviert) :
      SeitenSchritt z s (.gib r)
        ⟨s.reserviert.erase r, s.setAnwesend r false⟩

inductive SeitenLauf (z : ZielDaten) : Seitenbestand → List SeitenEreignis → Seitenbestand → Prop where
  | nil (s) : SeitenLauf z s [] s
  | cons {s t u e es} : SeitenSchritt z s e t → SeitenLauf z t es u → SeitenLauf z s (e :: es) u

def regionen (z : ZielDaten) (spur : List SeitenEreignis) : Prop :=
  ∃ s, SeitenLauf z Seitenbestand.leer spur s

theorem hole_ram_gleich {z s t r} (h : SeitenSchritt z s (.hole r) t) : t.anwesend = s.anwesend := by
  cases h with
  | hole => rfl

theorem ueberlapp_verweigert {z s t r r'} (vorhanden : r' ∈ s.reserviert)
    (ueberlappt : ¬ r.getrennt r') : ¬ SeitenSchritt z s (.hole r) t := by
  intro h
  cases h with
  | hole _ frisch => exact ueberlappt (frisch r' vorhanden)

theorem fuell_draussen_verweigert {z s t r}
    (outside : ∀ parent ∈ s.reserviert, ¬ parent.enthaelt r) :
    ¬ SeitenSchritt z s (.fuell r) t := by
  intro h
  cases h with
  | fuell _ held contained => exact outside _ held contained

inductive Speicherdienst where

  | read
  | write
  | execute
  deriving DecidableEq, Repr

/-- The decoded page table and the cache view of a core. The language owns shootdown and reuse. -/
structure Seiteneintrag where
  frame : Nat
  rights : List Speicherdienst
  generation : Nat
  deriving DecidableEq, Repr

structure MmuSicht where
  tables : Nat → Nat → Option Seiteneintrag
  tlb : Nat → Nat → Nat → Option Seiteneintrag

inductive MmuFehler where
  | address
  | absent
  | rights
  deriving DecidableEq, Repr

def ZielDaten.virtuell (z : ZielDaten) (addr : Nat) : Prop :=
  addr < 2 ^ (z.virtualBits - 1) ∨
    (2 ^ z.wbits - 2 ^ (z.virtualBits - 1) ≤ addr ∧ addr < 2 ^ z.wbits)

instance (z : ZielDaten) (addr : Nat) : Decidable (z.virtuell addr) :=
  inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

/-- Decode a translation from a local cached mapping or the installed table. A core may use a cached
    translation until the language's invalidation protocol removes it. -/
def uebersetze (z : ZielDaten) (s : MmuSicht) (core space addr : Nat) (right : Speicherdienst) :
    Except MmuFehler (Nat × Nat) :=
  if ¬ z.virtuell addr then .error .address
  else
    let page := addr / z.seitengranule
    match (s.tlb core space page).orElse (fun () => s.tables space page) with
    | none => .error .absent
    | some entry =>
      let phys := entry.frame * z.seitengranule + addr % z.seitengranule
      if phys ≥ 2 ^ z.physicalBits then .error .address
      else if right ∈ entry.rights then .ok (phys, entry.generation)
      else .error .rights

end Gabbro.Core.Katalog
