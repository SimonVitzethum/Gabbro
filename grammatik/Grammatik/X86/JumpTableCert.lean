/-
  File:      Grammatik/X86/JumpTableCert.lean
  Subject:   Jump-table certificates for indirect JMP through validated tables.

  Lane 769 (hardware completion): an indirect `JMP r/m64` (`FF /4`) whose
  target word is read from a validator-tracked jump table. Every table entry
  is a decoded instruction start or a listed entry, the target is never a
  forged number (M140 shape), and the admitted bytes execute through the
  accepted fetched step. See CUTS for scope.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.IndirectControlHardwareForms

namespace Gabbro.Grammatik.X86

/-- Manual provenance for every form claimed here. -/
def jtHandbuch : String :=
  "Intel SDM 325462-093US Vol.2A Ch.3 JMP (FF /4 JMP r/m64, p.3-504); " ++
  "Vol.1 s.3.3.7.1 canonical addressing. Local snapshot " ++
  ".tmp/HARDWARE-REFERENCES (intel-instruction-reference.txt)."

/-- Slot address of entry `i`: base plus eight bytes per entry. -/
def tabSlot (basis : Adresse) (i : Nat) : Adresse :=
  basis + BitVec.ofNat 64 (8 * i)

/-- Table entry read: the 8-byte word at the slot, if readable. -/
def tabEintrag (speicher : Speicher) (basis : Adresse) (i : Nat) :
    Option Wort :=
  read64 speicher (tabSlot basis i)

/-! ## 1. Validator-tracked target set and certificate.

    `starts` are decoded instruction starts, `eintraege` listed entries
    (the `Bild.eintraege` vector at the validator). The certificate is the
    reused admission `indirektZielOk` at EVERY table slot: a certified
    table jumps only to starts-or-entries. Lengths are checked data. -/

/-- Certificate: every entry word of the `n`-slot table is an admitted
    target (decoded start or listed entry); an unreadable slot refuses. -/
def jtZertOk (starts eintraege : List Adresse) (speicher : Speicher)
    (basis : Adresse) (n : Nat) : Bool :=
  (List.range n).all fun i => match tabEintrag speicher basis i with
    | some z => indirektZielOk starts eintraege z
    | none => false

/-- CERTIFICATE PROJECTION: an admitted entry of a certified table is an
    admitted target. Every premise is used. -/
theorem jtZertOk_eintrag (starts eintraege : List Adresse)
    (speicher : Speicher) (basis : Adresse) (n idx : Nat) (z : Wort)
    (hzert : jtZertOk starts eintraege speicher basis n = true)
    (hidx : idx < n)
    (hrd : tabEintrag speicher basis idx = some z) :
    indirektZielOk starts eintraege z = true := by
  have hall := (List.all_eq_true.mp hzert) idx (List.mem_range.mpr hidx)
  simp only [hrd] at hall
  exact hall

/-- The table words: successfully read entry words below `n`. -/
def tabWorte (speicher : Speicher) (basis : Adresse) (n : Nat) : List Wort :=
  (List.range n).filterMap (tabEintrag speicher basis)

/-- A read entry word is among the table words. Every premise is used. -/
theorem tabWorte_enthaelt (speicher : Speicher) (basis : Adresse)
    (n idx : Nat) (z : Wort)
    (hidx : idx < n)
    (hrd : tabEintrag speicher basis idx = some z) :
    z ∈ tabWorte speicher basis n := by
  unfold tabWorte
  rw [List.mem_filterMap]
  exact ⟨idx, List.mem_range.mpr hidx, hrd⟩

/-! ## 2. No forged pointer (M140 shape).

    The jump target must be a word READ from the table, never a bare
    number cast into a pointer. `jtGeschmiedetB` refuses (`true`) exactly
    the targets no table slot reads back: the mirror of
    `GateStub.m140VerweigertB` (a number where a pointer is expected). -/

/-- FORGED-POINTER CHECK: `true` means forged (no slot reads this word). -/
def jtGeschmiedetB (speicher : Speicher) (basis : Adresse) (n : Nat)
    (ziel : Wort) : Bool :=
  !decide (ziel ∈ tabWorte speicher basis n)

/-- A table-read word is never forged. Every premise is used. -/
theorem jtEcht_nicht_geschmiedet (speicher : Speicher) (basis : Adresse)
    (n idx : Nat) (ziel : Wort)
    (hidx : idx < n)
    (hrd : tabEintrag speicher basis idx = some ziel) :
    jtGeschmiedetB speicher basis n ziel = false := by
  have hmem := tabWorte_enthaelt speicher basis n idx ziel hidx hrd
  simp [jtGeschmiedetB, hmem]

/-- A word no slot reads IS forged and refused. Every premise is used. -/
theorem jtGeschmiedet_verweigert (speicher : Speicher) (basis : Adresse)
    (n : Nat) (ziel : Wort)
    (h : ziel ∉ tabWorte speicher basis n) :
    jtGeschmiedetB speicher basis n ziel = true := by
  simp [jtGeschmiedetB, h]

/-! ## 3. Bounded-index slot equation.

    The `jmpMem` effective address must BE a table slot for an in-bounds
    index: the index is checked data, never an unchecked offset. -/

/-- Bounded slot check: the effective address is slot `idx` below `n`. -/
def jtSprungOk (s : Zustand) (base : Register) (disp : BitVec 32)
    (basis : Adresse) (idx n : Nat) : Bool :=
  decide (effAddr s base disp = tabSlot basis idx ∧ idx < n)

/-- The check carries the slot equation and the bound. -/
theorem jtSprungOk_slot (s : Zustand) (base : Register) (disp : BitVec 32)
    (basis : Adresse) (idx n : Nat)
    (h : jtSprungOk s base disp basis idx n = true) :
    effAddr s base disp = tabSlot basis idx ∧ idx < n := by
  unfold jtSprungOk at h
  exact of_decide_eq_true h

/- CUTS:
   Proved here so far: provenance, slots, entry reads, the certificate
   with its entry projection, table words with membership, the
   forged-pointer check with genuine/forged facts, the bounded slot check.
   NOT proved here, and not claimed: everything else (see task).
-/

#print axioms jtHandbuch
#print axioms tabSlot
#print axioms tabEintrag
#print axioms jtZertOk_eintrag
#print axioms tabWorte_enthaelt
#print axioms jtEcht_nicht_geschmiedet
#print axioms jtGeschmiedet_verweigert
#print axioms jtSprungOk_slot

end Gabbro.Grammatik.X86
