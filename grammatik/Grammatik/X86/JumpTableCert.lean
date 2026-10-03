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
import Grammatik.X86.HardwareFaults
import Grammatik.X86.TSO

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

/-! ## 4. The connection: a certified fetched table jump.

    A `jmpMem` fetched from actual executable bytes, whose effective
    address is an in-bounds table slot of a certified table, lands on a
    validator-tracked target: a decoded start or a listed entry, read
    (never forged) from the table. The step keeps flags, memory and all
    registers except RIP, observes no fault class, and runs through the
    accepted fetched byte step. The target read comes from the pre-state
    before control moves (inherited order of `jmpMemSchritt_erfolg`); the
    admission is DERIVED from the certificate, never assumed. -/

/-- CONNECTION: the certified fetched table jump lands tracked. -/
theorem JumpTableCert_verbindung
    (s s' : Zustand) (base : Register) (disp : BitVec 32) (len : Nat)
    (basis : Adresse) (idx n : Nat)
    (starts eintraege : List Adresse)
    (rest : List Byte) (ziel : Wort)
    (hzert : jtZertOk starts eintraege s.speicher basis n = true)
    (hidx : idx < n)
    (hslot : effAddr s base disp = tabSlot basis idx)
    (hfetch : fetchInd s (geholt s) = some ((.jmpMem base disp len), rest))
    (hrd : read64 s.speicher (effAddr s base disp) = some ziel)
    (hstep : jmpMemSchritt len s base disp = some s') :
    s'.rip = ziel ∧ s'.flags = s.flags ∧
    s'.speicher = s.speicher ∧
    (∀ q : Register, s'.register q = s.register q) ∧
    (ziel ∈ starts ∨ ziel ∈ eintraege) ∧
    leseKlasse s.speicher (effAddr s base disp) = none ∧
    indByteschritt s = some s' ∧
    jtGeschmiedetB s.speicher basis n ziel = false := by
  have hok := (fetchInd_erfolg s (geholt s) _ _ hfetch).2.2.1
  have htab : tabEintrag s.speicher basis idx = some ziel := by
    unfold tabEintrag
    rw [← hslot]
    exact hrd
  have hzul : indirektZielOk starts eintraege ziel = true :=
    jtZertOk_eintrag starts eintraege s.speicher basis n idx ziel
      hzert hidx htab
  have hform : jmpMemSchritt len s base disp = some ({ s with rip := ziel }) :=
    jmpMemSchritt_erfolg len s base disp ziel hok hrd
  have hgleich : s' = { s with rip := ziel } := by
    rw [hform] at hstep
    cases hstep
    rfl
  have hschritt : indSchritt (.jmpMem base disp len) s = some s' := by
    unfold indSchritt
    exact hstep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgleich]
  · rw [hgleich]
  · rw [hgleich]
  · intro q
    rw [hgleich]
  · exact indirektZielOk_garantiert starts eintraege ziel hzul
  · exact leseErfolg_kein_fehler s.speicher (effAddr s base disp) ziel hrd
  · exact indByteschritt_weiter s _ rest s' hfetch hschritt
  · exact jtEcht_nicht_geschmiedet s.speicher basis n idx ziel hidx htab

/-! ## 5. Faults, gates and TSO framing.

    Widths: every slot is one 8-byte word (`read64`); the stride is 8.
    Order: the target word is read from the pre-state before control
    moves (reused `jmpMemSchritt_erfolg` order). Permissions: the slot
    needs `lesbar8`, the code prefix `ausfuehrbarN` (via `fetchInd`).
    Faults are the accepted classes: a faulting slot read observes
    `#PF` (the pinned permitted member), never a validator verdict.
    Flags: the jump keeps every flag (defined and undefined alike make
    no claim beyond preservation). TSO: the jump is load-only, so the
    per-core store buffer is untouched and canonical memory is unchanged
    by construction. The full per-access target-to-W/GX simulation stays
    OPEN (see CUTS). -/

/-- TSO projection after the jump: memory follows the successor, the
    store buffer is untouched (the jump issues no store). -/
def jtTsoNach (t : TSOZustand) (s' : Zustand) : TSOZustand :=
  { t with mem := s'.speicher }

/-- STORE-BUFFER NEUTRALITY: the table jump keeps every pending buffer
    and changes no canonical memory. Every premise is used. -/
theorem jtSprung_tso_neutral (t : TSOZustand) (s s' : Zustand)
    (base : Register) (disp : BitVec 32) (len : Nat) (ziel : Wort)
    (hok : laengeOk len = true)
    (hrd : read64 s.speicher (effAddr s base disp) = some ziel)
    (hstep : jmpMemSchritt len s base disp = some s') :
    (jtTsoNach t s').puffer = t.puffer ∧ s'.speicher = s.speicher := by
  have hform : jmpMemSchritt len s base disp = some ({ s with rip := ziel }) :=
    jmpMemSchritt_erfolg len s base disp ziel hok hrd
  have hgleich : s' = { s with rip := ziel } := by
    rw [hform] at hstep
    cases hstep
    rfl
  exact ⟨rfl, by rw [hgleich]⟩

/-- A faulting slot read observes `#PF` (the pinned permitted member of
    `datenFehlerKlassen`). Every premise is used. -/
theorem jtLesefehler_pf (s : Zustand) (base : Register) (disp : BitVec 32)
    (hrd : read64 s.speicher (effAddr s base disp) = none) :
    leseKlasse s.speicher (effAddr s base disp) = some .pf := by
  simp [leseKlasse, hrd]

/-- NO-SPECULATION for the table slot: a faulting slot read admits no
    jump transition. Reuses the accepted refusal (as the fault catalogue
    does for CMOV), never restated. -/
theorem jtSprung_verweigert_ohne_leserecht (len : Nat) (s : Zustand)
    (base : Register) (disp : BitVec 32)
    (hok : laengeOk len = true)
    (hrd : read64 s.speicher (effAddr s base disp) = none) :
    jmpMemSchritt len s base disp = none :=
  jmpMemSchritt_verweigert len s base disp hok hrd

/-- An out-of-bounds index refuses the slot check. Every premise is used. -/
theorem jtIndex_ausserhalb_verweigert (s : Zustand) (base : Register)
    (disp : BitVec 32) (basis : Adresse) (idx n : Nat)
    (h : n ≤ idx) :
    jtSprungOk s base disp basis idx n = false := by
  have hlt : ¬ idx < n := by omega
  unfold jtSprungOk
  exact decide_eq_false (fun hc => hlt hc.2)

/-- Witness targets are canonical addresses (the profile gate). -/
theorem jtZiel_kanonisch_beispiel :
    istKanonisch (BitVec.ofNat 64 4200) = true ∧
    istKanonisch (BitVec.ofNat 64 4208) = true := by
  decide

/-- A noncanonical data reference faults as `#GP` (reused gate). -/
theorem jtZiel_nichtkanonisch_gate :
    adrKlasse (BitVec.ofNat 64 (2 ^ 47)) false = some .gp :=
  adrKlasse_daten_gp

/- CUTS:
   Proved here so far: provenance, slots, entry reads, the certificate
   with its entry projection, table words with membership, the
   forged-pointer check with genuine/forged facts, the bounded slot
   check, the connection theorem, TSO store-buffer neutrality, the slot
   fault class with its no-speculation refusal, the out-of-bounds index
   refusal and the canonical-address gate pins.
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
#print axioms JumpTableCert_verbindung
#print axioms jtSprung_tso_neutral
#print axioms jtLesefehler_pf
#print axioms jtSprung_verweigert_ohne_leserecht
#print axioms jtIndex_ausserhalb_verweigert
#print axioms jtZiel_kanonisch_beispiel
#print axioms jtZiel_nichtkanonisch_gate

end Gabbro.Grammatik.X86
