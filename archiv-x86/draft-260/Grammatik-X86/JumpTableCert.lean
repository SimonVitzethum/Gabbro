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

/-! ## 6. Pinned bytes, common dispatch, explicit refusals.

    The table jump is the canonical `REX.W FF /4` mod=2 `rax`-based
    memory-indirect form (`Vol.2A 3-504`); its bytes execute through the
    accepted pilot-first adapter (`indAdapterDecode`), never a second
    decoder. Neighbours outside the profile (far `/3`, `mod=0`,
    the `E3` counter family) refuse by construction. -/

/-- PIN: the table-jump bytes through `rax+0` are
    `48 FF A0 00 00 00 00`. -/
theorem jtPin_bytes :
    encodeIndMem false .rax (BitVec.ofNat 32 0) =
      [natByte 72, natByte 255, natByte 160, natByte 0, natByte 0,
        natByte 0, natByte 0] := by
  decide

/-- PIN: the table-jump bytes dispatch through the common adapter to
    the memory-indirect jump form (pilot-first, no shadowing). -/
theorem jtAdapter_bytes (suffix : List Byte) :
    indAdapterDecode
      (encodeIndMem false .rax (BitVec.ofNat 32 0) ++ suffix) =
      some ((.indirekt (.jmpMem .rax (BitVec.ofNat 32 0)
        (if regLow .rax == 4 then 8 else 7))), suffix) :=
  indAdapter_indirekt _ _ _
    (pilot_verweigert_indMem false .rax _ _) (roundtrip_indMem_jmp .rax _ _)

/-- The pilot takes no table-jump bytes (disjoint dispatch). -/
theorem jtPilot_verweigert_tabellensprung (suffix : List Byte) :
    decode (encodeIndMem false .rax (BitVec.ofNat 32 0) ++ suffix) =
      none :=
  pilot_verweigert_indMem false .rax _ suffix

/-- NEIGHBOUR REFUSAL: the far-call extension `/3` is no table jump. -/
theorem jtNachbar_far_verweigert :
    decodeIndirekt [natByte 255, natByte 216] = none :=
  far_erweiterung_verweigert

/-- NEIGHBOUR REFUSAL: the non-canonical `mod=0` shape is no table jump. -/
theorem jtNachbar_modus0_verweigert :
    decodeIndirekt [natByte 255, natByte 16] = none :=
  modus0_verweigert

/-- NEIGHBOUR REFUSAL: the `E3` counter family is no table jump. -/
theorem jtNachbar_zaehler_verweigert :
    decodeIndirekt [natByte 227, natByte 5] = none :=
  zaehler_verweigert

/-- An unreadable first slot refuses the whole certificate. Every
    premise is used. -/
theorem jtZert_unlesbar_verweigert (starts eintraege : List Adresse)
    (speicher : Speicher) (basis : Adresse) (n : Nat)
    (h0 : 0 < n)
    (hlese : tabEintrag speicher basis 0 = none) :
    jtZertOk starts eintraege speicher basis n = false := by
  cases hcert : jtZertOk starts eintraege speicher basis n with
  | true =>
    have hall := (List.all_eq_true.mp hcert) 0 (List.mem_range.mpr h0)
    simp [hlese] at hall
  | false => rfl

/-- A table entry outside every start and entry refuses the whole
    certificate. Every premise is used. -/
theorem jtZert_fremdziel_verweigert (starts eintraege : List Adresse)
    (speicher : Speicher) (basis : Adresse) (n idx : Nat) (z : Wort)
    (hidx : idx < n)
    (hrd : tabEintrag speicher basis idx = some z)
    (hfremd : indirektZielOk starts eintraege z = false) :
    jtZertOk starts eintraege speicher basis n = false := by
  cases hcert : jtZertOk starts eintraege speicher basis n with
  | true =>
    have hz := jtZertOk_eintrag starts eintraege speicher basis n idx z
      hcert hidx hrd
    rw [hz] at hfremd
    cases hfremd
  | false => rfl

/-! ## 7. Reached witness machine.

    Closed concrete machine: `JMP [rax+0]` (`48 FF A0 00 00 00 00`,
    7 bytes) at 4096 with `rax = 8200`; the two-slot table at 8200
    holds `4200` and `4208` (both `ret` bytes, both executed-only
    starts); a separate data cell at 8300 is readable and writable.
    Code is execute-only, the table read-only, the data cell
    read/write: W^X throughout. -/

/-- Witness bytes: the jump encoding, the two table words
    (`4200 = 0x1068`, `4208 = 0x1070`, little-endian) and two `ret`. -/
def jtCodeBytes (a : Adresse) : Byte :=
  if a.toNat = 4096 then natByte 72
  else if a.toNat = 4097 then natByte 255
  else if a.toNat = 4098 then natByte 160
  else if a.toNat = 4099 then natByte 0
  else if a.toNat = 4100 then natByte 0
  else if a.toNat = 4101 then natByte 0
  else if a.toNat = 4102 then natByte 0
  else if a.toNat = 8200 then natByte 104
  else if a.toNat = 8201 then natByte 16
  else if a.toNat = 8208 then natByte 112
  else if a.toNat = 8209 then natByte 16
  else if a.toNat = 4200 then natByte 195
  else if a.toNat = 4208 then natByte 195
  else BitVec.ofNat 8 0

/-- Witness execute permission: the 7-byte jump window and the two
    one-byte targets. -/
def jtExec (a : Adresse) : Bool :=
  decide ((4096 ≤ a.toNat ∧ a.toNat < 4103) ∨
    a.toNat = 4200 ∨ a.toNat = 4208)

/-- Witness read permission: the 16-byte table and the data cell. -/
def jtLesbar (a : Adresse) : Bool :=
  decide ((8200 ≤ a.toNat ∧ a.toNat < 8216) ∨
    (8300 ≤ a.toNat ∧ a.toNat < 8308))

/-- Witness write permission: the data cell only (W^X elsewhere). -/
def jtSchreibbar (a : Adresse) : Bool :=
  decide (8300 ≤ a.toNat ∧ a.toNat < 8308)

/-- Witness memory: code execute-only, table read-only, data cell
    read/write. -/
def jtSpeicher : Speicher :=
  { bytes := jtCodeBytes
    lesbar := jtLesbar
    schreibbar := jtSchreibbar
    ausfuehrbar := jtExec }

/-- Witness registers: table base in `rax`, stack top at 9000. -/
def jtReg : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 8200
  else if q = Register.rsp then BitVec.ofNat 64 9000
  else BitVec.ofNat 64 0

/-- Witness start: table jump at 4096. -/
def jtS0 : Zustand :=
  { register := jtReg
    flags := zeugeFlags
    rip := BitVec.ofNat 64 4096
    speicher := jtSpeicher }

/-- Witness successor: control at the first table target. -/
def jtS1 : Zustand :=
  { jtS0 with rip := BitVec.ofNat 64 4200 }

/-- FETCH: the actual 7 bytes at 4096 are the canonical `JMP [rax+0]`
    with nothing after. -/
theorem jtS0_fetch :
    fetchInd jtS0 (geholt jtS0) =
      some (((.jmpMem .rax (BitVec.ofNat 32 0) 7)), []) := by
  decide

/-- The slot address is the table base: `rax + 0 = 8200`. -/
theorem jtS0_adresse :
    effAddr jtS0 .rax (BitVec.ofNat 32 0) =
      BitVec.ofNat 64 8200 := by
  decide

/-- The slot reads back the first target word `4200`. -/
theorem jtS0_liest :
    read64 jtS0.speicher (effAddr jtS0 .rax (BitVec.ofNat 32 0)) =
      some (BitVec.ofNat 64 4200) := by
  decide

/-- The slot equation: the effective address IS table slot 0. -/
theorem jtS0_slot :
    effAddr jtS0 .rax (BitVec.ofNat 32 0) =
      tabSlot (BitVec.ofNat 64 8200) 0 := by
  decide

/-- The two-slot table certifies against the two tracked starts. -/
theorem jtS0_zert :
    jtZertOk [BitVec.ofNat 64 4200, BitVec.ofNat 64 4208] []
      jtS0.speicher (BitVec.ofNat 64 8200) 2 = true := by
  decide

/-- FETCHED TABLE JUMP: from actual bytes, the byte step moves control
    to the table word. -/
theorem jtS0_schritt :
    jmpMemSchritt 7 jtS0 .rax (BitVec.ofNat 32 0) = some jtS1 := by
  have hok : laengeOk 7 = true := by decide
  have e := jmpMemSchritt_erfolg 7 jtS0 .rax (BitVec.ofNat 32 0)
    (BitVec.ofNat 64 4200) hok jtS0_liest
  unfold jtS1
  exact e

/-! ## 8. Joint companion witness.

    All premises of `JumpTableCert_verbindung` on joint concrete values
    (two-slot certified table, in-bounds slot 0, fetched `JMP [rax+0]`,
    target word `4200`), every conclusion conjunct through the fired
    connection, plus a memory-changing run on the separate data cell
    (zero to 42, read back): non-degenerate, reached, memory-changing. -/

/-- The data cell changes observably: zero to 42, read back. -/
theorem jtSpeicher_zeuge :
    ∃ (m' : Speicher),
      write64 jtSpeicher (BitVec.ofNat 64 8300) 42 = some m' ∧
      read64 m' (BitVec.ofNat 64 8300) = some 42 ∧
      jtSpeicher.bytes (BitVec.ofNat 64 8300) ≠
        m'.bytes (BitVec.ofNat 64 8300) := by
  have hsch : schreibbar8 jtSpeicher (BitVec.ofNat 64 8300) = true := by
    decide
  have hles : lesbar8 jtSpeicher (BitVec.ofNat 64 8300) = true := by
    decide
  have hwr : write64 jtSpeicher (BitVec.ofNat 64 8300) 42 =
      some { jtSpeicher with
        bytes := writeBytes jtSpeicher (BitVec.ofNat 64 8300) 42 } := by
    unfold write64
    rw [if_pos hsch]
  refine ⟨_, hwr, read64_nach_write64 _ _ _ _ hwr hles, ?_⟩
  have hhit := writeBytesN_hit jtSpeicher (BitVec.ofNat 64 8300) 42 8 0
    (by decide) (by decide)
  rw [addrOff_null] at hhit
  have hnull : jtSpeicher.bytes (BitVec.ofNat 64 8300) =
      BitVec.ofNat 8 0 := by
    decide
  show jtSpeicher.bytes (BitVec.ofNat 64 8300) ≠
    writeBytesN jtSpeicher (BitVec.ofNat 64 8300) 42 8
      (BitVec.ofNat 64 8300)
  rw [hnull, hhit]
  decide

/-- JOINT WITNESS for `JumpTableCert_verbindung`: every premise jointly
    on concrete values, every conclusion conjunct through the fired
    connection, and the memory-changing run beside the (load-only)
    jump. -/
theorem JumpTableCert_verbindung_zeuge :
    jtZertOk [BitVec.ofNat 64 4200, BitVec.ofNat 64 4208] []
        jtS0.speicher (BitVec.ofNat 64 8200) 2 = true ∧
    0 < 2 ∧
    effAddr jtS0 .rax (BitVec.ofNat 32 0) =
      tabSlot (BitVec.ofNat 64 8200) 0 ∧
    fetchInd jtS0 (geholt jtS0) =
      some (((.jmpMem .rax (BitVec.ofNat 32 0) 7)), []) ∧
    read64 jtS0.speicher (effAddr jtS0 .rax (BitVec.ofNat 32 0)) =
      some (BitVec.ofNat 64 4200) ∧
    jmpMemSchritt 7 jtS0 .rax (BitVec.ofNat 32 0) = some jtS1 ∧
    jtS1.rip = BitVec.ofNat 64 4200 ∧
    jtS1.flags = jtS0.flags ∧
    jtS1.speicher = jtS0.speicher ∧
    (∀ q : Register, jtS1.register q = jtS0.register q) ∧
    ((BitVec.ofNat 64 4200) ∈
      [BitVec.ofNat 64 4200, BitVec.ofNat 64 4208] ∨
      (BitVec.ofNat 64 4200) ∈ ([] : List Adresse)) ∧
    leseKlasse jtS0.speicher (effAddr jtS0 .rax (BitVec.ofNat 32 0)) =
      none ∧
    indByteschritt jtS0 = some jtS1 ∧
    jtGeschmiedetB jtS0.speicher (BitVec.ofNat 64 8200) 2
        (BitVec.ofNat 64 4200) = false ∧
    (∃ (m' : Speicher),
      write64 jtSpeicher (BitVec.ofNat 64 8300) 42 = some m' ∧
      read64 m' (BitVec.ofNat 64 8300) = some 42 ∧
      jtSpeicher.bytes (BitVec.ofNat 64 8300) ≠
        m'.bytes (BitVec.ofNat 64 8300)) := by
  have hconn := JumpTableCert_verbindung jtS0 jtS1 .rax
    (BitVec.ofNat 32 0) 7 (BitVec.ofNat 64 8200) 0 2
    [BitVec.ofNat 64 4200, BitVec.ofNat 64 4208] [] []
    (BitVec.ofNat 64 4200) jtS0_zert (by decide) jtS0_slot jtS0_fetch
    jtS0_liest jtS0_schritt
  exact ⟨jtS0_zert, by decide, jtS0_slot, jtS0_fetch, jtS0_liest,
    jtS0_schritt, hconn.1, hconn.2.1, hconn.2.2.1, hconn.2.2.2.1,
    hconn.2.2.2.2.1, hconn.2.2.2.2.2.1, hconn.2.2.2.2.2.2.1,
    hconn.2.2.2.2.2.2.2, jtSpeicher_zeuge⟩

/- CUTS:
   Proved here, over the REUSED canonical vocabulary (`Typen`,
   `Speicher.read64`/`write64`, `Ausfuehrung.effAddr`/`ripNach`,
   `Byteschritt.geholt`/`ausfuehrbarN`, `Codec` bytes,
   `IndirectControlHardwareForms` (`decodeIndirekt`, `jmpMemSchritt`,
   `fetchInd`, `indByteschritt`, `indirektZielOk`, `indAdapterDecode`,
   `GateStub`-mirrored M140 shape), `HardwareFaults` (`leseKlasse`,
   `istKanonisch`, `adrKlasse`), `TSO.TSOZustand` and no new machine,
   no new decoder row, no new interpreter:
   - jump-table slots (`tabSlot`, stride 8) with permission-checked
     entry reads (`tabEintrag` over `read64`);
   - the validator-tracked certificate (`jtZertOk`: every slot word a
     decoded start or a listed entry) with the entry projection
     (`jtZertOk_eintrag`);
   - table words with membership (`tabWorte`, `tabWorte_enthaelt`);
   - the no-forged-pointer check (`jtGeschmiedetB`, the M140 mirror:
     genuine table words pass, foreign words refuse);
   - the bounded-index slot equation (`jtSprungOk`);
   - the CONNECTION (`JumpTableCert_verbindung`): a certified fetched
     `JMP [base+disp]` lands on a tracked target with flags/memory/
     registers kept (RIP only), no fault class, through the accepted
     fetched byte step, unforged -- admission DERIVED from the
     certificate, the target read ordered on the pre-state;
   - TSO store-buffer neutrality (load-only: no `issueByte`, canonical
     memory unchanged); slot fault class (`#PF` member) with the
     no-speculation refusal; out-of-bounds index refusal;
     canonical-address gate pins;
   - pinned canonical bytes (`48 FF A0 00 00 00 00`) with common-adapter
     dispatch and pilot separation; three neighbour refusals (far
     `/3`, `mod=0`, `E3`); certificate refusals (unreadable slot,
     foreign target);
   - the reached joint witness (`JumpTableCert_verbindung_zeuge`):
     every premise jointly on concrete values, every conclusion
     conjunct through the fired connection, plus a memory-changing
     run (data cell zero to 42, read back) beside the load-only jump.
   NOT proved here, and not claimed:
   - No hardware correspondence: encodings are the stated canonical
     subset with self-consistency only, not x86 truth; the quotient of
     `decodeExt` (unified dispatcher) admission for these bytes stays
     with the dispatcher owner -- no second dispatcher is invented
     here (`indAdapterDecode` is reused, pilot-first-disjoint).
   - No whole-image validation: `starts`/`eintraege` are checked inputs;
     the decoded-start producer (byte walk from section starts and
     entries) and patched-site re-decode stay OPEN with their owners.
   - No per-access target-to-W/GX simulation: per-byte TSO facts do not
     establish aligned whole-word atomicity; the bridge stays OPEN.
   - No source correspondence, no contract/cost/time/termination
     claim; absence of a transition is never a termination statement.
   - No fault delivery (IDT/stack/handler/error code): delivery stays
     with its lane; only the class observation is stated.
   - Only named silicon/device/timing behaviour is assumed (the cited
     SDM headings); everything else is checked data or refused.
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
#print axioms jtPin_bytes
#print axioms jtAdapter_bytes
#print axioms jtPilot_verweigert_tabellensprung
#print axioms jtNachbar_far_verweigert
#print axioms jtNachbar_modus0_verweigert
#print axioms jtNachbar_zaehler_verweigert
#print axioms jtZert_unlesbar_verweigert
#print axioms jtZert_fremdziel_verweigert
#print axioms jtS0_fetch
#print axioms jtS0_adresse
#print axioms jtS0_liest
#print axioms jtS0_slot
#print axioms jtS0_zert
#print axioms jtS0_schritt
#print axioms jtSpeicher_zeuge
#print axioms JumpTableCert_verbindung_zeuge

end Gabbro.Grammatik.X86
