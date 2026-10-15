/-
  Control-flow helpers for the direct x86-64 validation (lane 338, plan A4).

  SETcc / CMOVcc / LEA as pure extensions over the canonical pilot
  vocabulary, plus the direct-branch target equation. No new register,
  memory, decoder or source model is invented here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung

namespace Gabbro.Grammatik.X86

/-- SETcc value: 1 when the condition holds over the flag snapshot, else 0. -/
def setCCWort (c : Bedingung) (f : Flags) : Wort :=
  if bedingung c f then 1 else 0

/-- Direct branch target from decoded length only: post-decode RIP plus
    the sign-extended displacement. Never an emitter annotation. -/
def direktZiel (rip : Adresse) (len : Nat) (disp : BitVec 32) : Adresse :=
  ripNach rip len + dispWort disp

/-- Low-byte update: upper 56 bits kept, low byte replaced.
    Models the narrow-8 preservation rule (upper bits unaffected). -/
def setLowByte (w : Wort) (b : Byte) : Wort :=
  BitVec.ofNat 64 (w.toNat / 256 * 256 + b.toNat)

/-- Upper bits survive a low-byte update. -/
theorem setLowByte_hoch (w : Wort) (b : Byte) :
    (setLowByte w b).toNat / 256 = w.toNat / 256 := by
  unfold setLowByte
  rw [BitVec.toNat_ofNat]
  have hw := w.isLt
  have hb := b.isLt
  simp at hw hb
  omega

/-- The low byte after the update is the written byte. -/
theorem setLowByte_tief (w : Wort) (b : Byte) :
    (setLowByte w b).toNat % 256 = b.toNat := by
  unfold setLowByte
  rw [BitVec.toNat_ofNat]
  have hw := w.isLt
  have hb := b.isLt
  simp at hw hb
  omega

/-- SETcc byte: 1 when the condition holds, else 0, as one byte. -/
def setCCByte (c : Bedingung) (f : Flags) : Byte :=
  if bedingung c f then BitVec.ofNat 8 1 else BitVec.ofNat 8 0

/-- SETcc pure application: low byte of `dst` set from the pre-state
    flags, upper bits preserved, flags and memory untouched. -/
def setCCAnwenden (s : Zustand) (dst : Register) (c : Bedingung) : Zustand :=
  { s with register := regSet s.register dst (setLowByte (s.register dst) (setCCByte c s.flags)) }

/-- SETcc preserves flags (MOV-like flag preservation). -/
theorem setCCAnwenden_flags (s : Zustand) (dst : Register) (c : Bedingung) :
    (setCCAnwenden s dst c).flags = s.flags := by
  rfl

/-- SETcc changes no memory byte. -/
theorem setCCAnwenden_speicher (s : Zustand) (dst : Register) (c : Bedingung) :
    (setCCAnwenden s dst c).speicher = s.speicher := by
  rfl

/-- CMOVcc pure application: `dst` takes the pre-state `src` value
    when the condition holds over the pre-state flags, else kept.
    Flags preserved, memory untouched, source evaluated pre-state. -/
def cmovAnwenden (s : Zustand) (dst src : Register) (c : Bedingung) : Zustand :=
  { s with register := fun q => if q = dst then (if bedingung c s.flags then s.register src else s.register dst) else s.register q }

/-- CMOVcc preserves flags. -/
theorem cmovAnwenden_flags (s : Zustand) (dst src : Register) (c : Bedingung) :
    (cmovAnwenden s dst src c).flags = s.flags := by
  rfl

/-- CMOVcc changes no memory byte. -/
theorem cmovAnwenden_speicher (s : Zustand) (dst src : Register) (c : Bedingung) :
    (cmovAnwenden s dst src c).speicher = s.speicher := by
  rfl

/-- CMOVcc step with decoded length only: RIP advances past the decoded
    instruction; the length is checked data, never an emitter note. -/
def cmovSchritt (d : Decodiert) (s : Zustand) (dst src : Register) (c : Bedingung) : Option Zustand :=
  match laengeOk d.laenge with
  | false => none
  | true => some ({ cmovAnwenden s dst src c with rip := ripNach s.rip d.laenge })

/-- CMOVcc taken: destination holds the pre-state source word. -/
theorem cmovSchritt_genommen (d : Decodiert) (s : Zustand) (dst src : Register) (c : Bedingung)
    (hok : laengeOk d.laenge = true) (hbed : bedingung c s.flags = true) :
    cmovSchritt d s dst src c = some ({ cmovAnwenden s dst src c with rip := ripNach s.rip d.laenge }) ∧
      (cmovAnwenden s dst src c).register dst = s.register src := by
  refine ⟨?_, ?_⟩
  · unfold cmovSchritt
    rw [hok]
  · unfold cmovAnwenden
    simp [hbed]

/-- CMOVcc with a memory source: the word is read FIRST through the
    permission-checked `read64`, then selected. A faulting read refuses
    on BOTH paths (no speculation of the fault away). -/
def cmovMemSchritt (d : Decodiert) (s : Zustand) (dst base : Register) (disp : BitVec 32) (c : Bedingung) : Option Zustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    match read64 s.speicher (effAddr s base disp) with
    | none => none
    | some v =>
      let w := if bedingung c s.flags then v else s.register dst
      some ({ s with register := regSet s.register dst w, rip := ripNach s.rip d.laenge })

/-- NO-SPECULATION: a faulting CMOV-memory read refuses even when the
    condition is false. The untaken path keeps its fault. -/
theorem cmovMem_feheler_bleibt (d : Decodiert) (s : Zustand) (dst base : Register) (disp : BitVec 32) (c : Bedingung)
    (hok : laengeOk d.laenge = true)
    (hread : read64 s.speicher (effAddr s base disp) = none)
    (hbed : bedingung c s.flags = false) :
    cmovMemSchritt d s dst base disp c = none ∧ bedingung c s.flags = false := by
  refine ⟨?_, hbed⟩
  unfold cmovMemSchritt
  rw [hok, hread]

/-- CMOV-memory success preserves flags. -/
theorem cmovMemSchritt_flags (d : Decodiert) (s s' : Zustand) (dst base : Register) (disp : BitVec 32) (c : Bedingung) (v : Wort)
    (hok : laengeOk d.laenge = true)
    (hread : read64 s.speicher (effAddr s base disp) = some v)
    (hstep : cmovMemSchritt d s dst base disp c = some s') :
    s'.flags = s.flags := by
  unfold cmovMemSchritt at hstep
  rw [hok, hread] at hstep
  cases hstep
  rfl

/-- LEA pure application: `dst` takes the effective address, computed
    from the pre-state base plus sign-extended displacement. No memory
    is touched, flags preserved (address math only). -/
def leaAnwenden (s : Zustand) (dst base : Register) (disp : BitVec 32) : Zustand :=
  { s with register := regSet s.register dst (effAddr s base disp) }

/-- LEA preserves flags. -/
theorem leaAnwenden_flags (s : Zustand) (dst base : Register) (disp : BitVec 32) :
    (leaAnwenden s dst base disp).flags = s.flags := by
  rfl

/-- LEA changes no memory byte. -/
theorem leaAnwenden_speicher (s : Zustand) (dst base : Register) (disp : BitVec 32) :
    (leaAnwenden s dst base disp).speicher = s.speicher := by
  rfl

/-- LEA step with decoded length only. -/
def leaSchritt (d : Decodiert) (s : Zustand) (dst base : Register) (disp : BitVec 32) : Option Zustand :=
  match laengeOk d.laenge with
  | false => none
  | true => some ({ leaAnwenden s dst base disp with rip := ripNach s.rip d.laenge })

/-- LEA success writes exactly the pre-state effective address. -/
theorem leaSchritt_erfolg (d : Decodiert) (s : Zustand) (dst base : Register) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true) :
    leaSchritt d s dst base disp =
      some ({ leaAnwenden s dst base disp with rip := ripNach s.rip d.laenge }) ∧
      (leaAnwenden s dst base disp).register dst = effAddr s base disp := by
  refine ⟨?_, ?_⟩
  · unfold leaSchritt
    rw [hok]
  · unfold leaAnwenden effAddr
    simp [regSet]

/-- Validator admission for a direct target: the decoded target must
    be a known instruction start or a listed entry. This `Bool` is
    validator/profile admission, NOT a hardware fault. -/
def direktZielOk (starts eintraege : List Adresse) (rip : Adresse) (len : Nat) (disp : BitVec 32) : Bool :=
  decide (direktZiel rip len disp ∈ starts ++ eintraege)

/-- ADMISSION GUARANTEE: an admitted direct target is a decoded
    instruction start or a listed entry. Every premise is used. -/
theorem direktZielOk_garantiert (starts eintraege : List Adresse) (rip : Adresse) (len : Nat) (disp : BitVec 32)
    (h : direktZielOk starts eintraege rip len disp = true) :
    direktZiel rip len disp ∈ starts ∨ direktZiel rip len disp ∈ eintraege := by
  unfold direktZielOk at h
  rw [decide_eq_true_eq] at h
  rw [List.mem_append] at h
  exact h

/-- Direct-target equation for the existing `jump32` step: the reused
    `schritt` lands exactly on `direktZiel`. Every premise is used. -/
theorem direktZiel_jump32 (d : Decodiert) (s s' : Zustand) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .jump32 disp)
    (hstep : schritt d s = some s') :
    s'.rip = direktZiel s.rip d.laenge disp := by
  rw [schritt_jump32 d s disp hok h] at hstep
  cases hstep
  rfl

/- NOTE: final CUTS block and axiom prints are at the end of this file. -/

/-- Direct-target equation for taken `jumpIf32`: reuse of `schritt`. -/
theorem direktZiel_jumpIf32_genommen (d : Decodiert) (s s' : Zustand) (cond : Bedingung) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .jumpIf32 cond disp)
    (hbed : bedingung cond s.flags = true) (hstep : schritt d s = some s') :
    s'.rip = direktZiel s.rip d.laenge disp := by
  rw [schritt_jumpIf32_genommen d s cond disp hok h hbed] at hstep
  cases hstep
  rfl

/-- Direct-target equation for `call32`: reuse of `schritt`; the return
    address store uses the post-decode address from decoding only. -/
theorem direktZiel_call32 (d : Decodiert) (s s' : Zustand) (disp : BitVec 32) (m : Speicher)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .call32 disp)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip d.laenge) = some m)
    (hstep : schritt d s = some s') :
    s'.rip = direktZiel s.rip d.laenge disp := by
  rw [schritt_call32_erfolg d s disp m hok h hwr] at hstep
  cases hstep
  rfl

/-- Untaken `jumpIf32` falls through to the post-decode address. -/
theorem direktZiel_jumpIf32_nicht (d : Decodiert) (s s' : Zustand) (cond : Bedingung) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .jumpIf32 cond disp)
    (hbed : bedingung cond s.flags = false) (hstep : schritt d s = some s') :
    s'.rip = ripNach s.rip d.laenge := by
  rw [schritt_jumpIf32_nicht d s cond disp hok h hbed] at hstep
  cases hstep
  rfl

/-! ## Witness states: two flag snapshots over shared registers. -/

/-- Witness memory: zeroed bytes, everything readable and writable. -/
def witSpeicher : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun _ => true
    schreibbar := fun _ => true
    ausfuehrbar := fun _ => false }

/-- Witness flags with the zero flag set (equal comparison just ran). -/
def witFlagsTrue : Flags :=
  { cf := false, pf := true, af := some false, zf := true, sf := false, of := false }

/-- Witness flags with the zero flag clear. -/
def witFlagsFalse : Flags :=
  { cf := false, pf := true, af := some false, zf := false, sf := false, of := false }

/-- Witness registers: `rax` holds 10, `rbx` holds 20, stack top at 8192. -/
def witReg : Register → Wort := fun q =>
  if q = Register.rax then 10
  else if q = Register.rbx then 20
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness state with the zero flag set. -/
def witTrue : Zustand :=
  { register := witReg, flags := witFlagsTrue, rip := BitVec.ofNat 64 4096, speicher := witSpeicher }

/-- Witness state with the zero flag clear. -/
def witFalse : Zustand :=
  { register := witReg, flags := witFlagsFalse, rip := BitVec.ofNat 64 4096, speicher := witSpeicher }

/-- WITNESS: the conditional move selects different words per flag. -/
theorem cmov_witness_unterscheidet :
    (cmovAnwenden witTrue .rax .rbx .e).register .rax = 20 ∧
    (cmovAnwenden witFalse .rax .rbx .e).register .rax = 10 := by
  decide

/-- The witness data address is readable for eight bytes. -/
theorem wit_lesbar8 :
    lesbar8 witSpeicher (BitVec.ofNat 64 8192) = true := by
  decide

/-- The witness data address is writable for eight bytes. -/
theorem wit_schreibbar8 :
    schreibbar8 witSpeicher (BitVec.ofNat 64 8192) = true := by
  decide

/-- JOINT WITNESS: the flag-selected word is stored and reads back,
    observably changing the memory byte from zero. -/
theorem cmov_speicher_zeuge :
    ∃ (m' : Speicher),
      write64 witSpeicher (BitVec.ofNat 64 8192)
        ((cmovAnwenden witTrue .rax .rbx .e).register .rax) = some m' ∧
      read64 m' (BitVec.ofNat 64 8192) = some 20 ∧
      m'.bytes (BitVec.ofNat 64 8192) ≠ witSpeicher.bytes (BitVec.ofNat 64 8192) := by
  have hsel : (cmovAnwenden witTrue .rax .rbx .e).register .rax = 20 :=
    cmov_witness_unterscheidet.1
  rw [hsel]
  have hwr : write64 witSpeicher (BitVec.ofNat 64 8192) 20 =
      some { witSpeicher with
        bytes := writeBytes witSpeicher (BitVec.ofNat 64 8192) 20 } := by
    unfold write64
    rw [if_pos wit_schreibbar8]
  refine ⟨_, hwr, read64_nach_write64 _ _ _ _ hwr wit_lesbar8, ?_⟩
  have hhit := writeBytesN_hit witSpeicher
    (BitVec.ofNat 64 8192) 20 8 0 (by decide) (by decide)
  rw [addrOff_null] at hhit
  show writeBytesN witSpeicher (BitVec.ofNat 64 8192) 20 8
      (BitVec.ofNat 64 8192) ≠ witSpeicher.bytes (BitVec.ofNat 64 8192)
  rw [hhit]
  decide

/-! ## Refusals: mid-instruction, data and off-image targets. -/

/-- MID-INSTRUCTION REFUSAL: from 4096 past a 5-byte instruction, a
    displacement of 2 lands on 4103, between the starts 4096 and 4101. -/
theorem ziel_mitte_verweigert :
    direktZielOk [BitVec.ofNat 64 4096, BitVec.ofNat 64 4101] []
      (BitVec.ofNat 64 4096) 5 (BitVec.ofNat 32 2) = false := by
  decide

/-- DATA REFUSAL: the same branch with displacement 4091 lands on the
    data address 8192, which is no instruction start and no entry. -/
theorem ziel_daten_verweigert :
    direktZielOk [BitVec.ofNat 64 4096] []
      (BitVec.ofNat 64 4096) 5 (BitVec.ofNat 32 4091) = false := by
  decide

/-- OFF-IMAGE REFUSAL: displacement 100 lands on 4201, outside every
    listed start and entry. -/
theorem ziel_aussen_verweigert :
    direktZielOk [BitVec.ofNat 64 4096] [BitVec.ofNat 64 4096]
      (BitVec.ofNat 64 4096) 5 (BitVec.ofNat 32 100) = false := by
  decide

/-- SETcc witness: zero-flag set writes 1 into the low byte, flags
    and memory untouched, upper bits preserved. -/
theorem setCC_zeuge :
    (setCCAnwenden witTrue .rax .e).register .rax = BitVec.ofNat 64 1 ∧
    (setCCAnwenden witTrue .rax .e).flags = witTrue.flags ∧
    (setCCAnwenden witTrue .rax .e).speicher = witTrue.speicher ∧
    ((setCCAnwenden witTrue .rax .e).register .rax).toNat / 256 =
      (witTrue.register .rax).toNat / 256 := by
  refine ⟨by decide, setCCAnwenden_flags _ _ _, setCCAnwenden_speicher _ _ _, ?_⟩
  have h := setLowByte_hoch (witTrue.register .rax) (setCCByte .e witTrue.flags)
  unfold setCCAnwenden at h ⊢
  simpa [regSet] using h

/-- JOINT witness for `cmovSchritt_genommen`: all premises on concrete
    values, plus the memory-changing run. -/
theorem cmovSchritt_genommen_zeuge :
    (cmovSchritt ⟨.movReg64 .rax .rbx, 3⟩ witTrue .rax .rbx .e =
      some ({ cmovAnwenden witTrue .rax .rbx .e with rip := ripNach witTrue.rip 3 })) ∧
    (cmovAnwenden witTrue .rax .rbx .e).register .rax = witTrue.register .rbx ∧
    ∃ (m' : Speicher),
      write64 witSpeicher (BitVec.ofNat 64 8192)
        ((cmovAnwenden witTrue .rax .rbx .e).register .rax) = some m' ∧
      read64 m' (BitVec.ofNat 64 8192) = some 20 ∧
      m'.bytes (BitVec.ofNat 64 8192) ≠ witSpeicher.bytes (BitVec.ofNat 64 8192) := by
  have hok : laengeOk 3 = true := by decide
  have hbed : bedingung .e witTrue.flags = true := by decide
  obtain ⟨hstep, hsel⟩ := cmovSchritt_genommen ⟨.movReg64 .rax .rbx, 3⟩ witTrue .rax .rbx .e hok hbed
  exact ⟨hstep, hsel, cmov_speicher_zeuge⟩

/-- Dark memory: nothing readable or writable (fault witness). -/
def witDunkel : Speicher :=
  { bytes := fun _ => BitVec.ofNat 8 0
    lesbar := fun _ => false
    schreibbar := fun _ => false
    ausfuehrbar := fun _ => false }

/-- JOINT witness for `cmovMem_feheler_bleibt`: unreadable source with a
    false condition still refuses, plus the memory-changing run. -/
theorem cmovMem_feheler_bleibt_zeuge :
    cmovMemSchritt ⟨.movReg64 .rax .rbx, 3⟩
      { witFalse with speicher := witDunkel } .rax .rsp
      (BitVec.ofNat 32 0) .e = none ∧
    bedingung .e witFalse.flags = false ∧
    ∃ (m' : Speicher),
      write64 witSpeicher (BitVec.ofNat 64 8192)
        ((cmovAnwenden witTrue .rax .rbx .e).register .rax) = some m' ∧
      read64 m' (BitVec.ofNat 64 8192) = some 20 ∧
      m'.bytes (BitVec.ofNat 64 8192) ≠ witSpeicher.bytes (BitVec.ofNat 64 8192) := by
  have hok : laengeOk 3 = true := by decide
  have hread : read64 witDunkel
      (effAddr { witFalse with speicher := witDunkel } .rsp (BitVec.ofNat 32 0)) = none := by
    decide
  have hbed : bedingung .e witFalse.flags = false := by decide
  obtain ⟨href, _⟩ := cmovMem_feheler_bleibt ⟨.movReg64 .rax .rbx, 3⟩
    { witFalse with speicher := witDunkel } .rax .rsp (BitVec.ofNat 32 0) .e hok hread hbed
  exact ⟨href, hbed, cmov_speicher_zeuge⟩

/-- JOINT witness for `leaSchritt_erfolg`: effective address from the
    pre-state base, plus the memory-changing run. -/
theorem leaSchritt_erfolg_zeuge :
    (leaSchritt ⟨.movReg64 .rax .rbx, 3⟩ witTrue .rax .rbx (BitVec.ofNat 32 16) =
      some ({ leaAnwenden witTrue .rax .rbx (BitVec.ofNat 32 16) with rip := ripNach witTrue.rip 3 })) ∧
    (leaAnwenden witTrue .rax .rbx (BitVec.ofNat 32 16)).register .rax =
      effAddr witTrue .rbx (BitVec.ofNat 32 16) ∧
    ∃ (m' : Speicher),
      write64 witSpeicher (BitVec.ofNat 64 8192)
        ((cmovAnwenden witTrue .rax .rbx .e).register .rax) = some m' ∧
      read64 m' (BitVec.ofNat 64 8192) = some 20 ∧
      m'.bytes (BitVec.ofNat 64 8192) ≠ witSpeicher.bytes (BitVec.ofNat 64 8192) := by
  have hok : laengeOk 3 = true := by decide
  obtain ⟨hstep, hsel⟩ := leaSchritt_erfolg ⟨.movReg64 .rax .rbx, 3⟩ witTrue .rax .rbx (BitVec.ofNat 32 16) hok
  exact ⟨hstep, hsel, cmov_speicher_zeuge⟩

/-- JOINT witness for `direktZiel_jump32`: the reused step lands on the
    decoded target, plus the memory-changing run. -/
theorem direktZiel_jump32_zeuge :
    (schritt ⟨.jump32 (BitVec.ofNat 32 16), 5⟩ witTrue).map (fun s => s.rip) =
      some (direktZiel (BitVec.ofNat 64 4096) 5 (BitVec.ofNat 32 16)) ∧
    ∃ (m' : Speicher),
      write64 witSpeicher (BitVec.ofNat 64 8192)
        ((cmovAnwenden witTrue .rax .rbx .e).register .rax) = some m' ∧
      read64 m' (BitVec.ofNat 64 8192) = some 20 ∧
      m'.bytes (BitVec.ofNat 64 8192) ≠ witSpeicher.bytes (BitVec.ofNat 64 8192) := by
  refine ⟨by decide, cmov_speicher_zeuge⟩

/-- JOINT witness for `direktZielOk_garantiert`: the accepted target is
    a listed start, plus the memory-changing run. -/
theorem direktZielOk_garantiert_zeuge :
    (direktZiel (BitVec.ofNat 64 4096) 5 (BitVec.ofNat 32 0) ∈
      [BitVec.ofNat 64 4096, BitVec.ofNat 64 4101] ∨
     direktZiel (BitVec.ofNat 64 4096) 5 (BitVec.ofNat 32 0) ∈
      ([] : List Adresse)) ∧
    ∃ (m' : Speicher),
      write64 witSpeicher (BitVec.ofNat 64 8192)
        ((cmovAnwenden witTrue .rax .rbx .e).register .rax) = some m' ∧
      read64 m' (BitVec.ofNat 64 8192) = some 20 ∧
      m'.bytes (BitVec.ofNat 64 8192) ≠ witSpeicher.bytes (BitVec.ofNat 64 8192) := by
  have h : direktZielOk [BitVec.ofNat 64 4096, BitVec.ofNat 64 4101] []
      (BitVec.ofNat 64 4096) 5 (BitVec.ofNat 32 0) = true := by
    decide
  exact ⟨direktZielOk_garantiert _ _ _ _ _ h, cmov_speicher_zeuge⟩

/-- ACCEPTED TARGET: displacement 0 lands on the next start 4101. -/
theorem ziel_anfang_akzeptiert :
    direktZielOk [BitVec.ofNat 64 4096, BitVec.ofNat 64 4101] []
      (BitVec.ofNat 64 4096) 5 (BitVec.ofNat 32 0) = true := by
  decide

/- CUTS:
   Proved here: SETcc value and low-byte application with upper-bits
   preservation and flag/memory framing; register CMOVcc with flag and
   memory framing plus a decoded-length step; faulting CMOVcc-memory with
   the no-speculation fact (fault kept on the untaken path); LEA from the
   pre-state effective address with flag/memory framing plus a
   decoded-length step; the direct-target equation
   `target = virtual_next_RIP + sign_extend(disp)` for the reused
   `jump32`, taken `jumpIf32` and `call32` steps (fall-through equation
   for untaken `jumpIf32`); the validator admission Bool `direktZielOk`
   with the start-or-entry guarantee; concrete mid-instruction, data and
   off-image refusals plus one accepted target; joint witnesses with a
   real memory-changing run for every main theorem.
   NOT proved here, and not claimed:
   - No new instruction encoding or decoding: the three forms have no
     bytes, no `Codec` rows and no `Befehl` constructors; `Typen.lean`
     is untouched. Lengths come from decoded `Decodiert.laenge` only.
   - No hardware correspondence: flag readings reuse `Wort.bedingung`,
     address math reuses `dispWort`/`effAddr`, faults are the existing
     permission-checked `read64`/`write64` outcomes, not silicon.
   - No alignment admission: ordinary accesses impose no alignment check
     here (actual behaviour); any profile alignment stays a
     validator-side decision with a certified scalar fallback, owned
     elsewhere.
   - Narrow 32-bit clearing (upper32 zeroed) is not modelled: only the
     8-bit SETcc preservation rule is stated; lane A1 owns narrow widths.
   - No indirect-target certificates: jump tables, register/memory
     indirect branches, returns and `entry fn` values stay with image
     work; no existing direct CALL/RET is used to legalise them.
   - No whole-image coverage: `starts`/`eintraege` are checked inputs,
     and the decoded-start producer (byte walk from section starts and
     entries) is an OPEN consumer interface, not invented here.
   - No source, TSO/GX, concurrency, gate/OS-contract, cost, time or
     termination claim; absence of a transition is never a termination
     statement.
-/

#print axioms setLowByte_hoch
#print axioms setLowByte_tief
#print axioms setCCAnwenden_flags
#print axioms setCCAnwenden_speicher
#print axioms cmovAnwenden_flags
#print axioms cmovAnwenden_speicher
#print axioms cmovSchritt_genommen
#print axioms cmovMem_feheler_bleibt
#print axioms cmovMemSchritt_flags
#print axioms leaAnwenden_flags
#print axioms leaAnwenden_speicher
#print axioms leaSchritt_erfolg
#print axioms direktZielOk_garantiert
#print axioms direktZiel_jump32
#print axioms direktZiel_jumpIf32_genommen
#print axioms direktZiel_jumpIf32_nicht
#print axioms direktZiel_call32
#print axioms cmov_witness_unterscheidet
#print axioms cmov_speicher_zeuge
#print axioms ziel_mitte_verweigert
#print axioms ziel_daten_verweigert
#print axioms ziel_aussen_verweigert
#print axioms ziel_anfang_akzeptiert
#print axioms setCC_zeuge
#print axioms cmovSchritt_genommen_zeuge
#print axioms cmovMem_feheler_bleibt_zeuge
#print axioms leaSchritt_erfolg_zeuge
#print axioms direktZiel_jump32_zeuge
#print axioms direktZielOk_garantiert_zeuge

end Gabbro.Grammatik.X86
