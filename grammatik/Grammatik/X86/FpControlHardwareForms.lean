/-
  File:      Grammatik/X86/FpControlHardwareForms.lean
  Subject:   Byte-executed MXCSR control-word load/store (LDMXCSR/STMXCSR).

  Lane 682: exact selected legacy forms `NP 0F AE /2` (LDMXCSR m32) and
  `NP 0F AE /3` (STMXCSR m32) from fetched bytes, with actual FOUR-byte
  load/store effects (`read32`/`write32`), architectural reserved-bit
  checks, profile-gated DAZ/MASK behaviour and precise MXCSR/register/
  RIP/memory/fault results over the reused `FpZustand`. No change to
  `ScalarFloat`, entry profiles, or any source/checker/Spec file.

  Provenance (Intel SDM 325462-093US, September 2026, local snapshot
  `.tmp/HARDWARE-REFERENCES/`, sha256 verified 2026-10-02):
  - LDMXCSR `NP 0F AE /2`, `MXCSR := m32`, reset default `1F80H`,
    `#GP for an attempt to set reserved bits` (Vol. 2A 3-538/3-539).
  - STMXCSR `NP 0F AE /3`, `m32 := MXCSR`, reserved bits stored as `0s`
    (Vol. 2B 4-676).
  - MXCSR layout Vol. 1 Fig. 10-3 (§10.2.3): bits 0-5 sticky flags,
    bit 6 DAZ, bits 7-12 masks, bits 13-14 RC, bit 15 FTZ, bits 16-31
    reserved (`#GP` on nonzero write); DAZ without support `#GP`
    (§10.2.3.4); `MXCSR_MASK` from FXSAVE guides legal writes (§11.6.6).
-/
import Grammatik.X86.ScalarFloat
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.FeatureProfile

namespace Gabbro.Grammatik.X86

/-- MXCSR control forms: load the word from, or store it to, a 32-bit
    memory operand addressed base plus displacement. -/
inductive MxcsrBefehl where
  | ldmxcsr (base : Register) (disp : BitVec 32)
  | stmxcsr (base : Register) (disp : BitVec 32)
  deriving DecidableEq, Repr

/-- A decoded MXCSR form: the form, its consumed length (checked data),
    and whether a LOCK prefix preceded it (`gesperrt`, always refused). -/
structure MxcsrDec where
  befehl : MxcsrBefehl
  laenge : Nat
  gesperrt : Bool
  deriving DecidableEq, Repr

/-- MXCSR byte-step outcome: success carries the successor, `fehlerGP`
    is the hardware general-protection fault (reserved bits, DAZ
    without support, masked-out bits), `fehlerUD` the invalid-opcode
    fault (LOCK prefix, denied feature/control gates), `verweigert`
    an explicit validator/permission refusal (never a fault). -/
inductive MxcsrAusgang where
  | weiter : FpZustand → MxcsrAusgang
  | fehlerGP : MxcsrAusgang
  | fehlerUD : MxcsrAusgang
  | verweigert : MxcsrAusgang

/-! ## 1. Profile and control gates (named silicon data, not guesses).

  The architectural reserved bits (16-31) are unconditional: any nonzero
  write faults (Vol. 1 §10.2.3). DAZ availability and the writable-bit
  mask (`MXCSR_MASK` from FXSAVE, Vol. 1 §11.6.6) are PROFILE data: the
  two instances below are example profiles, and real silicon values
  come from the target, never from a universal constant. -/

/-- MXCSR hardware profile: the writable-bit mask and DAZ support.
    Actual silicon values come from `MXCSR_MASK` (FXSAVE) on the
    target; these instances are checked profile data. -/
structure MxcsrProfil where
  maske : MXCSR
  dazVerfuegbar : Bool
  deriving DecidableEq, Repr

/-- Modern profile: every low bit writable, DAZ available. -/
def mxcsrProfilModern : MxcsrProfil := ⟨0xFFFF, true⟩

/-- Legacy profile: bit 6 (DAZ) not writable, DAZ unavailable. -/
def mxcsrProfilAlt : MxcsrProfil := ⟨0xFFBF, false⟩

/-- Feature/control gates: silicon has SSE, CR0.EM is clear, CR0.TS is
    clear, CR4.OSFXSR is set (Type 5 class; Vol. 2A §2.5, Table 2-22).
    Silicon splits denial into #UD (EM/OSFXSR) and #NM (TS); this model
    merges them as one control fault (see CUTS). -/
structure MxcsrSteuerung where
  sse : Bool
  emAus : Bool
  tsFrei : Bool
  osFx : Bool
  deriving DecidableEq, Repr

/-- The open gate: SSE present, emulation off, no task switch, OS FX on. -/
def mxcsrSteuerungOffen : MxcsrSteuerung :=
  ⟨true, true, true, true⟩

/-- All four gates hold. -/
def mxcsrSteuerungOk (c : MxcsrSteuerung) : Bool :=
  c.sse && c.emAus && c.tsFrei && c.osFx

/-- A denied gate denies the conjunction. -/
theorem mxcsrSteuerungOk_verweigert (c : MxcsrSteuerung)
    (h : (c.sse && c.emAus && c.tsFrei && c.osFx) = false) :
    mxcsrSteuerungOk c = false := by
  unfold mxcsrSteuerungOk
  simp [h]

/-- The open gate holds. -/
theorem mxcsrSteuerungOffen_ok :
    mxcsrSteuerungOk mxcsrSteuerungOffen = true := rfl

/-! ## 2. Architectural load checks and the stored word.

  `MXCSR := m32` faults with #GP unless the reserved bits (16-31) are
  zero, DAZ (bit 6) is supported where set, and no masked-out bit is
  set. `m32 := MXCSR` stores reserved bits as `0s` (Vol. 2B 4-676). -/

/-- Reserved bits (16-31) are clear: the word fits 16 bits. -/
def mxcsrReserviertFrei (w : MXCSR) : Bool := decide (w.toNat < 65536)

/-- A nonzero reserved bit refuses. -/
theorem mxcsrReserviertFrei_verweigert (w : MXCSR)
    (h : 65536 ≤ w.toNat) : mxcsrReserviertFrei w = false := by
  unfold mxcsrReserviertFrei
  simp [Nat.not_lt.mpr h]

/-- The reset word has no reserved bit set. -/
theorem mxcsrReserviertFrei_reset :
    mxcsrReserviertFrei 0x1F80 = true := by decide

/-- Architectural load admission under a profile: reserved-zero AND
    (DAZ set only where supported) AND (no masked-out bit set). -/
def ldmxcsrArchOk (p : MxcsrProfil) (w : MXCSR) : Bool :=
  mxcsrReserviertFrei w &&
    (!mxcsrBit w 6 || p.dazVerfuegbar) &&
    ((w &&& ~~~p.maske) == 0)

/-- The reset word loads under every profile. -/
theorem ldmxcsrArchOk_reset (p : MxcsrProfil)
    (hm : ((0x1F80 : MXCSR) &&& ~~~p.maske) = 0) :
    ldmxcsrArchOk p 0x1F80 = true := by
  have h1 : mxcsrReserviertFrei (0x1F80 : MXCSR) = true :=
    mxcsrReserviertFrei_reset
  have hb : mxcsrBit (0x1F80 : MXCSR) 6 = false := by decide
  unfold ldmxcsrArchOk
  rw [h1, hb, Bool.not_false, Bool.true_or, Bool.true_and, Bool.true_and,
    hm, beq_self_eq_true]

/-- The reset word loads under the modern profile. -/
theorem ldmxcsrArchOk_reset_modern :
    ldmxcsrArchOk mxcsrProfilModern 0x1F80 = true := by decide

/-- A reserved-bit word faults under every profile. -/
theorem ldmxcsrArchOk_reserviert_verweigert (p : MxcsrProfil)
    (w : MXCSR) (h : 65536 ≤ w.toNat) :
    ldmxcsrArchOk p w = false := by
  unfold ldmxcsrArchOk
  rw [mxcsrReserviertFrei_verweigert w h]
  simp

/-- A DAZ word faults where DAZ is unavailable. -/
theorem ldmxcsrArchOk_daz_verweigert (w : MXCSR)
    (h6 : mxcsrBit w 6 = true) :
    ldmxcsrArchOk mxcsrProfilAlt w = false := by
  unfold ldmxcsrArchOk mxcsrProfilAlt
  simp [h6]

/-- A masked-out bit faults: bit 6 under the legacy mask. -/
theorem ldmxcsrArchOk_maske_verweigert :
    ldmxcsrArchOk mxcsrProfilAlt 0x1FC0 = false := by decide

/-- The FTZ word (bit 15) loads under the modern profile: it is
    architecturally legal although source-inadmissible. -/
theorem ldmxcsrArchOk_ftz_modern :
    ldmxcsrArchOk mxcsrProfilModern 0x9F80 = true := by decide

/-- The word STMXCSR stores: the control word with reserved bits zeroed
    (manual: reserved bits are stored as `0s`). -/
def mxcsrSpeicherWort (w : MXCSR) : Wort := BitVec.ofNat 64 (w.toNat % 65536)

/-- The stored word keeps the low 16 bits. -/
theorem mxcsrSpeicherWort_tief (w : MXCSR) :
    (mxcsrSpeicherWort w).toNat % 65536 = w.toNat % 65536 := by
  unfold mxcsrSpeicherWort
  rw [BitVec.toNat_ofNat]
  have hw := w.isLt
  omega

/-- Round trip: a stored and reloaded word is the word itself when its
    reserved bits are clear. -/
theorem mxcsrSpeicherWort_rundlauf (w : MXCSR)
    (h : mxcsrReserviertFrei w = true) :
    BitVec.ofNat 32 ((mxcsrSpeicherWort w).toNat % 4294967296) = w := by
  unfold mxcsrReserviertFrei at h
  simp only [decide_eq_true_eq] at h
  have h1 : w.toNat % 65536 = w.toNat := Nat.mod_eq_of_lt h
  have h2 : w.toNat % 4294967296 = w.toNat :=
    Nat.mod_eq_of_lt (by omega)
  have hinner : (BitVec.ofNat 64 (w.toNat % 65536)).toNat = w.toNat := by
    have h64 : (w.toNat % 65536) % 2 ^ 64 = w.toNat := by
      rw [h1]
      exact Nat.mod_eq_of_lt (by have hw := w.isLt; omega)
    calc (BitVec.ofNat 64 (w.toNat % 65536)).toNat
        = (w.toNat % 65536) % 2 ^ 64 := BitVec.toNat_ofNat _ _
      _ = w.toNat := h64
  have houter : ((BitVec.ofNat 64 (w.toNat % 65536)).toNat % 4294967296)
      % 2 ^ 32 = w.toNat := by
    rw [hinner, h2, Nat.mod_eq_of_lt w.isLt]
  unfold mxcsrSpeicherWort
  have hfin : (BitVec.ofNat 32
      ((BitVec.ofNat 64 (w.toNat % 65536)).toNat % 4294967296)).toNat
      = w.toNat := by
    rw [BitVec.toNat_ofNat]
    exact houter
  exact BitVec.eq_of_toNat_eq hfin

/-! ## 3. Step semantics: exact control/memory/RIP/fault results.

  Guard order is architectural: decode length, LOCK (#UD), feature and
  control gates (#UD), then the four-byte memory access (permission
  refusal), then the reserved/profile check on load (#GP). LDMXCSR
  installs the full word (`MXCSR := m32`, sticky flags included — no
  exception fires at load); STMXCSR stores it with reserved bits
  zeroed. Both preserve flags, GPRs, XMM and (load) memory; RIP
  advances past the decoded length. -/

/-- Single MXCSR step; outcomes distinguish the hardware faults #GP
    and #UD from validator/permission refusal. -/
def mxcsrSchritt (d : MxcsrDec) (t : FpZustand) (p : MxcsrProfil)
    (c : MxcsrSteuerung) : MxcsrAusgang :=
  match laengeOk d.laenge with
  | false => .verweigert
  | true =>
    match d.gesperrt with
    | true => .fehlerUD
    | false =>
      match mxcsrSteuerungOk c with
      | false => .fehlerUD
      | true =>
        let nach := ripNach t.kern.rip d.laenge
        match d.befehl with
        | .ldmxcsr base disp =>
          match read32 t.kern.speicher (effAddr t.kern base disp) with
          | none => .verweigert
          | some v =>
            let w : MXCSR :=
              BitVec.ofNat 32 (v.toNat % 4294967296)
            match ldmxcsrArchOk p w with
            | false => .fehlerGP
            | true => .weiter { t with kern := { t.kern with rip := nach }, fp := ⟨w⟩ }
        | .stmxcsr base disp =>
          match write32 t.kern.speicher (effAddr t.kern base disp)
              (mxcsrSpeicherWort t.fp.mxcsr) with
          | none => .verweigert
          | some m => .weiter { t with kern := { t.kern with speicher := m, rip := nach } }

/-- A bad decode length refuses every MXCSR form. -/
theorem mxcsrSchritt_laenge_verweigert (d : MxcsrDec) (t : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (h : laengeOk d.laenge = false) :
    mxcsrSchritt d t p c = .verweigert := by
  unfold mxcsrSchritt
  simp [h]

/-- A LOCK-prefixed form faults with #UD, whatever follows. -/
theorem mxcsrSchritt_gesperrt_ud (d : MxcsrDec) (t : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = true) :
    mxcsrSchritt d t p c = .fehlerUD := by
  unfold mxcsrSchritt
  simp [hok, h]

/-- A denied feature/control gate faults with #UD. -/
theorem mxcsrSchritt_tor_ud (d : MxcsrDec) (t : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = false) :
    mxcsrSchritt d t p c = .fehlerUD := by
  unfold mxcsrSchritt
  simp [hok, h, htor]

/-- LDMXCSR success: the four-byte word becomes the control word. -/
theorem mxcsrSchritt_ld_erfolg (d : MxcsrDec) (t : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (base : Register) (disp : BitVec 32) (v : Wort) (w : MXCSR)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = true)
    (hbef : d.befehl = .ldmxcsr base disp)
    (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hw : w = BitVec.ofNat 32 (v.toNat % 4294967296))
    (hok2 : ldmxcsrArchOk p w = true) :
    mxcsrSchritt d t p c = .weiter ({ t with kern := { t.kern with rip := ripNach t.kern.rip d.laenge }, fp := ⟨w⟩ }) := by
  unfold mxcsrSchritt
  simp only [hok, h, htor, hbef, hrd]
  rw [← hw, hok2]

/-- LDMXCSR architectural fault: a reserved/profile-refused word is #GP. -/
theorem mxcsrSchritt_ld_gp (d : MxcsrDec) (t : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (base : Register) (disp : BitVec 32) (v : Wort) (w : MXCSR)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = true)
    (hbef : d.befehl = .ldmxcsr base disp)
    (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hw : w = BitVec.ofNat 32 (v.toNat % 4294967296))
    (hok2 : ldmxcsrArchOk p w = false) :
    mxcsrSchritt d t p c = .fehlerGP := by
  unfold mxcsrSchritt
  simp only [hok, h, htor, hbef, hrd]
  rw [← hw, hok2]

/-- LDMXCSR permission refusal: a failed four-byte read is no fault. -/
theorem mxcsrSchritt_ld_verweigert (d : MxcsrDec) (t : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (base : Register) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = true)
    (hbef : d.befehl = .ldmxcsr base disp)
    (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = none) :
    mxcsrSchritt d t p c = .verweigert := by
  unfold mxcsrSchritt
  simp [hok, h, htor, hbef, hrd]

/-- STMXCSR success: exactly the four target bytes change. -/
theorem mxcsrSchritt_st_erfolg (d : MxcsrDec) (t : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (base : Register) (disp : BitVec 32) (m : Speicher)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = true)
    (hbef : d.befehl = .stmxcsr base disp)
    (hwr : write32 t.kern.speicher (effAddr t.kern base disp)
      (mxcsrSpeicherWort t.fp.mxcsr) = some m) :
    mxcsrSchritt d t p c = .weiter ({ t with kern := { t.kern with speicher := m, rip := ripNach t.kern.rip d.laenge } }) := by
  unfold mxcsrSchritt
  simp [hok, h, htor, hbef, hwr]

/-- STMXCSR permission refusal: a failed four-byte write is no fault. -/
theorem mxcsrSchritt_st_verweigert (d : MxcsrDec) (t : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (base : Register) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = true)
    (hbef : d.befehl = .stmxcsr base disp)
    (hwr : write32 t.kern.speicher (effAddr t.kern base disp)
      (mxcsrSpeicherWort t.fp.mxcsr) = none) :
    mxcsrSchritt d t p c = .verweigert := by
  unfold mxcsrSchritt
  simp [hok, h, htor, hbef, hwr]

/-! ## Step frames: what each success leaves alone.

  LDMXCSR changes only the control word and RIP; STMXCSR changes
  only four memory bytes and RIP. Flags, GPRs and XMM never move;
  permissions never change. Every premise is used. -/

/-- A successful load keeps the flags. -/
theorem mxcsrSchritt_ld_flags (d : MxcsrDec) (t t' : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (base : Register) (disp : BitVec 32) (v : Wort) (w : MXCSR)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = true)
    (hbef : d.befehl = .ldmxcsr base disp)
    (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hw : w = BitVec.ofNat 32 (v.toNat % 4294967296))
    (hok2 : ldmxcsrArchOk p w = true)
    (hstep : mxcsrSchritt d t p c = .weiter t') :
    t'.kern.flags = t.kern.flags := by
  rw [mxcsrSchritt_ld_erfolg d t p c base disp v w hok h htor hbef hrd hw
    hok2] at hstep
  cases hstep
  rfl

/-- A successful load changes no memory byte. -/
theorem mxcsrSchritt_ld_speicher (d : MxcsrDec) (t t' : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (base : Register) (disp : BitVec 32) (v : Wort) (w : MXCSR)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = true)
    (hbef : d.befehl = .ldmxcsr base disp)
    (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hw : w = BitVec.ofNat 32 (v.toNat % 4294967296))
    (hok2 : ldmxcsrArchOk p w = true)
    (hstep : mxcsrSchritt d t p c = .weiter t') :
    t'.kern.speicher = t.kern.speicher := by
  rw [mxcsrSchritt_ld_erfolg d t p c base disp v w hok h htor hbef hrd hw
    hok2] at hstep
  cases hstep
  rfl

/-- A successful load keeps every GPR. -/
theorem mxcsrSchritt_ld_gpr (d : MxcsrDec) (t t' : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (base : Register) (disp : BitVec 32) (v : Wort) (w : MXCSR)
    (q : Register)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = true)
    (hbef : d.befehl = .ldmxcsr base disp)
    (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hw : w = BitVec.ofNat 32 (v.toNat % 4294967296))
    (hok2 : ldmxcsrArchOk p w = true)
    (hstep : mxcsrSchritt d t p c = .weiter t') :
    t'.kern.register q = t.kern.register q := by
  rw [mxcsrSchritt_ld_erfolg d t p c base disp v w hok h htor hbef hrd hw
    hok2] at hstep
  cases hstep
  rfl

/-- A successful load changes no XMM register. -/
theorem mxcsrSchritt_ld_xmm (d : MxcsrDec) (t t' : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (base : Register) (disp : BitVec 32) (v : Wort) (w : MXCSR)
    (q : XmmReg)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = true)
    (hbef : d.befehl = .ldmxcsr base disp)
    (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hw : w = BitVec.ofNat 32 (v.toNat % 4294967296))
    (hok2 : ldmxcsrArchOk p w = true)
    (hstep : mxcsrSchritt d t p c = .weiter t') :
    t'.xmm q = t.xmm q := by
  rw [mxcsrSchritt_ld_erfolg d t p c base disp v w hok h htor hbef hrd hw
    hok2] at hstep
  cases hstep
  rfl

/-- A successful load installs exactly the four-byte word. -/
theorem mxcsrSchritt_ld_wort (d : MxcsrDec) (t t' : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (base : Register) (disp : BitVec 32) (v : Wort) (w : MXCSR)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = true)
    (hbef : d.befehl = .ldmxcsr base disp)
    (hrd : read32 t.kern.speicher (effAddr t.kern base disp) = some v)
    (hw : w = BitVec.ofNat 32 (v.toNat % 4294967296))
    (hok2 : ldmxcsrArchOk p w = true)
    (hstep : mxcsrSchritt d t p c = .weiter t') :
    t'.fp.mxcsr = w := by
  rw [mxcsrSchritt_ld_erfolg d t p c base disp v w hok h htor hbef hrd hw
    hok2] at hstep
  cases hstep
  rfl

/-- A successful store keeps the control word. -/
theorem mxcsrSchritt_st_fp (d : MxcsrDec) (t t' : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (base : Register) (disp : BitVec 32) (m : Speicher)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = true)
    (hbef : d.befehl = .stmxcsr base disp)
    (hwr : write32 t.kern.speicher (effAddr t.kern base disp)
      (mxcsrSpeicherWort t.fp.mxcsr) = some m)
    (hstep : mxcsrSchritt d t p c = .weiter t') :
    t'.fp = t.fp := by
  rw [mxcsrSchritt_st_erfolg d t p c base disp m hok h htor hbef
    hwr] at hstep
  cases hstep
  rfl

/-- A successful store preserves the flags. -/
theorem mxcsrSchritt_st_flags (d : MxcsrDec) (t t' : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (base : Register) (disp : BitVec 32) (m : Speicher)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = true)
    (hbef : d.befehl = .stmxcsr base disp)
    (hwr : write32 t.kern.speicher (effAddr t.kern base disp)
      (mxcsrSpeicherWort t.fp.mxcsr) = some m)
    (hstep : mxcsrSchritt d t p c = .weiter t') :
    t'.kern.flags = t.kern.flags := by
  rw [mxcsrSchritt_st_erfolg d t p c base disp m hok h htor hbef
    hwr] at hstep
  cases hstep
  rfl

/-- A successful store changes nothing outside its four bytes. -/
theorem mxcsrSchritt_st_rahmen (d : MxcsrDec) (t t' : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (base : Register) (disp : BitVec 32) (m : Speicher) (x : Adresse)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = true)
    (hbef : d.befehl = .stmxcsr base disp)
    (hwr : write32 t.kern.speicher (effAddr t.kern base disp)
      (mxcsrSpeicherWort t.fp.mxcsr) = some m)
    (hstep : mxcsrSchritt d t p c = .weiter t')
    (hout : ∀ k : Nat, k < 4 → x ≠ addrOff (effAddr t.kern base disp) k) :
    t'.kern.speicher.bytes x = t.kern.speicher.bytes x := by
  rw [mxcsrSchritt_st_erfolg d t p c base disp m hok h htor hbef
    hwr] at hstep
  cases hstep
  exact write32_rahmen t.kern.speicher m (effAddr t.kern base disp) x _ hwr
    hout

/-- A successful store keeps every permission: only bytes change. -/
theorem mxcsrSchritt_st_berechtigungen (d : MxcsrDec) (t t' : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (base : Register) (disp : BitVec 32) (m : Speicher)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = true)
    (hbef : d.befehl = .stmxcsr base disp)
    (hwr : write32 t.kern.speicher (effAddr t.kern base disp)
      (mxcsrSpeicherWort t.fp.mxcsr) = some m)
    (hstep : mxcsrSchritt d t p c = .weiter t') :
    t'.kern.speicher.lesbar = t.kern.speicher.lesbar ∧
      t'.kern.speicher.schreibbar = t.kern.speicher.schreibbar ∧
      t'.kern.speicher.ausfuehrbar = t.kern.speicher.ausfuehrbar := by
  rw [mxcsrSchritt_st_erfolg d t p c base disp m hok h htor hbef
    hwr] at hstep
  cases hstep
  exact write32_erhaelt_berechtigungen t.kern.speicher
    (effAddr t.kern base disp) _ m hwr

/-- A successful store keeps every GPR. -/
theorem mxcsrSchritt_st_gpr (d : MxcsrDec) (t t' : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (base : Register) (disp : BitVec 32) (m : Speicher) (q : Register)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = true)
    (hbef : d.befehl = .stmxcsr base disp)
    (hwr : write32 t.kern.speicher (effAddr t.kern base disp)
      (mxcsrSpeicherWort t.fp.mxcsr) = some m)
    (hstep : mxcsrSchritt d t p c = .weiter t') :
    t'.kern.register q = t.kern.register q := by
  rw [mxcsrSchritt_st_erfolg d t p c base disp m hok h htor hbef
    hwr] at hstep
  cases hstep
  rfl

/-- A successful store changes no XMM register. -/
theorem mxcsrSchritt_st_xmm (d : MxcsrDec) (t t' : FpZustand)
    (p : MxcsrProfil) (c : MxcsrSteuerung)
    (base : Register) (disp : BitVec 32) (m : Speicher) (q : XmmReg)
    (hok : laengeOk d.laenge = true) (h : d.gesperrt = false)
    (htor : mxcsrSteuerungOk c = true)
    (hbef : d.befehl = .stmxcsr base disp)
    (hwr : write32 t.kern.speicher (effAddr t.kern base disp)
      (mxcsrSpeicherWort t.fp.mxcsr) = some m)
    (hstep : mxcsrSchritt d t p c = .weiter t') :
    t'.xmm q = t.xmm q := by
  rw [mxcsrSchritt_st_erfolg d t p c base disp m hok h htor hbef
    hwr] at hstep
  cases hstep
  rfl

/-! ## 4. Canonical bytes: `0F AE /2` and `0F AE /3` memory forms.

  Stated from the Intel SDM opcode map (`NP 0F AE /2` LDMXCSR m32,
  `NP 0F AE /3` STMXCSR m32; ModRM `/2` = reg field 2, `/3` = reg
  field 3; operand encoding M = memory only): two escape bytes, a
  ModRM with mod field 2 (base plus disp32, pilot SIB rule: SIB `0x24`
  iff the low base code is 4), and the disp32. An optional `F0` LOCK
  prefix decodes to a locked form that always faults (#UD on silicon).
  Register ModRM (mod 3), other reg fields, other prefixes (F2/F3/66/
  REX/VEX) and truncations refuse with `none`. -/

/-- Canonical LDMXCSR bytes: `0F AE /2`, mod 10, disp32. -/
def mxcsrEncodeLd (base : Register) (d : BitVec 32) : List Byte :=
  let head := [natByte 15, natByte 174, modrmMem 2 (regLow base)]
  if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
  else head ++ leBytes32 d

/-- Canonical STMXCSR bytes: `0F AE /3`, mod 10, disp32. -/
def mxcsrEncodeSt (base : Register) (d : BitVec 32) : List Byte :=
  let head := [natByte 15, natByte 174, modrmMem 3 (regLow base)]
  if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
  else head ++ leBytes32 d

/-- Decode after the `0F AE` escape: ModRM mod 2 with reg field 2 or 3
    and the disp32; SIB `0x24` where the pilot rule demands it. The
    `lock` flag records a preceding `F0` prefix. -/
def mxcsrDecodeRest (lock : Bool) : List Byte → Option (MxcsrDec × List Byte)
  | [] => none
  | m :: rest =>
    let reg := byteNat m / 8 % 8
    let rm := byteNat m % 8
    match byteNat m / 64 with
    | 2 =>
      if rm == 4 then
        match rest with
        | [] => none
        | sib :: rest2 =>
          if byteNat sib == 36 then
            match parseLe32 rest2 with
            | none => none
            | some (d, rest3) =>
              match reg, codeReg rm with
              | 2, some base => some (⟨.ldmxcsr base d, 8 + (if lock then 1 else 0), lock⟩, rest3)
              | 3, some base => some (⟨.stmxcsr base d, 8 + (if lock then 1 else 0), lock⟩, rest3)
              | _, _ => none
          else none
      else
        match parseLe32 rest with
        | none => none
        | some (d, rest3) =>
          match reg, codeReg rm with
          | 2, some base => some (⟨.ldmxcsr base d, 7 + (if lock then 1 else 0), lock⟩, rest3)
          | 3, some base => some (⟨.stmxcsr base d, 7 + (if lock then 1 else 0), lock⟩, rest3)
          | _, _ => none
    | _ => none

/-- Decode canonical MXCSR bytes, with an optional LOCK prefix. -/
def mxcsrDecode : List Byte → Option (MxcsrDec × List Byte)
  | [] => none
  | b :: rest =>
    if byteNat b == 240 then
      match rest with
      | b1 :: b2 :: rest2 =>
        if byteNat b1 == 15 && byteNat b2 == 174 then mxcsrDecodeRest true rest2
        else none
      | _ => none
    else if byteNat b == 15 then
      match rest with
      | b2 :: rest2 =>
        if byteNat b2 == 174 then mxcsrDecodeRest false rest2
        else none
      | _ => none
    else none

/-- The escape bytes are `0F AE`. -/
theorem mxcsrEscape_pin :
    natByte 15 = (0x0F : Byte) ∧ natByte 174 = (0xAE : Byte) := by
  decide

set_option maxHeartbeats 4000000 in
/-- Encode/decode round trip for LDMXCSR, both SIB shapes. -/
theorem mxcsrRoundtrip_ld (base : Register) (d : BitVec 32)
    (suffix : List Byte) (hb : regCode base < 8) :
    mxcsrDecode (mxcsrEncodeLd base d ++ suffix) =
      some (⟨.ldmxcsr base d, (mxcsrEncodeLd base d).length, false⟩,
        suffix) := by
  cases base <;>
    simp_all [mxcsrEncodeLd, mxcsrDecode, mxcsrDecodeRest, codeReg, regCode,
      regLow, modrmMem, leBytes32, parseLe32_cons]

set_option maxHeartbeats 4000000 in
/-- Encode/decode round trip for STMXCSR, both SIB shapes. -/
theorem mxcsrRoundtrip_st (base : Register) (d : BitVec 32)
    (suffix : List Byte) (hb : regCode base < 8) :
    mxcsrDecode (mxcsrEncodeSt base d ++ suffix) =
      some (⟨.stmxcsr base d, (mxcsrEncodeSt base d).length, false⟩,
        suffix) := by
  cases base <;>
    simp_all [mxcsrEncodeSt, mxcsrDecode, mxcsrDecodeRest, codeReg, regCode,
      regLow, modrmMem, leBytes32, parseLe32_cons]

/-- Encoder lengths: 7 bytes without SIB, 8 with SIB (both forms). -/
theorem mxcsrEncodeLd_len (base : Register) (d : BitVec 32) :
    (mxcsrEncodeLd base d).length = 7 ∨
      (mxcsrEncodeLd base d).length = 8 := by
  unfold mxcsrEncodeLd
  by_cases hb : regLow base == 4
  · simp [hb, length_leBytes32]
  · simp [hb, length_leBytes32]

/-- Encoder lengths: 7 bytes without SIB, 8 with SIB (both forms). -/
theorem mxcsrEncodeSt_len (base : Register) (d : BitVec 32) :
    (mxcsrEncodeSt base d).length = 7 ∨
      (mxcsrEncodeSt base d).length = 8 := by
  unfold mxcsrEncodeSt
  by_cases hb : regLow base == 4
  · simp [hb, length_leBytes32]
  · simp [hb, length_leBytes32]

/-- Pinned lengths: plain base 7 bytes, SIB base 8 bytes. -/
theorem mxcsrEncode_len_pin :
    (mxcsrEncodeLd .rax 0).length = 7 ∧
      (mxcsrEncodeLd .rsp 0).length = 8 ∧
      (mxcsrEncodeSt .rax 0).length = 7 ∧
      (mxcsrEncodeSt .rsp 0).length = 8 := by
  decide

/-- A LOCK-prefixed LDMXCSR decodes to a locked form (pinned bytes). -/
theorem mxcsrDecode_lockt_ld_pin :
    mxcsrDecode ([natByte 240] ++ mxcsrEncodeLd .rax 0) =
      some (⟨.ldmxcsr .rax 0, 8, true⟩, []) := by
  decide

/-- A LOCK-prefixed STMXCSR decodes to a locked form (pinned bytes). -/
theorem mxcsrDecode_lockt_st_pin :
    mxcsrDecode ([natByte 240] ++ mxcsrEncodeSt .rax 0) =
      some (⟨.stmxcsr .rax 0, 8, true⟩, []) := by
  decide

/-- A register ModRM (mod 3) is no memory form and refuses. -/
theorem mxcsrDecode_register_verweigert (suffix : List Byte) :
    mxcsrDecode (natByte 15 :: natByte 174 ::
      natByte 216 :: suffix) = none := by
  have h15 : byteNat (natByte 15) = 15 :=
    byteNat_natByte_of_lt 15 (by decide)
  have h174 : byteNat (natByte 174) = 174 :=
    byteNat_natByte_of_lt 174 (by decide)
  have h216 : byteNat (natByte 216) = 216 :=
    byteNat_natByte_of_lt 216 (by decide)
  simp [mxcsrDecode, mxcsrDecodeRest, h15, h174, h216]

/-- A wrong reg field (`/0`) refuses. -/
theorem mxcsrDecode_feldNull_verweigert (suffix : List Byte) :
    mxcsrDecode (natByte 15 :: natByte 174 ::
      natByte 128 :: suffix) = none := by
  have h15 : byteNat (natByte 15) = 15 :=
    byteNat_natByte_of_lt 15 (by decide)
  have h174 : byteNat (natByte 174) = 174 :=
    byteNat_natByte_of_lt 174 (by decide)
  have h128 : byteNat (natByte 128) = 128 :=
    byteNat_natByte_of_lt 128 (by decide)
  simp only [mxcsrDecode, mxcsrDecodeRest, h15, h174, h128]
  cases h : parseLe32 suffix <;> simp_all

/-- A wrong escape opcode refuses. -/
theorem mxcsrDecode_falscherOpcode_verweigert (suffix : List Byte) :
    mxcsrDecode (natByte 15 :: natByte 175 ::
      natByte 144 :: suffix) = none := by
  simp [mxcsrDecode]

/-- A truncated escape refuses. -/
theorem mxcsrDecode_abgeschnitten_verweigert :
    mxcsrDecode [natByte 15] = none ∧
      mxcsrDecode [natByte 15, natByte 174] = none ∧
      mxcsrDecode ((mxcsrEncodeLd .rax 0).take 6) = none := by
  refine ⟨by simp [mxcsrDecode], by decide, by decide⟩

/-- A lone LOCK prefix refuses. -/
theorem mxcsrDecode_lockAllein_verweigert :
    mxcsrDecode [natByte 240] = none := by
  simp [mxcsrDecode]

/-! ## 5. Fetch from actual executable memory and byte step.

  Fetch reads the bytes at the core RIP from the state's ACTUAL memory
  (executable prefix only, capped at 15, reusing `geholt`), decodes
  them with the independent §4 decoder, and checks consumed-length
  consistency, decode-length validity and execute permission before
  the decoded value reaches `mxcsrSchritt`. The profile and control
  gates travel as explicit parameters: a forged decoded value can
  never inject an instruction, and a forged word never becomes the
  control state without its architectural checks. -/

/-- The fetched window of an extended state: actual bytes at the core
    RIP, executable prefix only, capped at 15 (reuses `geholt`). -/
def mxcsrGeholt (t : FpZustand) : List Byte := geholt t.kern

/-- Fetch and decode: decode the ACTUAL fetched bytes with the
    independent decoder, then check consumed-length/remaining-suffix
    consistency, decode-length validity and execute permission of the
    consumed prefix. -/
def mxcsrFetchDekodiert (t : FpZustand) :
    Option (MxcsrDec × List Byte) :=
  match mxcsrDecode (mxcsrGeholt t) with
  | none => none
  | some (d, rest) =>
    if d.laenge + rest.length == (mxcsrGeholt t).length &&
        laengeOk d.laenge && ausfuehrbarN t.kern.speicher t.kern.rip d.laenge
    then some (d, rest)
    else none

/-- One byte step from actual memory: fetch, decode, then the
    §3 step under the given profile and control gates. -/
def mxcsrByteschritt (t : FpZustand) (p : MxcsrProfil)
    (c : MxcsrSteuerung) : MxcsrAusgang :=
  match mxcsrFetchDekodiert t with
  | none => .verweigert
  | some (d, _) =>
    mxcsrSchritt d t p c

/-- Fetch success pins the decoder equation and every guard. -/
theorem mxcsrFetchDekodiert_erfolg (t : FpZustand) (d : MxcsrDec)
    (rest : List Byte) (h : mxcsrFetchDekodiert t = some (d, rest)) :
    mxcsrDecode (mxcsrGeholt t) = some (d, rest) ∧
      d.laenge + rest.length = (mxcsrGeholt t).length ∧
      laengeOk d.laenge = true ∧
      ausfuehrbarN t.kern.speicher t.kern.rip d.laenge = true := by
  unfold mxcsrFetchDekodiert at h
  cases hd : mxcsrDecode (mxcsrGeholt t) with
  | none =>
    rw [hd] at h
    simp at h
  | some q =>
    obtain ⟨d', rest'⟩ := q
    rw [hd] at h
    simp only at h
    by_cases hc : (d'.laenge + rest'.length == (mxcsrGeholt t).length &&
        laengeOk d'.laenge && ausfuehrbarN t.kern.speicher t.kern.rip d'.laenge)
    · rw [if_pos hc] at h
      obtain ⟨rfl, rfl⟩ := Option.some_inj.mp h
      rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨rfl, hc.1.1, hc.1.2, hc.2⟩
    · rw [if_neg hc] at h
      simp at h

/-- A successful fetched byte-step runs the §3 step on the fetched
    form under the same profile and gates. -/
theorem mxcsrByteschritt_schritt (t : FpZustand) (p : MxcsrProfil)
    (c : MxcsrSteuerung) (t' : FpZustand) (d : MxcsrDec)
    (rest : List Byte)
    (hf : mxcsrFetchDekodiert t = some (d, rest))
    (hout : mxcsrByteschritt t p c = .weiter t') :
    mxcsrSchritt d t p c = .weiter t' := by
  unfold mxcsrByteschritt at hout
  rw [hf] at hout
  simp only at hout
  exact hout

/-- A fetched architectural fault is the §3 fault on the fetched form. -/
theorem mxcsrByteschritt_gp (t : FpZustand) (p : MxcsrProfil)
    (c : MxcsrSteuerung) (d : MxcsrDec) (rest : List Byte)
    (hf : mxcsrFetchDekodiert t = some (d, rest))
    (hs : mxcsrSchritt d t p c = .fehlerGP) :
    mxcsrByteschritt t p c = .fehlerGP := by
  unfold mxcsrByteschritt
  rw [hf]
  simp [hs]

/-- A fetched LOCK/control fault is the §3 fault on the fetched form. -/
theorem mxcsrByteschritt_ud (t : FpZustand) (p : MxcsrProfil)
    (c : MxcsrSteuerung) (d : MxcsrDec) (rest : List Byte)
    (hf : mxcsrFetchDekodiert t = some (d, rest))
    (hs : mxcsrSchritt d t p c = .fehlerUD) :
    mxcsrByteschritt t p c = .fehlerUD := by
  unfold mxcsrByteschritt
  rw [hf]
  simp [hs]

/-- Fetch refusal is byte-step refusal. -/
theorem mxcsrByteschritt_hol_verweigert (t : FpZustand) (p : MxcsrProfil)
    (c : MxcsrSteuerung) (hf : mxcsrFetchDekodiert t = none) :
    mxcsrByteschritt t p c = .verweigert := by
  unfold mxcsrByteschritt
  rw [hf]

/-! ## 6. Adapter for lanes 660/670/672/674.

  Exact input/output boundary for consumers (loaded-image execution,
  relocation follow-up, entry/duty connection, budget connection):
  input is the extended state plus the MXCSR profile and the control
  gates; output is `MxcsrAusgang` with its kind projector and the
  observation accessors below. No consumer needs the decoder or the
  step internals; every observation is read off the outcome. -/

/-- Outcome kind: 0 success, 1 #GP fault, 2 #UD fault, 3 refusal. -/
def mxcsrKind : MxcsrAusgang → Nat
  | .weiter _ => 0
  | .fehlerGP => 1
  | .fehlerUD => 2
  | .verweigert => 3

/-- The kind of a successful step. -/
theorem mxcsrKind_weiter (t' : FpZustand) :
    mxcsrKind (.weiter t') = 0 := rfl

/-- The kind of the reserved-bit fault. -/
theorem mxcsrKind_gp : mxcsrKind .fehlerGP = 1 := rfl

/-- The kind of the LOCK/control fault. -/
theorem mxcsrKind_ud : mxcsrKind .fehlerUD = 2 := rfl

/-- The kind of a refusal. -/
theorem mxcsrKind_verweigert : mxcsrKind .verweigert = 3 := rfl

/-- Successor memory out of an outcome (none unless success). -/
def mxcsrSpeicherNach : MxcsrAusgang → Option Speicher
  | .weiter t' => some t'.kern.speicher
  | _ => none

/-- Successor control word out of an outcome (none unless success). -/
def mxcsrWortNach : MxcsrAusgang → Option MXCSR
  | .weiter t' => some t'.fp.mxcsr
  | _ => none

/-- Successor RIP out of an outcome (none unless success). -/
def mxcsrRipNach : MxcsrAusgang → Option Adresse
  | .weiter t' => some t'.kern.rip
  | _ => none

/-- A fault carries no successor memory. -/
theorem mxcsrSpeicherNach_gp : mxcsrSpeicherNach .fehlerGP = none := rfl

/-- A fault carries no successor control word. -/
theorem mxcsrWortNach_gp : mxcsrWortNach .fehlerGP = none := rfl

/-- A refusal carries no successor control word. -/
theorem mxcsrWortNach_verweigert : mxcsrWortNach .verweigert = none := rfl

/-! ## 7. Witness image: a byte-executed save/load fragment.

  Code at `0x1000` holds `LDMXCSR [rax+0]` (7 bytes) followed by
  `STMXCSR [rax+4]` (7 bytes); `rax` points at the data cell `0x2000`,
  preloaded with `0x1FBF` (reset plus sticky flags: admitted, since
  the profile ignores sticky bits). The first fetched step installs
  a new control word (real control change); the second stores it at
  `0x2004` (real memory change) while the control word is preserved.
  Code is execute-only, data read/write-only. -/

/-- Witness code: load bytes followed by store bytes (14 bytes). -/
def mxcsrWitCode : List Byte :=
  mxcsrEncodeLd .rax 0 ++ mxcsrEncodeSt .rax 4

/-- Witness code with a LOCK prefix on the load (8 bytes). -/
def mxcsrWitCodeLock : List Byte :=
  [natByte 240] ++ mxcsrEncodeLd .rax 0

/-- Witness bytes: `code` at `0x1000`, the word `w` little-endian at
    `0x2000`, zeroes elsewhere. -/
def mxcsrWitBytes (code : List Byte) (w : Wort) (a : Adresse) : Byte :=
  if a.toNat - 4096 < code.length then code.getD (a.toNat - 4096) 0
  else if a.toNat - 8192 < 4 then wortByte w (a.toNat - 8192)
  else BitVec.ofNat 8 0

/-- Witness memory: data readable/writable, code execute-only. -/
def mxcsrWitSpeicher (code : List Byte) (w : Wort) : Speicher :=
  { bytes := mxcsrWitBytes code w, lesbar := fun a => decide (8192 ≤ a.toNat ∧ a.toNat < 8208), schreibbar := fun a => decide (8192 ≤ a.toNat ∧ a.toNat < 8208), ausfuehrbar := fun a => decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + code.length) }

/-- Witness registers: `rax` points at the data cell. -/
def mxcsrWitReg : Register → Wort := fun q =>
  if q = Register.rax then BitVec.ofNat 64 8192 else BitVec.ofNat 64 0

/-- Witness XMM file: all zero (control forms never touch XMM). -/
def mxcsrWitXmm : XmmDatei := fun _ => vecJoin 0 0

/-- Witness state: reset control word, RIP at the code. -/
def mxcsrWitT (code : List Byte) (w : Wort) : FpZustand :=
  ⟨{ register := mxcsrWitReg, flags := zeugeFlags, rip := BitVec.ofNat 64 4096, speicher := mxcsrWitSpeicher code w }, mxcsrWitXmm, kontextReset⟩

/-- The main witness: load/store code, `0x1FBF` preloaded. -/
def mxcsrWitHaupt : FpZustand :=
  mxcsrWitT mxcsrWitCode 0x1FBF

/-- The witness code is 14 bytes long. -/
theorem mxcsrWitCode_len : mxcsrWitCode.length = 14 := by
  unfold mxcsrWitCode
  have h1 : (mxcsrEncodeLd .rax 0).length = 7 :=
    Or.resolve_right (mxcsrEncodeLd_len .rax 0) (by decide)
  have h2 : (mxcsrEncodeSt .rax 4).length = 7 :=
    Or.resolve_right (mxcsrEncodeSt_len .rax 4) (by decide)
  rw [List.length_append, h1, h2]

/-- The fetch window holds exactly the witness code. -/
theorem mxcsrWit_geholt :
    mxcsrGeholt mxcsrWitHaupt =
      mxcsrEncodeLd .rax 0 ++ mxcsrEncodeSt .rax 4 := by
  decide

/-- Fetch from the actual load bytes yields the load form. -/
theorem mxcsrWit_fetch1 :
    mxcsrFetchDekodiert mxcsrWitHaupt =
      some (⟨.ldmxcsr .rax 0, 7, false⟩, mxcsrEncodeSt .rax 4) := by
  decide

/-- The preloaded word reads back through the real four-byte load. -/
theorem mxcsrWit_liest :
    read32 mxcsrWitHaupt.kern.speicher (BitVec.ofNat 64 8192) =
      some 0x1FBF := by
  decide

/-- The witness store address: `rax + 0` is `0x2000`. -/
theorem mxcsrWit_effAddr :
    effAddr mxcsrWitHaupt.kern Register.rax 0 =
      BitVec.ofNat 64 8192 := by
  decide

/-- State after the load: `0x1FBF` installed, RIP past the load. -/
def mxcsrWitT1 : FpZustand :=
  { mxcsrWitHaupt with kern := { mxcsrWitHaupt.kern with rip := BitVec.ofNat 64 4103 }, fp := ⟨0x1FBF⟩ }

/-- The reached load step installs the preloaded word. -/
theorem mxcsrWit_schritt1 :
    mxcsrByteschritt mxcsrWitHaupt mxcsrProfilModern
      mxcsrSteuerungOffen = .weiter mxcsrWitT1 := by
  have hf := mxcsrWit_fetch1
  have hrd := mxcsrWit_liest
  have hok2 : ldmxcsrArchOk mxcsrProfilModern 0x1FBF = true := by
    decide
  have hs := mxcsrSchritt_ld_erfolg ⟨.ldmxcsr .rax 0, 7, false⟩
    mxcsrWitHaupt mxcsrProfilModern mxcsrSteuerungOffen .rax 0 0x1FBF
    0x1FBF (by decide) rfl mxcsrSteuerungOffen_ok rfl hrd rfl hok2
  unfold mxcsrByteschritt
  rw [hf]
  simp only
  exact hs

/-- Fetch from the actual store bytes yields the store form. -/
theorem mxcsrWit_fetch2 :
    mxcsrFetchDekodiert mxcsrWitT1 =
      some (⟨.stmxcsr .rax 4, 7, false⟩, []) := by
  decide

/-- State after the store: word at `0x2004`, RIP past the store. -/
def mxcsrWitT2 : FpZustand :=
  { mxcsrWitT1 with kern := { mxcsrWitT1.kern with speicher := { mxcsrWitT1.kern.speicher with bytes := writeBytesN mxcsrWitT1.kern.speicher (BitVec.ofNat 64 8196) (mxcsrSpeicherWort 0x1FBF) 4 }, rip := BitVec.ofNat 64 4110 } }

/-- The reached store step writes the installed word at `0x2004`. -/
theorem mxcsrWit_schritt2 :
    mxcsrByteschritt mxcsrWitT1 mxcsrProfilModern
      mxcsrSteuerungOffen = .weiter mxcsrWitT2 := by
  have hf := mxcsrWit_fetch2
  have hwr : write32 mxcsrWitT1.kern.speicher (effAddr mxcsrWitT1.kern Register.rax 4) (mxcsrSpeicherWort 0x1FBF) = some mxcsrWitT2.kern.speicher := by
    have hperm : schreibbarN mxcsrWitT1.kern.speicher (BitVec.ofNat 64 8196) 4 = true := by
      decide
    have heff : effAddr mxcsrWitT1.kern Register.rax 4 = BitVec.ofNat 64 8196 := by
      decide
    rw [heff]
    unfold write32
    rw [if_pos hperm]
    rfl
  have hs := mxcsrSchritt_st_erfolg ⟨.stmxcsr .rax 4, 7, false⟩
    mxcsrWitT1 mxcsrProfilModern mxcsrSteuerungOffen .rax 4
    mxcsrWitT2.kern.speicher (by decide) rfl mxcsrSteuerungOffen_ok rfl
    hwr
  unfold mxcsrByteschritt
  rw [hf]
  simp only
  exact hs

/-- The stored word reads back: `0x1FBF` at `0x2004`. -/
theorem mxcsrWit_liest2 :
    read32 mxcsrWitT2.kern.speicher (BitVec.ofNat 64 8196) =
      some (BitVec.ofNat 64 0x1FBF) := by
  decide

/-- The store observably changed memory (first footprint byte). -/
theorem mxcsrWit_aendert :
    mxcsrWitHaupt.kern.speicher.bytes (BitVec.ofNat 64 8196) ≠
      mxcsrWitT2.kern.speicher.bytes (BitVec.ofNat 64 8196) := by
  decide

/-- The load installed a new control word (real control change). -/
theorem mxcsrWit_kontrolle_aendert :
    mxcsrWitHaupt.fp.mxcsr ≠ mxcsrWitT1.fp.mxcsr := by
  decide

/-- The installed word is admitted (sticky flags stay unchecked). -/
theorem mxcsrWit_eintritt :
    fpEintritt mxcsrWitT1.fp = true := by
  decide

/-- The store preserves the installed control word. -/
theorem mxcsrWit_fp_bleibt : mxcsrWitT2.fp = mxcsrWitT1.fp := rfl

/-- Neighboring bytes are untouched: the byte past the store. -/
theorem mxcsrWit_nachbar_bleibt :
    mxcsrWitT2.kern.speicher.bytes (BitVec.ofNat 64 8200) =
      mxcsrWitHaupt.kern.speicher.bytes (BitVec.ofNat 64 8200) := by
  decide

/-- Code bytes are untouched by the store. -/
theorem mxcsrWit_code_bleibt :
    mxcsrWitT2.kern.speicher.bytes (BitVec.ofNat 64 4096) =
      mxcsrWitHaupt.kern.speicher.bytes (BitVec.ofNat 64 4096) := by
  decide

/-- Past the image there is nothing executable: fetch refuses. -/
theorem mxcsrWit_nachBild_verweigert :
    mxcsrFetchDekodiert mxcsrWitT2 = none := by
  decide

/-! ## 8. Planted negatives: one varied leg each.

  Every refusal below varies exactly one leg of the witness run and
  is decided on actual bytes/words/profiles, never trusted. -/

/-- RESERVED-BIT LOAD: a word with bit 16 set faults with #GP,
    although fetch, gates and permissions all hold. -/
theorem mxcsrNeg_reserviert_gp :
    mxcsrKind (mxcsrByteschritt (mxcsrWitT mxcsrWitCode 0x11F80)
      mxcsrProfilModern mxcsrSteuerungOffen) = 1 := by
  decide

/-- LOCK PREFIX: locked load bytes fault with #UD. -/
theorem mxcsrNeg_lock_ud :
    mxcsrKind (mxcsrByteschritt (mxcsrWitT mxcsrWitCodeLock 0x1FBF)
      mxcsrProfilModern mxcsrSteuerungOffen) = 2 := by
  decide

/-- CONTROL DENIAL: a closed OS gate faults with #UD. -/
theorem mxcsrNeg_tor_ud :
    mxcsrKind (mxcsrByteschritt mxcsrWitHaupt mxcsrProfilModern
      ⟨true, true, true, false⟩) = 2 := by
  decide

/-- MISSING SILICON: no SSE support faults with #UD. -/
theorem mxcsrNeg_silizium_ud :
    mxcsrKind (mxcsrByteschritt mxcsrWitHaupt mxcsrProfilModern
      ⟨false, true, true, true⟩) = 2 := by
  decide

/-- DAZ WITHOUT SUPPORT: the legacy profile faults with #GP. -/
theorem mxcsrNeg_daz_gp :
    mxcsrKind (mxcsrByteschritt (mxcsrWitT mxcsrWitCode 0x1FC0)
      mxcsrProfilAlt mxcsrSteuerungOffen) = 1 := by
  decide

/-- Memory with a hole at the fourth store byte (`0x2007`). -/
def mxcsrWitSpeicherLoch : Speicher :=
  { mxcsrWitT1.kern.speicher with schreibbar := fun a => !(a == BitVec.ofNat 64 8199) }

/-- Post-load state over the holed memory. -/
def mxcsrWitT1Loch : FpZustand :=
  { mxcsrWitT1 with kern := { mxcsrWitT1.kern with speicher := mxcsrWitSpeicherLoch } }

/-- MISSING FOURTH-BYTE PERMISSION (store): the hole refuses, no fault. -/
theorem mxcsrNeg_loch_verweigert :
    mxcsrKind (mxcsrByteschritt mxcsrWitT1Loch mxcsrProfilModern
      mxcsrSteuerungOffen) = 3 := by
  decide

/-- Memory with a hole at the fourth load byte (`0x2003`). -/
def mxcsrWitSpeicherLochLese : Speicher :=
  { mxcsrWitHaupt.kern.speicher with lesbar := fun a => !(a == BitVec.ofNat 64 8195) }

/-- Start state over the read-holed memory. -/
def mxcsrWitHauptLochLese : FpZustand :=
  { mxcsrWitHaupt with kern := { mxcsrWitHaupt.kern with speicher := mxcsrWitSpeicherLochLese } }

/-- MISSING FOURTH-BYTE PERMISSION (load): the hole refuses, no fault. -/
theorem mxcsrNeg_lochLese_verweigert :
    mxcsrKind (mxcsrByteschritt mxcsrWitHauptLochLese mxcsrProfilModern
      mxcsrSteuerungOffen) = 3 := by
  decide

/-- ARCHITECTURALLY LEGAL BUT SOURCE-INADMISSIBLE: the FTZ word loads
    fine (kind 0, the word is installed) although no admitted FP step
    ever runs under it -- hardware #GP and source refusal apart. -/
theorem mxcsrPos_ftz_weiter_aber_unzulässig :
    mxcsrKind (mxcsrByteschritt (mxcsrWitT mxcsrWitCode 0x9F80)
      mxcsrProfilModern mxcsrSteuerungOffen) = 0 ∧
      mxcsrWortNach (mxcsrByteschritt (mxcsrWitT mxcsrWitCode 0x9F80)
        mxcsrProfilModern mxcsrSteuerungOffen) = some 0x9F80 ∧
      fpEintritt ⟨0x9F80⟩ = false := by
  refine ⟨by decide, by decide, ?_⟩
  exact mxcsr_ftz_verweigert

/-- RESET-WORD LOAD establishes the admitted profile. -/
theorem mxcsrPos_reset_stellt_her :
    mxcsrWortNach (mxcsrByteschritt (mxcsrWitT mxcsrWitCode 0x1F80)
      mxcsrProfilModern mxcsrSteuerungOffen) = some 0x1F80 ∧
      fpEintritt ⟨0x1F80⟩ = true := by
  refine ⟨by decide, kontextReset_gueltig⟩

/-! ## 9. Joint witness: fetched save/load with memory and control change.

  The two fetched steps install `0x1FBF` (control change against the
  reset word) and store it at `0x2004` (real memory change with a
  read-back), keep the admitted profile throughout, preserve the
  control word across the store, and leave the neighboring byte, the
  code bytes and the executable image behind the fragment untouched.
  Non-degenerate: a control-changing load plus a store-changing save,
  jointly instantiated with all intermediate access checks. -/

/-- JOINT WITNESS (fetched MXCSR save/load + reached changes): the
    load fetches and installs `0x1FBF`, the store fetches and writes
    it at `0x2004` where it reads back, memory and control observably
    change, the profile stays admitted, and neighbors/code stay put. -/
theorem mxcsr_gelenk_zeuge :
    ∃ (t1 t2 : FpZustand),
      mxcsrFetchDekodiert mxcsrWitHaupt =
        some (⟨.ldmxcsr .rax 0, 7, false⟩, mxcsrEncodeSt .rax 4) ∧
      mxcsrByteschritt mxcsrWitHaupt mxcsrProfilModern
        mxcsrSteuerungOffen = .weiter t1 ∧
      mxcsrWitHaupt.fp.mxcsr ≠ t1.fp.mxcsr ∧
      t1.fp.mxcsr = 0x1FBF ∧
      fpEintritt t1.fp = true ∧
      mxcsrFetchDekodiert t1 =
        some (⟨.stmxcsr .rax 4, 7, false⟩, []) ∧
      mxcsrByteschritt t1 mxcsrProfilModern
        mxcsrSteuerungOffen = .weiter t2 ∧
      read32 t2.kern.speicher (BitVec.ofNat 64 8196) =
        some (BitVec.ofNat 64 0x1FBF) ∧
      mxcsrWitHaupt.kern.speicher.bytes (BitVec.ofNat 64 8196) ≠
        t2.kern.speicher.bytes (BitVec.ofNat 64 8196) ∧
      t2.fp = t1.fp ∧
      t2.kern.speicher.bytes (BitVec.ofNat 64 8200) =
        mxcsrWitHaupt.kern.speicher.bytes (BitVec.ofNat 64 8200) ∧
      mxcsrFetchDekodiert t2 = none := by
  exact ⟨mxcsrWitT1, mxcsrWitT2, mxcsrWit_fetch1, mxcsrWit_schritt1,
    mxcsrWit_kontrolle_aendert, rfl, mxcsrWit_eintritt, mxcsrWit_fetch2,
    mxcsrWit_schritt2, mxcsrWit_liest2, mxcsrWit_aendert,
    mxcsrWit_fp_bleibt, mxcsrWit_nachbar_bleibt,
    mxcsrWit_nachBild_verweigert⟩

/- CUTS: what is not proved here.

   Proved here, over the reused canonical vocabulary (`Typen`,
   `Speicher` with the REAL `read32`/`write32`, `Ausfuehrung`,
   `Codec`, `Byteschritt`, `Gleitprofil`, `ScalarFloat` with its
   `FpZustand`/`fpEintritt`, `FeatureProfile` untouched):
   - exact selected legacy forms `NP 0F AE /2` (LDMXCSR m32) and
     `NP 0F AE /3` (STMXCSR m32) with ModRM mod 10 plus disp32 and
     the pilot SIB rule, decoded from fetched bytes with an optional
     LOCK prefix, generic round trips, encoder lengths and planted
     malformed/truncation refusals;
   - architectural checks: reserved bits 16-31 unconditionally (Vol. 1
     Fig. 10-3), DAZ and writable-bit mask as PROFILE data (Vol. 1
     §§10.2.3.4/11.6.6), feature/control gates (Type 5 class), with
     #GP vs #UD vs validator-refusal kept apart;
   - the four-byte memory discipline: LDMXCSR reads through `read32`
     (never an 8-byte load), STMXCSR writes through `write32` with
     reserved bits stored as `0s` (never an 8-byte store), with full
     frames (flags/GPRs/XMM/permissions preserved, exactly the
     four-byte footprint changes);
   - the byte-executed fragment: fetched LDMXCSR installs `0x1FBF`
     (control change), fetched STMXCSR stores it (memory change with
     read-back), reset-word load establishes admission, FTZ-word load
     succeeds architecturally while staying source-inadmissible,
     neighboring-byte/code frames, past-image refusal;
   - the adapter boundary (§6: `mxcsrByteschritt` input, `MxcsrAusgang`
     output with kind and observation accessors) for lanes
     660/670/672/674, which own the integration on their side.
   NOT proved here, and not claimed:
   - No VEX forms (VLDMXCSR/VSTMXCSR), no REX extension, no mod 0/1
     memory shapes, no FXSAVE/FXRSTOR composition: a partial MXCSR
     save is not full XMM/YMM interrupt context preservation (open
     for 672/674/660); legacy x87 state is untouched throughout.
   - Silicon splits control denial into #UD (EM/OSFXSR) and #NM (TS);
     this model merges them as `fehlerUD`. CR0/CR4 values are gate
     data, never probed hardware; CPUID/VEX checks beyond the gates
     are absent by construction.
   - MXCSR_MASK values (`0xFFFF`/`0xFFBF`) are example profile data;
     real silicon values come from FXSAVE on the target. Sticky-flag
     accumulation/traps, sNaN quieting, NaN payloads, the deferred
     exception on the next XMM/YMM instruction, alignment (#AC),
     paging (#PF/#SS) beyond permission `none`, TSO granularity and
     tearing of the four-byte access, costs, timing and budgets stay
     open. Permission `none` is validator refusal, never a fault.
   - No source/checker/emitter/goal claim: the joint witness pairs
     reached byte execution with its observations; no lowering
     between source programs and these bytes is stated. Full
     source-to-final-loaded-bytes validation remains OPEN.
   - Rule 13 (inhabitation): no theorem here quantifies over source
     syntax; the joint non-degenerate witness is `mxcsr_gelenk_zeuge`
     (control-changing load plus store-changing save, all premises
     jointly instantiated on concrete bytes, words and profiles).
-/

#print axioms mxcsrSteuerungOk_verweigert
#print axioms mxcsrSteuerungOffen_ok
#print axioms mxcsrReserviertFrei_verweigert
#print axioms mxcsrReserviertFrei_reset
#print axioms ldmxcsrArchOk_reset
#print axioms ldmxcsrArchOk_reset_modern
#print axioms ldmxcsrArchOk_reserviert_verweigert
#print axioms ldmxcsrArchOk_daz_verweigert
#print axioms ldmxcsrArchOk_maske_verweigert
#print axioms ldmxcsrArchOk_ftz_modern
#print axioms mxcsrSpeicherWort_tief
#print axioms mxcsrSpeicherWort_rundlauf
#print axioms mxcsrSchritt_laenge_verweigert
#print axioms mxcsrSchritt_gesperrt_ud
#print axioms mxcsrSchritt_tor_ud
#print axioms mxcsrSchritt_ld_erfolg
#print axioms mxcsrSchritt_ld_gp
#print axioms mxcsrSchritt_ld_verweigert
#print axioms mxcsrSchritt_st_erfolg
#print axioms mxcsrSchritt_st_verweigert
#print axioms mxcsrSchritt_ld_flags
#print axioms mxcsrSchritt_ld_speicher
#print axioms mxcsrSchritt_ld_gpr
#print axioms mxcsrSchritt_ld_xmm
#print axioms mxcsrSchritt_ld_wort
#print axioms mxcsrSchritt_st_fp
#print axioms mxcsrSchritt_st_flags
#print axioms mxcsrSchritt_st_rahmen
#print axioms mxcsrSchritt_st_berechtigungen
#print axioms mxcsrSchritt_st_gpr
#print axioms mxcsrSchritt_st_xmm
#print axioms mxcsrEscape_pin
#print axioms mxcsrRoundtrip_ld
#print axioms mxcsrRoundtrip_st
#print axioms mxcsrEncodeLd_len
#print axioms mxcsrEncodeSt_len
#print axioms mxcsrEncode_len_pin
#print axioms mxcsrDecode_lockt_ld_pin
#print axioms mxcsrDecode_lockt_st_pin
#print axioms mxcsrDecode_register_verweigert
#print axioms mxcsrDecode_feldNull_verweigert
#print axioms mxcsrDecode_falscherOpcode_verweigert
#print axioms mxcsrDecode_abgeschnitten_verweigert
#print axioms mxcsrDecode_lockAllein_verweigert
#print axioms mxcsrFetchDekodiert_erfolg
#print axioms mxcsrByteschritt_schritt
#print axioms mxcsrByteschritt_gp
#print axioms mxcsrByteschritt_ud
#print axioms mxcsrByteschritt_hol_verweigert
#print axioms mxcsrKind_weiter
#print axioms mxcsrKind_gp
#print axioms mxcsrKind_ud
#print axioms mxcsrKind_verweigert
#print axioms mxcsrSpeicherNach_gp
#print axioms mxcsrWortNach_gp
#print axioms mxcsrWortNach_verweigert
#print axioms mxcsrWitCode_len
#print axioms mxcsrWit_geholt
#print axioms mxcsrWit_fetch1
#print axioms mxcsrWit_liest
#print axioms mxcsrWit_effAddr
#print axioms mxcsrWit_schritt1
#print axioms mxcsrWit_fetch2
#print axioms mxcsrWit_schritt2
#print axioms mxcsrWit_liest2
#print axioms mxcsrWit_aendert
#print axioms mxcsrWit_kontrolle_aendert
#print axioms mxcsrWit_eintritt
#print axioms mxcsrWit_fp_bleibt
#print axioms mxcsrWit_nachbar_bleibt
#print axioms mxcsrWit_code_bleibt
#print axioms mxcsrWit_nachBild_verweigert
#print axioms mxcsrNeg_reserviert_gp
#print axioms mxcsrNeg_lock_ud
#print axioms mxcsrNeg_tor_ud
#print axioms mxcsrNeg_silizium_ud
#print axioms mxcsrNeg_daz_gp
#print axioms mxcsrNeg_loch_verweigert
#print axioms mxcsrNeg_lochLese_verweigert
#print axioms mxcsrPos_ftz_weiter_aber_unzulässig
#print axioms mxcsrPos_reset_stellt_her
#print axioms mxcsr_gelenk_zeuge

end Gabbro.Grammatik.X86
