/-
  File:      Grammatik/X86/AddressedHardwareExecution.lean
  Subject:   Full selected SIB/RIP-relative addresses bound to actual effects.

  Lane 730: a generic checked effective-address adapter over the accepted
  `AddressEncoding` selected forms (`AdrForm`, `adrEff`, `parseAdrTail`,
  `kanonisch48`, `fussZugelassen`). It binds the actual instruction
  length/next RIP and the canonical register values to real producer
  access effects (LOCK XADD through `LockedInstructionExecution`, address
  math through `EffectiveAddress`). No new memory micro-interpreter and
  no second decoder for accepted rows: pilot-owned tails stay refused by
  the reused `parseAdrTail`, proved in both directions below.
  Provenance: clone-local Intel SDM 325462-093US Sep 2026, Vol. 1
  Section 3.7.5 (specifying an offset), Section 3.7.5.1 (64-bit mode,
  RIP-relative addressing), LOCK prefix and XADD entries.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.Byteschritt
import Grammatik.X86.AddressEncoding
import Grammatik.X86.EffectiveAddress
import Grammatik.X86.LockedOps
import Grammatik.X86.LockedInstructionExecution

namespace Gabbro.Grammatik.X86

/-- Ordered admission faults of one addressed access: canonical form
    first, no-wrap second, per-direction permission last. -/
inductive AdrFehler where
  | unkanonisch | umbruch | keinLesen | keinSchreiben
  deriving DecidableEq, Repr

/-! ## 1. Ordered admission: canonical, no-wrap, then permission.

    The adapter checks the computed `adrEff` address in fault order and
    reports the FIRST failure. It reuses the accepted `kanonisch48`,
    `OhneUmbruch` range and `lesbar8`/`schreibbar8` checks, so success
    coincides exactly with the accepted `fussZugelassen`. -/

/-- Checked admission of one computed address in fault order. -/
def adrPruefe (m : Speicher) (a : Adresse) (schreiben : Bool) :
    Option AdrFehler :=
  match kanonisch48 a with
  | false => some .unkanonisch
  | true =>
    match decide (a.toNat + 8 ≤ 2 ^ 64) with
    | false => some .umbruch
    | true =>
      let ok := if schreiben then schreibbar8 m a else lesbar8 m a
      match ok with
      | false => some (if schreiben then .keinSchreiben else .keinLesen)
      | true => none

/-- The ordered check succeeds exactly where `fussZugelassen` admits:
    no second admission model is invented. -/
theorem adrPruefe_gleich_fuss (m : Speicher) (a : Adresse)
    (schreiben : Bool) :
    adrPruefe m a schreiben = none ↔
      fussZugelassen m a schreiben = true := by
  unfold adrPruefe fussZugelassen
  cases hkan : kanonisch48 a with
  | false => simp [hkan]
  | true =>
    simp only [hkan]
    cases hwrap : decide (a.toNat + 8 ≤ 2 ^ 64) with
    | false => simp [hwrap]
    | true =>
      simp only [hwrap]
      cases schreiben with
      | true =>
        cases hperm : schreibbar8 m a <;> simp [hperm]
      | false =>
        cases hperm : lesbar8 m a <;> simp [hperm]

/-- ORDER: a noncanonical address is refused before permissions are
    consulted, even with full rights. -/
theorem adrPruefe_ordnung_kanonisch (m : Speicher) (a : Adresse)
    (schreiben : Bool)     (h : kanonisch48 a = false) :
    adrPruefe m a schreiben = some .unkanonisch := by
  unfold adrPruefe
  simp only [h]

/-- ORDER: a wrapping footprint is refused before permissions, even
    with full rights and a canonical top-of-space address. -/
theorem adrPruefe_ordnung_umbruch (m : Speicher) (a : Adresse)
    (schreiben : Bool) (hkan : kanonisch48 a = true)
    (hwrap : ¬ a.toNat + 8 ≤ 2 ^ 64) :
    adrPruefe m a schreiben = some .umbruch := by
  have hdec : decide (a.toNat + 8 ≤ 2 ^ 64) = false :=
    decide_eq_false hwrap
  unfold adrPruefe
  simp only [hkan, hdec]

/-! ## 2. Generic addressed access with actual length/next-RIP binding.

    The adapter computes `adrEff` from the canonical register values,
    admits it through `adrPruefe`, and performs the REAL `read64` /
    `write64` effect, advancing RIP by the ACTUAL instruction length
    `l`. A bad length refuses before any memory is touched. -/

/-- Checked load through a full selected form: the word at `adrEff`,
    or the first admission fault in order. -/
def adrLade (m : Speicher) (s : Zustand) (ripNext : Adresse)
    (f : AdrForm) : Option Wort ⊕ AdrFehler :=
  let a := adrEff s ripNext f
  match adrPruefe m a false with
  | some e => .inr e
  | none =>
    match read64 m a with
    | some v => .inl v
    | none => .inr .keinLesen

/-- Checked store through a full selected form: the successor memory,
    or the first admission fault in order. -/
def adrSpeichere (m : Speicher) (s : Zustand) (ripNext : Adresse)
    (f : AdrForm) (v : Wort) : Option Speicher ⊕ AdrFehler :=
  let a := adrEff s ripNext f
  match adrPruefe m a true with
  | some e => .inr e
  | none =>
    match write64 m a v with
    | some m' => .inl m'
    | none => .inr .keinSchreiben

/-- A successful addressed load reads exactly the effective address. -/
theorem adrLade_erfolg (m : Speicher) (s : Zustand) (ripNext : Adresse)
    (f : AdrForm) (v : Wort)
    (h : adrLade m s ripNext f = .inl v) :
    read64 m (adrEff s ripNext f) = some v := by
  unfold adrLade at h
  cases hpr : adrPruefe m (adrEff s ripNext f) false with
  | some e => simp [hpr] at h
  | none =>
    simp only [hpr] at h
    cases hrd : read64 m (adrEff s ripNext f) with
    | none => simp [hrd] at h
    | some w =>
      simp [hrd] at h
      rw [h]

/-- A refused addressed load admits no value: every outcome is a fault. -/
theorem adrLade_verweigert_fehler (m : Speicher) (s : Zustand)
    (ripNext : Adresse) (f : AdrForm) (e : AdrFehler)
    (h : adrLade m s ripNext f = .inr e) :
    adrPruefe m (adrEff s ripNext f) false = some e ∨
      read64 m (adrEff s ripNext f) = none := by
  unfold adrLade at h
  cases hpr : adrPruefe m (adrEff s ripNext f) false with
  | some e' =>
    simp [hpr] at h
    subst h
    exact Or.inl rfl
  | none =>
    simp only [hpr] at h
    cases hrd : read64 m (adrEff s ripNext f) with
    | some w => simp [hrd] at h
    | none => exact Or.inr rfl

/-- A successful addressed store writes exactly the eight bytes at the
    effective address and preserves every permission. -/
theorem adrSpeichere_erfolg (m m' : Speicher) (s : Zustand)
    (ripNext : Adresse) (f : AdrForm) (v : Wort)
    (h : adrSpeichere m s ripNext f v = .inl m') :
    write64 m (adrEff s ripNext f) v = some m' ∧
      m'.lesbar = m.lesbar ∧ m'.schreibbar = m.schreibbar ∧
      m'.ausfuehrbar = m.ausfuehrbar := by
  unfold adrSpeichere at h
  cases hpr : adrPruefe m (adrEff s ripNext f) true with
  | some e => simp [hpr] at h
  | none =>
    simp only [hpr] at h
    cases hwr : write64 m (adrEff s ripNext f) v with
    | none => simp [hwr] at h
    | some w =>
      simp [hwr] at h
      subst h
      exact ⟨rfl, write64_erhaelt_berechtigungen m _ v w hwr⟩

/-- BRIDGE: on the pilot-owned shape the adapter reads the PILOT
    address: adapter success is a pilot-footprint read, by reuse of
    `adrEff_basisForm` and not a second address model. -/
theorem adrLade_basisForm_pilot (m : Speicher) (s : Zustand)
    (b : Register) (d : BitVec 32) (n : Adresse) (v : Wort)
    (h : adrLade m s n (basisForm b d) = .inl v) :
    read64 m (effAddr s b d) = some v := by
  have hrd := adrLade_erfolg m s n (basisForm b d) v h
  rw [adrEff_basisForm] at hrd
  exact hrd

/-! ## 3. LOCK XADD through full selected forms.

    `decodeLockAdr` matches the accepted LOCK + canonical REX.W + 0F +
    XADD prefix (reusing `rexLockBits`) and parses the TAIL with the
    accepted `parseAdrTail`. Pilot-owned tails stay refused by that
    reused parser, so no accepted row is re-decided. `lockXaddAdr`
    mirrors the accepted `lockSchrittVoll` XADD arm with the target
    `adrEff` plus the canonical/no-wrap pre-checks. -/

/-- Admission granted for a write direction: canonical, no wrap and
    write rights give no fault. -/
theorem adrPruefe_schreib_frei (m : Speicher) (a : Adresse)
    (hkan : kanonisch48 a = true)
    (hwrap : a.toNat + 8 ≤ 2 ^ 64)
    (hperm : schreibbar8 m a = true) :
    adrPruefe m a true = none := by
  have hdec : decide (a.toNat + 8 ≤ 2 ^ 64) = true :=
    decide_eq_true hwrap
  unfold adrPruefe
  simp only [hkan, hdec, hperm, if_true]

/-- Admission refused for a write direction: without write rights the
    fault is named, after the canonical and wrap checks. -/
theorem adrPruefe_schreib_verweigert (m : Speicher) (a : Adresse)
    (hkan : kanonisch48 a = true)
    (hwrap : a.toNat + 8 ≤ 2 ^ 64)
    (hperm : schreibbar8 m a = false) :
    adrPruefe m a true = some .keinSchreiben := by
  have hdec : decide (a.toNat + 8 ≤ 2 ^ 64) = true :=
    decide_eq_true hwrap
  unfold adrPruefe
  simp only [hkan, hdec, hperm, if_true]

/-- Extended LOCK decode: LOCK prefix, canonical REX.W (`rexLockBits`,
    hence X = 0 exactly as the accepted producer), 0F escape, XADD
    opcode 193, then the selected tail through the accepted
    `parseAdrTail`. Anything else refuses with `none`. -/
def decodeLockAdr : List Byte → Option (Register × AdrForm × List Byte)
  | [] => none
  | b0 :: rest0 =>
    if byteNat b0 == 240 then
      match rest0 with
      | [] => none
      | b1 :: rest1 =>
        match rexLockBits b1 with
        | some (rh, bh) =>
          match rest1 with
          | [] => none
          | b2 :: rest2 =>
            if byteNat b2 == 15 then
              match rest2 with
              | [] => none
              | b3 :: rest3 =>
                if byteNat b3 == 193 then
                  parseAdrTail rh 0 bh rest3
                else none
            else none
        | none => none
    else none

/-- Full-form LOCK XADD on a locked machine: the actual length `len`
    and next RIP `ripNext` bind the fetched bytes to the effect. Order:
    length, own-buffer, canonical, no-wrap, alignment, read permission,
    write permission. Every memory failure is `speicherFehler`, exactly
    as the accepted producer classifies it. -/
def lockXaddAdr (c : Nat) (src : Register) (f : AdrForm) (len : Nat)
    (m : LockMaschine) (ripNext : Adresse) : LockAusgang :=
  match laengeOk len with
  | false => .verweigert
  | true =>
    match m.puffer c with
    | _ :: _ => .verweigert
    | [] =>
      match adrPruefe m.zu.speicher (adrEff m.zu ripNext f) true with
      | some _ => .speicherFehler
      | none =>
        if ausgerichtet8 (adrEff m.zu ripNext f) then
          match read64 m.zu.speicher (adrEff m.zu ripNext f) with
          | none => .speicherFehler
          | some alt =>
            match write64 m.zu.speicher (adrEff m.zu ripNext f)
                (alt + m.zu.register src) with
            | none => .speicherFehler
            | some mem' =>
              let r := add64 alt (m.zu.register src)
              let z1 :=
                schrittRegister m.zu (ripNach m.zu.rip len) r.2 src alt
              let z2 := { z1 with speicher := mem' }
              LockAusgang.ok ⟨z2, m.puffer⟩
                ⟨c, Fuss (adrEff m.zu ripNext f),
                  Fuss (adrEff m.zu ripNext f), some alt,
                  some (alt + m.zu.register src), true, false⟩
        else .verweigert

/-! ## 4. No silent completeness: disjoint coverage, lawful adapter.

    The extended decoder and the accepted producer decoder cover
    DISJOINT byte sets: pilot-owned tails are refused here, extended
    tails are refused there, each pinned on closed bytes. On the
    overlapping admitted subset (base plus displacement, canonical and
    aligned) the adapter reaches EXACTLY the accepted producer outcome,
    from equations rather than successor assumptions. -/

/-- The extended decoder refuses the pilot base-plus-disp32 encoding. -/
theorem decoder_weist_pilot_basis_zurueck :
    decodeLockAdr (encodeLock (.xadd64 .rax .rbx (BitVec.ofNat 32 5))) =
      none := by
  decide

/-- The extended decoder refuses the pilot SIB-36 encoding. -/
theorem decoder_weist_pilot_sib_zurueck :
    decodeLockAdr (encodeLock (.xadd64 .rax .rsp (BitVec.ofNat 32 5))) =
      none := by
  decide

/-- The accepted producer refuses the extended scaled tail. -/
theorem produzent_weist_skaliert_zurueck :
    decodeLock [natByte 240, natByte 77, natByte 15, natByte 193,
      natByte 68, natByte 200, natByte 0] = none := by
  decide

/-- The extended decoder takes the scaled tail whole. -/
theorem decoder_nimmt_skaliert :
    decodeLockAdr [natByte 240, natByte 77, natByte 15, natByte 193,
      natByte 68, natByte 200, natByte 0] =
      some (.r8,
        ⟨some .r8, some .rcx, 8, u8Nach32 (natByte 0), .d8, false⟩,
        []) := by
  decide

/-- LAWFUL ADAPTER: on the pilot-owned shape, with a canonical,
    no-wrap, aligned target, the full-form XADD reaches exactly the
    accepted producer outcome, for every hardware and readiness
    profile (the XADD arm consults neither). -/
theorem lockXaddAdr_basisForm (c : Nat) (src b : Register)
    (d : BitVec 32) (len : Nat) (m : LockMaschine)
    (ripNext : Adresse) (hw : HwProfil) (bp : BereitProfil)
    (hkan : kanonisch48 (effAddr m.zu b d) = true)
    (hwrap : (effAddr m.zu b d).toNat + 8 ≤ 2 ^ 64)
    (hali : ausgerichtet8 (effAddr m.zu b d) = true) :
    lockXaddAdr c src (basisForm b d) len m ripNext =
      lockSchrittVoll (.ok (.xadd64 src b d) len) c m hw bp := by
  unfold lockXaddAdr lockSchrittVoll
  simp only [adrEff_basisForm]
  cases hlen : laengeOk len with
  | false => rfl
  | true =>
    cases hbuf : m.puffer c with
    | cons _ _ => rfl
    | nil =>
      cases hperm : schreibbar8 m.zu.speicher (effAddr m.zu b d) with
      | true =>
        simp only [adrPruefe_schreib_frei _ _ hkan hwrap hperm, hali]
        cases hrd : read64 m.zu.speicher (effAddr m.zu b d) with
        | none => rfl
        | some alt =>
          cases hwr : write64 m.zu.speicher (effAddr m.zu b d)
              (alt + m.zu.register src) with
          | none => rfl
          | some mem' => rfl
      | false =>
        simp only [adrPruefe_schreib_verweigert _ _ hkan hwrap hperm,
          hali]
        cases hrd : read64 m.zu.speicher (effAddr m.zu b d) with
        | none => rfl
        | some a =>
          dsimp only
          simp only [write64_verweigert _ _ _ hperm, if_true]

/-- Success pins the full successor: the word grows by the source
    register, the source takes the old word, RIP advances by the
    actual length, and the event records the full-form footprint. -/
theorem lockXaddAdr_erfolg (c : Nat) (src : Register) (f : AdrForm)
    (len : Nat) (m : LockMaschine) (ripNext : Adresse)
    (alt sval : Wort) (mem' : Speicher)
    (hok : laengeOk len = true)
    (hbuf : m.puffer c = [])
    (hfrei : adrPruefe m.zu.speicher (adrEff m.zu ripNext f) true = none)
    (hali : ausgerichtet8 (adrEff m.zu ripNext f) = true)
    (hrd : read64 m.zu.speicher (adrEff m.zu ripNext f) = some alt)
    (hreg : m.zu.register src = sval)
    (hwr : write64 m.zu.speicher (adrEff m.zu ripNext f) (alt + sval) =
      some mem') :
    ∃ (m' : LockMaschine) (ev : LockEreignis),
      lockXaddAdr c src f len m ripNext = LockAusgang.ok m' ev ∧
        m'.zu.speicher = mem' ∧
        m'.zu.register src = alt ∧
        m'.zu.rip = ripNach m.zu.rip len ∧
        ev.lesen = Fuss (adrEff m.zu ripNext f) ∧
        ev.gelesen = some alt ∧
        ev.geschrieben = some (alt + sval) := by
  unfold lockXaddAdr
  simp only [hok, hbuf, hfrei, hali, hrd, hreg, hwr]
  exact ⟨_, _, rfl, rfl, by simp [schrittRegister, regSet],
    rfl, rfl, rfl, rfl⟩

/-- One fetched full-form XADD step: decode the actual fetched window
    and run the adapter with the measured length and the post-decode
    RIP as the RIP base. A failed fetch refuses loudly. -/
def lockXaddGeholt (c : Nat) (m : LockMaschine) : LockAusgang :=
  match decodeLockAdr (geholt m.zu) with
  | none => .verweigert
  | some (src, f, rest) =>
    let l := (geholt m.zu).length - rest.length
    lockXaddAdr c src f l m (ripNach m.zu.rip l)

/-! ## 5. Reached witnesses: fetched scaled and RIP-relative XADD.

    Both witnesses fetch CLOSED bytes from actual executable memory and
    change data memory observably: the scaled SIB form writes through
    `r8 + rcx * 8`, the RIP-relative form through `ripNext + disp`,
    both landing on the aligned word at 8200. -/

/-- Scaled witness image: `LOCK XADD r8, [r8 + rcx*8 + 0]`. -/
def lockAdrWitBild : List Byte :=
  [natByte 240, natByte 77, natByte 15, natByte 193,
    natByte 68, natByte 200, natByte 0]

/-- RIP-relative witness image: `LOCK XADD r8, [rip + 4095]`. -/
def lockRipWitBild : List Byte :=
  [natByte 240, natByte 76, natByte 15, natByte 193,
    natByte 5, natByte 255, natByte 15, natByte 0, natByte 0]

/-- Witness code bytes: the image at 4096, zeroes elsewhere. -/
def lockWitBytes (bild : List Byte) (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else
    match bild[a.toNat - 4096]? with
    | some b => b
    | none => BitVec.ofNat 8 0

/-- Witness execute permission: exactly the image bytes. -/
def lockWitCode (n : Nat) (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4096 + n)

/-- Witness data permission: sixteen bytes at 8192. -/
def lockWitDaten (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8208)

/-- Witness memory over one image. -/
def lockWitSpeicher (bild : List Byte) (n : Nat) : Speicher :=
  { bytes := lockWitBytes bild, lesbar := lockWitDaten,
    schreibbar := lockWitDaten, ausfuehrbar := lockWitCode n }

/-- Witness registers: `r8 = 8192`, `rcx = 1`. -/
def lockWitReg : Register → Wort
  | .r8 => BitVec.ofNat 64 8192
  | .rcx => BitVec.ofNat 64 1
  | .rsp => BitVec.ofNat 64 8704
  | _ => BitVec.ofNat 64 0

/-- Scaled witness machine: code at 4096, empty buffers. -/
def lockAdrWit : LockMaschine :=
  ⟨{ register := lockWitReg, flags := zeugeFlags,
     rip := BitVec.ofNat 64 4096,
     speicher := lockWitSpeicher lockAdrWitBild 7 },
   fun _ => []⟩

/-- RIP-relative witness machine: code at 4096, empty buffers. -/
def lockRipWit : LockMaschine :=
  ⟨{ register := lockWitReg, flags := zeugeFlags,
     rip := BitVec.ofNat 64 4096,
     speicher := lockWitSpeicher lockRipWitBild 9 },
   fun _ => []⟩

/-- JOINT WITNESS: the fetched scaled XADD lands `0 + 8192` at
    `r8 + rcx * 8 = 8200`, observably changing byte 8201 from zero,
    exchanging `r8 := 0` and advancing RIP past its seven bytes. -/
theorem lockXaddGeholt_zeuge :
    lockAdrWit.zu.speicher.bytes (BitVec.ofNat 64 8201) =
      BitVec.ofNat 8 0 ∧
    (match lockXaddGeholt 0 lockAdrWit with
     | .ok m' ev =>
       some (m'.zu.speicher.bytes (BitVec.ofNat 64 8201),
         ev.gelesen, ev.geschrieben, m'.zu.register .r8, m'.zu.rip)
     | _ => none) =
      some (BitVec.ofNat 8 32, some 0,
        some (BitVec.ofNat 64 8192), 0, BitVec.ofNat 64 4103) := by
  refine ⟨by decide, by decide⟩

/-- The extended decoder takes the RIP-relative tail whole. -/
theorem decoder_nimmt_rip :
    decodeLockAdr [natByte 240, natByte 76, natByte 15, natByte 193,
      natByte 5, natByte 255, natByte 15, natByte 0, natByte 0] =
      some (.r8, ripForm (BitVec.ofNat 32 4095), []) := by
  decide

/-- The accepted producer refuses the RIP-relative LOCK tail. -/
theorem produzent_weist_rip_zurueck :
    decodeLock [natByte 240, natByte 76, natByte 15, natByte 193,
      natByte 5, natByte 255, natByte 15, natByte 0, natByte 0] =
      none := by
  decide

/-- PURE RIP OBSERVATION: the RIP-relative form names 8200 from the
    post-decode RIP, without touching memory. -/
theorem ripForm_beobachtung :
    adrEff lockRipWit.zu (ripNach lockRipWit.zu.rip 9)
      (ripForm (BitVec.ofNat 32 4095)) = BitVec.ofNat 64 8200 := by
  decide

/-- JOINT WITNESS: the fetched RIP-relative XADD lands `0 + 8192` at
    `ripNext + 4095 = 8200`, with the same observable change,
    exchange and RIP advance (nine bytes this time). -/
theorem lockRipGeholt_zeuge :
    lockRipWit.zu.speicher.bytes (BitVec.ofNat 64 8201) =
      BitVec.ofNat 8 0 ∧
    (match lockXaddGeholt 0 lockRipWit with
     | .ok m' ev =>
       some (m'.zu.speicher.bytes (BitVec.ofNat 64 8201),
         ev.gelesen, ev.geschrieben, m'.zu.register .r8, m'.zu.rip)
     | _ => none) =
      some (BitVec.ofNat 8 32, some 0,
        some (BitVec.ofNat 64 8192), 0, BitVec.ofNat 64 4105) := by
  refine ⟨by decide, by decide⟩

/-! ## 6. Negative probes: malformed tails, length, order, faults.

    Every refusal below is pinned on closed bytes or proved in full
    generality from the definition: register-direct and truncated
    tails, missing LOCK and legacy prefixes, zero length, a nonempty
    buffer ahead of a bad address, a noncanonical address ahead of
    permissions, and a failed read behind admitted checks. -/

/-- REFUSAL: register-direct under LOCK names no address here (the
    producer parses it as architectural #UD; no UD is claimed here). -/
theorem decoder_weist_mod3_zurueck :
    decodeLockAdr [natByte 240, natByte 76, natByte 15, natByte 193,
      natByte 192] = none := by
  decide

/-- REFUSAL: ModRM without its SIB byte (truncated). -/
theorem decoder_weist_ohne_sib_zurueck :
    decodeLockAdr [natByte 240, natByte 76, natByte 15, natByte 193,
      natByte 68] = none := by
  decide

/-- REFUSAL: SIB present but the displacement byte missing. -/
theorem decoder_weist_kurze_disp8_zurueck :
    decodeLockAdr [natByte 240, natByte 77, natByte 15, natByte 193,
      natByte 68, natByte 200] = none := by
  decide

/-- REFUSAL: no LOCK prefix, no extended row. -/
theorem decoder_weist_ohne_lock_zurueck :
    decodeLockAdr [natByte 15, natByte 193, natByte 68, natByte 200,
      natByte 0] = none := by
  decide

/-- REFUSAL: a legacy prefix before LOCK is not canonical. -/
theorem decoder_weist_vorsatz_zurueck :
    decodeLockAdr [natByte 102, natByte 240, natByte 77, natByte 15,
      natByte 193, natByte 68, natByte 200, natByte 0] = none := by
  decide

/-- REFUSAL: zero length never steps, whatever the machine holds. -/
theorem lockXaddAdr_laenge_verweigert (m : LockMaschine) (f : AdrForm)
    (n : Adresse) :
    lockXaddAdr 0 .rax f 0 m n = .verweigert := by
  unfold lockXaddAdr
  rfl

/-- ORDER: a nonempty own buffer refuses before the address is
    consulted at all. -/
theorem lockXaddAdr_puffer_zuerst (c : Nat) (src : Register)
    (f : AdrForm) (len : Nat) (m : LockMaschine) (ripNext : Adresse)
    (x : TSOEintrag) (xs : List TSOEintrag)
    (hok : laengeOk len = true) (hbuf : m.puffer c = x :: xs) :
    lockXaddAdr c src f len m ripNext = .verweigert := by
  unfold lockXaddAdr
  simp only [hok, hbuf]

/-- ORDER: a noncanonical target is a memory fault even with an empty
    buffer and a good length, before permissions are consulted. -/
theorem lockXaddAdr_unkanonisch (c : Nat) (src : Register)
    (f : AdrForm) (len : Nat) (m : LockMaschine) (ripNext : Adresse)
    (hok : laengeOk len = true) (hbuf : m.puffer c = [])
    (hkan : kanonisch48 (adrEff m.zu ripNext f) = false) :
    lockXaddAdr c src f len m ripNext = .speicherFehler := by
  unfold lockXaddAdr
  simp only [hok, hbuf, adrPruefe_ordnung_kanonisch _ _ _ hkan]

/-- FAULT: a failed read behind admitted checks is a memory fault,
    never a silent value. -/
theorem lockXaddAdr_lesefehler (c : Nat) (src : Register) (f : AdrForm)
    (len : Nat) (m : LockMaschine) (ripNext : Adresse)
    (hok : laengeOk len = true) (hbuf : m.puffer c = [])
    (hali : ausgerichtet8 (adrEff m.zu ripNext f) = true)
    (hrd : read64 m.zu.speicher (adrEff m.zu ripNext f) = none) :
    lockXaddAdr c src f len m ripNext = .speicherFehler := by
  unfold lockXaddAdr
  simp only [hok, hbuf]
  cases hpr : adrPruefe m.zu.speicher (adrEff m.zu ripNext f) true with
  | some _ => rfl
  | none => simp only [hali, hrd, if_true]

/-- CANONICAL FIRST on closed values: the noncanonical hole refuses
    under fully permissive memory. -/
theorem adrPruefe_loch :
    adrPruefe zeugenSpeicher (BitVec.ofNat 64 (2 ^ 47)) true =
      some .unkanonisch := by
  decide

/-! ## 7. Aliasing across forms: one address, several spellings.

    Different full forms may name the same address; the adapter never
    claims injectivity. The two witnesses above already land on 8200
    through different forms; the pins below name the equality. -/

/-- Witness registers for the alias pin: `rbx = 8192`, `rcx = 0`. -/
def aliasReg : Register → Wort
  | .rbx => BitVec.ofNat 64 8192
  | .rcx => BitVec.ofNat 64 0
  | _ => BitVec.ofNat 64 0

/-- ALIAS: a scaled form with a zero index IS the base form. -/
theorem adress_alias_pin :
    adrEff ⟨aliasReg, zeugeFlags, BitVec.ofNat 64 0, zeugenSpeicher⟩
        (BitVec.ofNat 64 0)
        (skaliertForm .rbx .rcx 8 (BitVec.ofNat 32 5) .d8) =
      adrEff ⟨aliasReg, zeugeFlags, BitVec.ofNat 64 0, zeugenSpeicher⟩
        (BitVec.ofNat 64 0) (basisForm .rbx (BitVec.ofNat 32 5)) := by
  decide

/-- ALIAS at the witness addresses: the scaled SIB spelling and the
    RIP-relative spelling both name 8200. -/
theorem adress_formen_alias_pin :
    adrEff lockAdrWit.zu (ripNach lockAdrWit.zu.rip 7)
        ⟨some .r8, some .rcx, 8, u8Nach32 (natByte 0), .d8, false⟩ =
        BitVec.ofNat 64 8200 ∧
      adrEff lockRipWit.zu (ripNach lockRipWit.zu.rip 9)
          (ripForm (BitVec.ofNat 32 4095)) =
        BitVec.ofNat 64 8200 := by
  decide

/-! ## 8. Consumer interface (documentation only).

    Unified-dispatcher and concurrency consumers use exactly:
    `decodeLockAdr` (bytes to source register, `AdrForm`, rest),
    `lockXaddAdr` (adapter step with actual length and next RIP),
    `lockXaddGeholt` (fetched step from actual executable memory),
    `adrLade` / `adrSpeichere` (generic checked access),
    `adrPruefe` (ordered admission, lawful with `fussZugelassen`),
    and the `LockEreignis` footprints (`Fuss` byte lists) for
    per-access grouping. No other definition here is load-bearing
    for consumers. -/

/- CUTS:
    Proved here: ordered admission (`adrPruefe`) lawful with the
    accepted `fussZugelassen`, with canonical/wrap-before-permission
    order; generic addressed load/store bound to the actual length
    and next RIP, with success/refusal equations and the pilot bridge
    (`adrLade_basisForm_pilot`); an extended LOCK XADD decoder over
    full selected tails reusing `rexLockBits` and `parseAdrTail`,
    disjoint from the accepted producer in both directions on closed
    bytes; the adapter execution mirroring the accepted
    `lockSchrittVoll` XADD arm, with the lawful-adapter equation on
    the canonical aligned base-plus-displacement subset; fetched
    joint memory-changing witnesses for a scaled SIB XADD and a
    RIP-relative XADD, plus a pure RIP-relative observation;
    negative probes (register-direct, truncated SIB/disp, missing
    LOCK, legacy prefix, pilot tails both ways, zero length, buffer
    order, noncanonical order, read fault, the noncanonical hole
    under full rights); cross-form alias pins, including both
    witness spellings of 8200.
    NOT proved here, and not claimed:
    - No silicon correspondence: byte shapes follow the clone-local
      Intel SDM 325462-093US (Vol. 1 Sections 3.7.5/3.7.5.1, LOCK
      prefix and XADD entries) as stated contracts; no socket,
      stepping or vendor-difference claim.
    - No X-extended (REX.X = 1) high-index scaled LOCK rows: the
      decoder reuses the accepted canonical `rexLockBits` subset, so
      `r9`-as-index LOCK tails stay refused here; a follow-up owns
      them with their own round trips.
    - No LOCK CMPXCHG through full forms and no generic round trip
      over all register pairs: each shape class is pinned on closed
      bytes, as in the accepted producers.
    - No TSO/GX bridge: events carry sequential `Fuss` byte lists as
      grouping hooks; tearing, visibility and interleaving stay OPEN.
    - No source correspondence, no ABI/loader/entry/budget claim, no
      whole-image or source-to-byte validation claim.
-/

#print axioms adrPruefe_gleich_fuss
#print axioms adrPruefe_ordnung_kanonisch
#print axioms adrPruefe_ordnung_umbruch
#print axioms adrLade_erfolg
#print axioms adrLade_verweigert_fehler
#print axioms adrSpeichere_erfolg
#print axioms adrLade_basisForm_pilot
#print axioms adrPruefe_schreib_frei
#print axioms adrPruefe_schreib_verweigert
#print axioms decoder_weist_pilot_basis_zurueck
#print axioms decoder_weist_pilot_sib_zurueck
#print axioms produzent_weist_skaliert_zurueck
#print axioms decoder_nimmt_skaliert
#print axioms lockXaddAdr_basisForm
#print axioms lockXaddAdr_erfolg
#print axioms lockXaddGeholt_zeuge
#print axioms decoder_nimmt_rip
#print axioms produzent_weist_rip_zurueck
#print axioms ripForm_beobachtung
#print axioms lockRipGeholt_zeuge
#print axioms decoder_weist_mod3_zurueck
#print axioms decoder_weist_ohne_sib_zurueck
#print axioms decoder_weist_kurze_disp8_zurueck
#print axioms decoder_weist_ohne_lock_zurueck
#print axioms decoder_weist_vorsatz_zurueck
#print axioms lockXaddAdr_laenge_verweigert
#print axioms lockXaddAdr_puffer_zuerst
#print axioms lockXaddAdr_unkanonisch
#print axioms lockXaddAdr_lesefehler
#print axioms adrPruefe_loch
#print axioms adress_alias_pin
#print axioms adress_formen_alias_pin

end Gabbro.Grammatik.X86
