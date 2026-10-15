/-
  File:      Grammatik/X86/LockedInstructionExecution.lean
  Subject:   Final-byte LOCK XADD / LOCK CMPXCHG (64-bit word forms) and
             MFENCE: canonical decode/encode plus fetched execution over
             the canonical register/TSO state, with a proved adapter to
             the accepted `LockedOps` vocabulary.

  Lane 662: producer API for the typed W/GX consumers and
  HardwareExecution660. Manual provenance (local snapshot
  `.tmp/HARDWARE-REFERENCES/`, Intel SDM 325462-093US Sep 2026):
  LOCK prefix Vol. 2A 3-565/3-566, XADD Vol. 2D 6-27/6-28,
  CMPXCHG Vol. 2A 3-193/3-194, MFENCE Vol. 2B 4-15.
  Reuses `Zustand`/`TSOZustand`, `effAddr`, `add64`/`sub64`,
  `lockSchritt`/`casSchritt`, `mfenceZulaessig` shape and the
  `decodeExt` dispatcher (tried first, never shadowed). No second
  evaluator for older forms, no source/checker/goal change.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung
import Grammatik.X86.Codec
import Grammatik.X86.TSO
import Grammatik.X86.LockedOps
import Grammatik.X86.WordAtomicity
import Grammatik.X86.ExtendedExecution
import Grammatik.X86.FeatureProfile

namespace Gabbro.Grammatik.X86

/-- Essential locked word forms: LOCK XADD and LOCK CMPXCHG over one
    64-bit memory word (base register plus 32-bit displacement), and
    the MFENCE full fence. Narrower widths stay open (see CUTS). -/
inductive LockForm where
  | xadd64 (src base : Register) (disp : BitVec 32)
  | cmpxchg64 (src base : Register) (disp : BitVec 32)
  | mfence
  deriving DecidableEq, Repr

/-! ## 1. Parsed shapes and canonical encoding.

    Opcode facts (Intel SDM Vol. 2A/2B/2D): LOCK is byte 0xF0; XADD
    r/m64 is REX.W + 0F C1, CMPXCHG r/m64 is REX.W + 0F B1, MFENCE is
    0F AE with ModRM reg field 6 (any r/m, manual: the processor
    ignores the r/m field). LOCK with a register destination, and LOCK
    on MFENCE, are architectural #UD (XADD/CMPXCHG/LOCK entries);
    MFENCE without SSE2 is #UD (MFENCE entry, CPUID.01H:EDX.SSE2[26]).
    A failed CMPXCHG comparison still performs the destination write
    cycle (CMPXCHG entry: "never a locked read without a locked
    write"), so failure needs write permission. -/

/-- Architectural #UD grounds the byte layer parses or gates but never
    executes: LOCK on a register destination, LOCK on the fence, and a
    fence without silicon SSE2 (MFENCE entry, CPUID.01H:EDX.SSE2[26]).
    The last ground is raised by control state, never by decode. -/
inductive LockUdGrund where
  | lockAufRegister
  | lockAufZaun
  | sse2Fehlt
  deriving DecidableEq, Repr

/-- One parsed locked instruction: an admitted form, or a parsed
    architectural #UD, each with its consumed length. -/
inductive LockAnweisung where
  | ok (f : LockForm) (len : Nat)
  | ud (g : LockUdGrund) (len : Nat)
  deriving DecidableEq, Repr

/-- Canonical byte encoding of one essential locked form: the LOCK
    prefix, canonical REX.W (X=0, mirroring the pilot REX shape), the
    0F escape, the opcode, ModRM mod=2 base-plus-disp32 (SIB exactly
    when the base needs it), and MFENCE as 0F AE F0. -/
def encodeLock : LockForm → List Byte
  | .xadd64 src base d =>
    let head := [natByte 240, rexByte (regHigh src) (regHigh base),
      natByte 15, natByte 193, modrmMem (regLow src) (regLow base)]
    if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
    else head ++ leBytes32 d
  | .cmpxchg64 src base d =>
    let head := [natByte 240, rexByte (regHigh src) (regHigh base),
      natByte 15, natByte 177, modrmMem (regLow src) (regLow base)]
    if regLow base == 4 then head ++ natByte 36 :: leBytes32 d
    else head ++ leBytes32 d
  | .mfence => [natByte 15, natByte 174, natByte 240]

/-- Consumed length of one essential locked form. -/
def lockLen : LockForm → Nat
  | .xadd64 _ base _ => if regLow base == 4 then 10 else 9
  | .cmpxchg64 _ base _ => if regLow base == 4 then 10 else 9
  | .mfence => 3

/-- Every essential encoding fits the 15-byte instruction cap. -/
theorem encodeLock_len (f : LockForm) :
    1 ≤ (encodeLock f).length ∧ (encodeLock f).length ≤ 15 := by
  cases f with
  | mfence => exact show 1 ≤ 3 ∧ 3 ≤ 15 from by decide
  | xadd64 src base d =>
    simp only [encodeLock]
    split
    · exact show 1 ≤ 10 ∧ 10 ≤ 15 from by decide
    · exact show 1 ≤ 9 ∧ 9 ≤ 15 from by decide
  | cmpxchg64 src base d =>
    simp only [encodeLock]
    split
    · exact show 1 ≤ 10 ∧ 10 ≤ 15 from by decide
    · exact show 1 ≤ 9 ∧ 9 ≤ 15 from by decide

/-! ## 2. Byte decoder.

    The LOCK prefix selects the locked rows; without it these opcodes
    are not claimed here. REX must carry W=1 with X=0 (canonical
    subset); memory is mod=2 base-plus-disp32 with the SIB byte exactly
    when the base needs it. LOCK with a register destination (mod=3)
    parses to the #UD marker with length 5; LOCK before an MFENCE shape
    parses to the fence #UD marker with length 4. Truncation, wrong
    opcodes, non-canonical REX and other modes refuse with `none`. -/

/-- Accepted REX prefix bits for the locked rows: W=1, X=0, exactly
    0x48/0x49/0x4C/0x4D. -/
def rexLockBits : Byte → Option (Nat × Nat)
  | b =>
    match byteNat b with
    | 72 => some (0, 0)
    | 73 => some (0, 1)
    | 76 => some (1, 0)
    | 77 => some (1, 1)
    | _ => none

/-- The REX encoder lands in the accepted locked prefix set. -/
theorem rexLockBits_rexByte (rh bh : Nat)
    (hrh : rh < 2) (hbh : bh < 2) :
    rexLockBits (rexByte rh bh) = some (rh, bh) := by
  unfold rexLockBits rexByte
  have h1 : rh = 0 ∨ rh = 1 := by omega
  have h2 : bh = 0 ∨ bh = 1 := by omega
  cases h1 with
  | inl h0 =>
    cases h2 with
    | inl h3 => subst h0; subst h3; rfl
    | inr h3 => subst h0; subst h3; rfl
  | inr h0 =>
    cases h2 with
    | inl h3 => subst h0; subst h3; rfl
    | inr h3 => subst h0; subst h3; rfl

/-- Decode after LOCK, REX.W and the 0F escape: opcodes 193 (XADD)
    and 177 (CMPXCHG). Memory (mod=2) decodes the word form;
    register-direct (mod=3) under LOCK is the parsed #UD with the
    5-byte length; every other mode refuses. -/
def decodeLockModrm (mk : Register → Register → BitVec 32 → LockForm)
    (rh bh : Nat) : List Byte → Option (LockAnweisung × List Byte)
  | [] => none
  | m :: rest =>
    let rg := byteNat m / 8 % 8
    let qm := byteNat m % 8
    match byteNat m / 64 with
    | 3 =>
      match codeReg (rh * 8 + rg), codeReg (bh * 8 + qm) with
      | some _, some _ => some (LockAnweisung.ud .lockAufRegister 5, rest)
      | _, _ => none
    | 2 =>
      if qm == 4 then
        match rest with
        | [] => none
        | s :: rest1 =>
          if byteNat s == 36 then
            match parseLe32 rest1 with
            | some (d, rest') =>
              match codeReg (rh * 8 + rg), codeReg (bh * 8 + qm) with
              | some rs, some rb => some (LockAnweisung.ok (mk rs rb d) 10, rest')
              | _, _ => none
            | none => none
          else none
      else
        match parseLe32 rest with
        | some (d, rest') =>
          match codeReg (rh * 8 + rg), codeReg (bh * 8 + qm) with
          | some rs, some rb => some (LockAnweisung.ok (mk rs rb d) 9, rest')
          | _, _ => none
        | none => none
    | _ => none

/-- Top-level locked decode: LOCK-prefixed 64-bit XADD/CMPXCHG word
    rows, or the bare MFENCE shape (any r/m with reg field 6, per the
    manual: the processor ignores the r/m field). LOCK before an
    MFENCE shape is the parsed fence #UD. -/
def decodeLock : List Byte → Option (LockAnweisung × List Byte)
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
                match byteNat b3 with
                | 193 => decodeLockModrm .xadd64 rh bh rest3
                | 177 => decodeLockModrm .cmpxchg64 rh bh rest3
                | _ => none
            else none
        | none =>
          if byteNat b1 == 15 then
            match rest1 with
            | [] => none
            | b2 :: rest2 =>
              if byteNat b2 == 174 then
                match rest2 with
                | [] => none
                | m :: rest =>
                  if byteNat m / 8 % 8 == 6 then
                    some (LockAnweisung.ud .lockAufZaun 4, rest)
                  else none
              else none
          else none
    else if byteNat b0 == 15 then
      match rest0 with
      | [] => none
      | b1 :: rest1 =>
        if byteNat b1 == 174 then
          match rest1 with
          | [] => none
          | m :: rest =>
            if byteNat m / 8 % 8 == 6 then
              some (LockAnweisung.ok .mfence 3, rest)
            else none
        else none
    else none

/-! ## 3. Codec round trips: decode inverts encode on every row. -/

set_option maxHeartbeats 4000000 in
/-- Round trip for LOCK XADD, both SIB and non-SIB shapes. -/
theorem roundtrip_lock_xadd (src base : Register) (d : BitVec 32)
    (suffix : List Byte) :
    decodeLock (encodeLock (.xadd64 src base d) ++ suffix) =
      some (LockAnweisung.ok (.xadd64 src base d)
        (encodeLock (.xadd64 src base d)).length, suffix) := by
  cases src <;> cases base <;>
    simp [encodeLock, decodeLock, decodeLockModrm, codeReg, regCode,
      regHigh, regLow, rexByte, rexLockBits, modrmMem, leBytes32,
      parseLe32_cons]

set_option maxHeartbeats 4000000 in
/-- Round trip for LOCK CMPXCHG, both SIB and non-SIB shapes. -/
theorem roundtrip_lock_cmpxchg (src base : Register) (d : BitVec 32)
    (suffix : List Byte) :
    decodeLock (encodeLock (.cmpxchg64 src base d) ++ suffix) =
      some (LockAnweisung.ok (.cmpxchg64 src base d)
        (encodeLock (.cmpxchg64 src base d)).length, suffix) := by
  cases src <;> cases base <;>
    simp [encodeLock, decodeLock, decodeLockModrm, codeReg, regCode,
      regHigh, regLow, rexByte, rexLockBits, modrmMem, leBytes32,
      parseLe32_cons]

/-- Round trip for MFENCE. -/
theorem roundtrip_lock_mfence (suffix : List Byte) :
    decodeLock (encodeLock .mfence ++ suffix) =
      some (LockAnweisung.ok .mfence (encodeLock .mfence).length, suffix) := by
  rfl

/-- Decoding inverts encoding on every essential locked row, over any
    suffix. The decoded length is the consumed prefix length. -/
theorem roundtripLock (f : LockForm) (suffix : List Byte) :
    decodeLock (encodeLock f ++ suffix) =
      some (LockAnweisung.ok f (encodeLock f).length, suffix) := by
  cases f with
  | mfence => exact roundtrip_lock_mfence suffix
  | xadd64 src base d => exact roundtrip_lock_xadd src base d suffix
  | cmpxchg64 src base d =>
    exact roundtrip_lock_cmpxchg src base d suffix

/-- A successful locked round trip consumes exactly its prefix within
    the 15-byte cap. -/
theorem roundtripLock_len_ok (f : LockForm) (suffix : List Byte) :
    ∃ (n : Nat) (rest : List Byte),
      decodeLock (encodeLock f ++ suffix) =
        some (LockAnweisung.ok f n, rest) ∧
        n + rest.length = (encodeLock f ++ suffix).length ∧
        1 ≤ n ∧ n ≤ 15 := by
  refine ⟨(encodeLock f).length, suffix, roundtripLock f suffix, ?_, ?_, ?_⟩
  · rw [List.length_append]
  · exact (encodeLock_len f).1
  · exact (encodeLock_len f).2

/-! ## 4. Machine and full execution.

    The locked machine pairs the canonical `Zustand` (registers, flags,
    RIP, memory) with the per-core TSO store buffers. LOCK word steps
    bypass the acting core's buffer and operate on canonical memory
    exactly when that buffer is empty, reusing `read64`/`write64` (hence
    the actual permission checks) and the accepted flag operators
    `add64`/`sub64`. The fence gates on the SSE2 feature conjunction
    (`merkmalZugelassen ... .sseDoppel`: silicon AND readiness) and on
    the empty own buffer, mirroring `mfenceZulaessig`. -/

/-- The locked machine: canonical registers/flags/RIP/memory plus the
    per-core TSO store buffers. -/
structure LockMaschine where
  zu : Zustand
  puffer : Nat → List TSOEintrag

/-- Projection to the canonical TSO state: the machine memory with the
    machine buffers. -/
def toTSO (m : LockMaschine) : TSOZustand := ⟨m.zu.speicher, m.puffer⟩

/-- Execution outcome: success with its access event; the memory-access
    fault class (`speicherFehler`: failed read/write permission or page
    failure, never #UD); architectural #UD exactly where the manual
    states it (`udFehler`); profile refusal (`verweigert`: empty-buffer
    violation, misalignment, bad length, unsupported shape). Admission
    refusals are never #UD claims. -/
inductive LockAusgang where
  | ok (m : LockMaschine) (ev : LockEreignis)
  | speicherFehler
  | udFehler (g : LockUdGrund)
  | verweigert

/-- Full execution of one parsed locked instruction on core `c`. XADD
    exchanges the old word into the source register and installs the
    sum with addition flags (manual Operation/Flags). CMPXCHG compares
    against RAX: success installs the source with ZF set; failure loads
    the word into RAX with ZF cleared AND writes the word back, so the
    failure path also needs write permission (manual: "never a locked
    read without a locked write"). MFENCE needs admitted SSE2 and an
    empty own buffer and moves only RIP. -/
def lockSchrittVoll (a : LockAnweisung) (c : Nat) (m : LockMaschine)
    (hw : HwProfil) (bp : BereitProfil) : LockAusgang :=
  match a with
  | .ud g _ => .udFehler g
  | .ok f len =>
    match laengeOk len with
    | false => .verweigert
    | true =>
      match f with
      | .mfence =>
        match merkmalZugelassen hw bp .sseDoppel with
        | false => .udFehler .sse2Fehlt
        | true =>
          match m.puffer c with
          | _ :: _ => .verweigert
          | [] =>
            LockAusgang.ok ⟨{ m.zu with rip := ripNach m.zu.rip len }, m.puffer⟩
              ⟨c, [], [], none, none, false, true⟩
      | .xadd64 src base d =>
        match m.puffer c with
        | _ :: _ => .verweigert
        | [] =>
          let tgt := effAddr m.zu base d
          if ausgerichtet8 tgt then
            match read64 m.zu.speicher tgt with
            | none => .speicherFehler
            | some alt =>
              match write64 m.zu.speicher tgt
                  (alt + m.zu.register src) with
              | none => .speicherFehler
              | some mem' =>
                let r := add64 alt (m.zu.register src)
                let z1 := schrittRegister m.zu (ripNach m.zu.rip len) r.2 src alt
                let z2 := { z1 with speicher := mem' }
                LockAusgang.ok ⟨z2, m.puffer⟩
                  ⟨c, Fuss tgt, Fuss tgt, some alt,
                    some (alt + m.zu.register src), true, false⟩
          else .verweigert
      | .cmpxchg64 src base d =>
        match m.puffer c with
        | _ :: _ => .verweigert
        | [] =>
          let tgt := effAddr m.zu base d
          if ausgerichtet8 tgt then
            match read64 m.zu.speicher tgt with
            | none => .speicherFehler
            | some dest =>
              let acc := m.zu.register .rax
              let cmp := sub64 dest acc
              if dest == acc then
                match write64 m.zu.speicher tgt (m.zu.register src) with
                | none => .speicherFehler
                | some mem' =>
                  let z1 := { m.zu with rip := ripNach m.zu.rip len }
                  let z2 := { z1 with speicher := mem' }
                  let z3 := { z2 with flags := cmp.2 }
                  LockAusgang.ok ⟨z3, m.puffer⟩
                    ⟨c, Fuss tgt, Fuss tgt, some dest,
                      some (m.zu.register src), true, false⟩
              else
                match write64 m.zu.speicher tgt dest with
                | none => .speicherFehler
                | some mem' =>
                  let z1 := schrittRegister m.zu (ripNach m.zu.rip len)
                    cmp.2 .rax dest
                  let z2 := { z1 with speicher := mem' }
                  LockAusgang.ok ⟨z2, m.puffer⟩
                    ⟨c, Fuss tgt, Fuss tgt, some dest, some dest,
                      true, false⟩
          else .verweigert

/-! ## 5. Step equations: success pins the full successor. -/

/-- XADD success: the word grows by the source register, the source
    register takes the old word, flags follow the addition, RIP
    advances by the parsed length. -/
theorem lockSchrittVoll_xadd_erfolg (m : LockMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (hw : HwProfil) (bp : BereitProfil)
    (alt sval : Wort) (mem' : Speicher)
    (hbuf : m.puffer c = [])
    (hali : ausgerichtet8 (effAddr m.zu base d) = true)
    (hrd : read64 m.zu.speicher (effAddr m.zu base d) = some alt)
    (hreg : m.zu.register src = sval)
    (hok : laengeOk len = true)
    (hwr : write64 m.zu.speicher (effAddr m.zu base d) (alt + sval) =
      some mem') :
    lockSchrittVoll (.ok (.xadd64 src base d) len) c m hw bp =
      LockAusgang.ok ⟨{ schrittRegister m.zu (ripNach m.zu.rip len) (add64 alt sval).2 src alt with speicher := mem' }, m.puffer⟩
        ⟨c, Fuss (effAddr m.zu base d), Fuss (effAddr m.zu base d),
          some alt, some (alt + sval), true, false⟩ := by
  unfold lockSchrittVoll
  simp [hbuf, hali, hrd, hreg, hok, hwr]

/-- CMPXCHG success: the source installs, RAX is untouched, ZF is set
    through the comparison flags. -/
theorem lockSchrittVoll_cmpxchg_erfolg (m : LockMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (hw : HwProfil) (bp : BereitProfil)
    (dest sval : Wort) (mem' : Speicher)
    (hbuf : m.puffer c = [])
    (hali : ausgerichtet8 (effAddr m.zu base d) = true)
    (hrd : read64 m.zu.speicher (effAddr m.zu base d) = some dest)
    (hgleich : (dest == m.zu.register .rax) = true)
    (hsrc : m.zu.register src = sval)
    (hok : laengeOk len = true)
    (hwr : write64 m.zu.speicher (effAddr m.zu base d) sval = some mem') :
    lockSchrittVoll (.ok (.cmpxchg64 src base d) len) c m hw bp =
      LockAusgang.ok ⟨{ { { m.zu with rip := ripNach m.zu.rip len } with speicher := mem' } with flags := (sub64 dest (m.zu.register .rax)).2 }, m.puffer⟩
        ⟨c, Fuss (effAddr m.zu base d), Fuss (effAddr m.zu base d),
          some dest, some sval, true, false⟩ := by
  unfold lockSchrittVoll
  simp [hbuf, hali, hrd, hgleich, hsrc, hok, hwr]

/-- CMPXCHG failure: the word is written back unchanged (the manual's
    write cycle without regard to the comparison), RAX takes the word,
    ZF is cleared through the comparison flags. -/
theorem lockSchrittVoll_cmpxchg_fehlschlag (m : LockMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (hw : HwProfil) (bp : BereitProfil)
    (dest : Wort) (mem' : Speicher)
    (hbuf : m.puffer c = [])
    (hali : ausgerichtet8 (effAddr m.zu base d) = true)
    (hrd : read64 m.zu.speicher (effAddr m.zu base d) = some dest)
    (hfehl : (dest == m.zu.register .rax) = false)
    (hok : laengeOk len = true)
    (hwr : write64 m.zu.speicher (effAddr m.zu base d) dest = some mem') :
    lockSchrittVoll (.ok (.cmpxchg64 src base d) len) c m hw bp =
      LockAusgang.ok ⟨{ schrittRegister m.zu (ripNach m.zu.rip len) (sub64 dest (m.zu.register .rax)).2 .rax dest with speicher := mem' }, m.puffer⟩
        ⟨c, Fuss (effAddr m.zu base d), Fuss (effAddr m.zu base d),
          some dest, some dest, true, false⟩ := by
  unfold lockSchrittVoll
  simp [hbuf, hali, hrd, hfehl, hok, hwr]

/-- MFENCE success: only RIP advances; memory and every buffer are
    untouched and the event is fence-only. -/
theorem lockSchrittVoll_mfence_erfolg (m : LockMaschine) (c : Nat)
    (len : Nat) (hw : HwProfil) (bp : BereitProfil)
    (hzulaessig : merkmalZugelassen hw bp .sseDoppel = true)
    (hbuf : m.puffer c = [])
    (hok : laengeOk len = true) :
    lockSchrittVoll (.ok .mfence len) c m hw bp =
      LockAusgang.ok ⟨{ m.zu with rip := ripNach m.zu.rip len }, m.puffer⟩
        ⟨c, [], [], none, none, false, true⟩ := by
  unfold lockSchrittVoll
  simp [hzulaessig, hbuf, hok]

/-- A parsed #UD never executes: it answers the #UD outcome. -/
theorem lockSchrittVoll_ud (g : LockUdGrund) (len : Nat) (c : Nat)
    (m : LockMaschine) (hw : HwProfil) (bp : BereitProfil) :
    lockSchrittVoll (.ud g len) c m hw bp = .udFehler g := by
  rfl

/-- Missing SSE2 gates the fence to #UD, exactly as the manual states
    (CPUID.01H:EDX.SSE2[26] = 0). -/
theorem lockSchrittVoll_mfence_ohne_sse2 (m : LockMaschine) (c : Nat)
    (len : Nat) (hw : HwProfil) (bp : BereitProfil)
    (hok : laengeOk len = true)
    (hfehlt : merkmalZugelassen hw bp .sseDoppel = false) :
    lockSchrittVoll (.ok .mfence len) c m hw bp =
      .udFehler .sse2Fehlt := by
  unfold lockSchrittVoll
  simp [hok, hfehlt]

/-- A non-empty own buffer refuses the locked word step: profile
    admission, never a hardware fault claim. -/
theorem lockSchrittVoll_xadd_puffer_verweigert (m : LockMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32) (len : Nat)
    (hw : HwProfil) (bp : BereitProfil)
    (e : TSOEintrag) (rest : List TSOEintrag)
    (hbuf : m.puffer c = e :: rest)
    (hok : laengeOk len = true) :
    lockSchrittVoll (.ok (.xadd64 src base d) len) c m hw bp =
      .verweigert := by
  unfold lockSchrittVoll
  simp [hbuf, hok]

/-- A misaligned word refuses the locked step as an unsupported
    profile: the architecture locks misaligned fields, so this is an
    admission refusal, never a fault claim. -/
theorem lockSchrittVoll_xadd_unaligned_verweigert (m : LockMaschine)
    (c : Nat) (src base : Register) (d : BitVec 32) (len : Nat)
    (hw : HwProfil) (bp : BereitProfil)
    (hbuf : m.puffer c = [])
    (hok : laengeOk len = true)
    (hfehl : ausgerichtet8 (effAddr m.zu base d) = false) :
    lockSchrittVoll (.ok (.xadd64 src base d) len) c m hw bp =
      .verweigert := by
  unfold lockSchrittVoll
  simp [hbuf, hok, hfehl]

/-! ## 6. Adapter to the accepted LOCK vocabulary.

    The fetched word steps project onto `lockSchritt`/`casSchritt` on
    the projected TSO state. The one architectural difference is made
    explicit: the accepted `casSchritt` models a failed comparison as a
    stutter with no write, while the manual performs the destination
    write cycle regardless. The adapter proves both sides agree on the
    success path and on the observable bytes of the failure path, and
    that the failure path additionally requires full write permission
    -- exactly the observable mismatch, resolved, not assumed away. -/

/-- XADD projects onto the accepted locked add with the same words. -/
theorem lockVoll_xadd_adapter (m : LockMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32)
    (alt : Wort) (mem' : Speicher)
    (hbuf : m.puffer c = [])
    (hrd : read64 m.zu.speicher (effAddr m.zu base d) = some alt)
    (hali : ausgerichtet8 (effAddr m.zu base d) = true)
    (hwr : write64 m.zu.speicher (effAddr m.zu base d)
      (alt + m.zu.register src) = some mem') :
    ∃ ev : LockEreignis,
      lockSchritt (.xadd64 (effAddr m.zu base d) (m.zu.register src)) c
        (toTSO m) = some (⟨mem', m.puffer⟩, ev) ∧
        ev.gelesen = some alt ∧ ev.istRmw = true := by
  refine ⟨⟨c, Fuss (effAddr m.zu base d), Fuss (effAddr m.zu base d),
    some alt, some (alt + m.zu.register src), true, false⟩, ?_, rfl,
    rfl⟩
  exact lockSchritt_xadd_erfolg (toTSO m) c _ _ alt mem'
    hbuf hrd hali hwr

/-- CMPXCHG success projects onto the accepted CAS success. -/
theorem lockVoll_cmpxchg_erfolg_adapter (m : LockMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32)
    (dest : Wort) (mem' : Speicher)
    (hbuf : m.puffer c = [])
    (hrd : read64 m.zu.speicher (effAddr m.zu base d) = some dest)
    (hali : ausgerichtet8 (effAddr m.zu base d) = true)
    (hgleich : (dest == m.zu.register .rax) = true)
    (hwr : write64 m.zu.speicher (effAddr m.zu base d)
      (m.zu.register src) = some mem') :
    casSchritt (effAddr m.zu base d) (m.zu.register .rax)
      (m.zu.register src) c (toTSO m) = some (⟨mem', m.puffer⟩, true) := by
  exact casSchritt_erfolg (toTSO m) c _ _ _ dest mem'
    hbuf hrd hali hgleich hwr

/-- RESOLVED MISMATCH (failure path): the accepted `casSchritt` answers
    a failed comparison with a stutter, while this machine performs the
    manual's write-back. Both agree that no observable byte changes and
    that the accepted stutter answers `false`; the write-back
    additionally pins full write permission of the footprint -- the
    exact observable difference, proved, not assumed. -/
theorem lockVoll_cmpxchg_fehlschlag_adapter (m : LockMaschine) (c : Nat)
    (src base : Register) (d : BitVec 32)
    (dest : Wort) (mem' : Speicher)
    (hbuf : m.puffer c = [])
    (hrd : read64 m.zu.speicher (effAddr m.zu base d) = some dest)
    (hali : ausgerichtet8 (effAddr m.zu base d) = true)
    (hfehl : (dest == m.zu.register .rax) = false)
    (hwr : write64 m.zu.speicher (effAddr m.zu base d) dest = some mem') :
    casSchritt (effAddr m.zu base d) (m.zu.register .rax)
      (m.zu.register src) c (toTSO m) = some (toTSO m, false) ∧
      schreibbar8 m.zu.speicher (effAddr m.zu base d) = true ∧
      (∀ x, (∀ k : Nat, k < 8 → x ≠ addrOff (effAddr m.zu base d) k) →
        mem'.bytes x = m.zu.speicher.bytes x) := by
  refine ⟨?_, ?_, ?_⟩
  · exact casSchritt_fehlschlag (toTSO m) c _ _ _ dest
      hbuf hrd hali hfehl
  · exact write64_braucht_schreibbar m.zu.speicher _ dest mem' hwr
  · intro x haussen
    exact write64_rahmen m.zu.speicher mem' _ x dest hwr haussen

/-- MFENCE projects onto the accepted fence with the same event. -/
theorem lockVoll_mfence_adapter (m : LockMaschine) (c : Nat)
    (hbuf : m.puffer c = []) :
    lockSchritt .mfence c (toTSO m) =
      some (toTSO m, ⟨c, [], [], none, none, false, true⟩) := by
  exact lockSchritt_mfence_erfolg (toTSO m) c hbuf

/-! ## 7. Fetched layer: reuse the unified dispatcher, then lock rows.

    `decodeLockExt` tries the accepted `decodeExt` first and consults
    the locked rows only where every older decoder refuses: no older
    form is shadowed, and no lock row steals older bytes, by
    construction. Fetch reuses the canonical executable window
    (`geholt`), the 15-byte cap and the execute-permission prefix
    (`ausfuehrbarN`); the fetched step runs `lockSchrittVoll` on the
    fetched instruction only. -/

/-- Consumed length of one parsed locked instruction. -/
def lockLaenge : LockAnweisung → Nat
  | .ok _ len => len
  | .ud _ len => len

/-- Combined decode: the accepted unified dispatcher first, the locked
    rows only where it refuses. -/
def decodeLockExt : List Byte → Option (LockAnweisung × List Byte) :=
  fun bs =>
    match decodeExt bs with
    | some _ => none
    | none => decodeLock bs

/-- Where the unified dispatcher accepts, the combined decode refuses:
    older rows keep their bytes. -/
theorem decodeLockExt_aelter (bs : List Byte) (e : ExtInstr)
    (rest : List Byte) (h : decodeExt bs = some (e, rest)) :
    decodeLockExt bs = none := by
  unfold decodeLockExt
  rw [h]

/-- Where every older decoder refuses, a locked row is taken whole. -/
theorem decodeLockExt_lock (bs : List Byte) (a : LockAnweisung)
    (rest : List Byte) (h1 : decodeExt bs = none)
    (h2 : decodeLock bs = some (a, rest)) :
    decodeLockExt bs = some (a, rest) := by
  unfold decodeLockExt
  rw [h1, h2]

/-- Fetch and decode for the locked rows: the actual fetched bytes at
    `rip` through the combined decoder, with consumed-length,
    length-validity and execute-permission checks. Anything else is an
    explicit `none`. -/
def lockFetch (m : LockMaschine) : Option (LockAnweisung × List Byte) :=
  match decodeLockExt (geholt m.zu) with
  | none => none
  | some (a, rest) =>
    if lockLaenge a + rest.length == (geholt m.zu).length &&
        laengeOk (lockLaenge a) &&
        ausfuehrbarN m.zu.speicher m.zu.rip (lockLaenge a)
    then some (a, rest)
    else none

/-- One fetched locked step: fetch, decode, then `lockSchrittVoll`.
    Takes only the machine: no caller-supplied decoded value ever
    becomes a trusted fetch. -/
def lockByteschritt (m : LockMaschine) (c : Nat) (hw : HwProfil)
    (bp : BereitProfil) : LockAusgang :=
  match lockFetch m with
  | none => .verweigert
  | some (a, _) => lockSchrittVoll a c m hw bp

/-- FETCH-TO-STEP (success): the fetched step runs `lockSchrittVoll`
    on the fetched instruction. -/
theorem lockByteschritt_weiter (m : LockMaschine) (c : Nat)
    (hw : HwProfil) (bp : BereitProfil) (a : LockAnweisung)
    (rest : List Byte) (hf : lockFetch m = some (a, rest))
    (hs : lockSchrittVoll a c m hw bp = o) :
    lockByteschritt m c hw bp = o := by
  unfold lockByteschritt
  simp only [hf, hs]

/-- FETCH-TO-STEP (fetch refusal): no fetch means the profile refusal,
    never a termination claim. -/
theorem lockByteschritt_verweigert_ohne_fetch (m : LockMaschine) (c : Nat)
    (hw : HwProfil) (bp : BereitProfil) (hf : lockFetch m = none) :
    lockByteschritt m c hw bp = .verweigert := by
  unfold lockByteschritt
  simp only [hf]

/-- Outcome kind: the decidable projection used by refusal witnesses. -/
inductive LockArt where
  | ok
  | speicherFehler
  | udFehler
  | verweigert
  deriving DecidableEq, Repr

/-- Project one fetched outcome to its kind. -/
def lockArt : LockAusgang → LockArt
  | .ok _ _ => .ok
  | .speicherFehler => .speicherFehler
  | .udFehler _ => .udFehler
  | .verweigert => .verweigert

/-- Observe the RIP of a fetched outcome (`none` on non-success). -/
def lockRip : LockAusgang → Option Adresse
  | .ok m _ => some m.zu.rip
  | _ => none

/-- Observe one register of a fetched outcome (`none` on non-success). -/
def lockReg (r : Register) : LockAusgang → Option Wort
  | .ok m _ => some (m.zu.register r)
  | _ => none

/-- Observe one memory byte of a fetched outcome (`none` on non-success). -/
def lockByte (a : Adresse) : LockAusgang → Option Byte
  | .ok m _ => some (m.zu.speicher.bytes a)
  | _ => none

/-- Observe the flags of a fetched outcome (`none` on non-success). -/
def lockFlags : LockAusgang → Option Flags
  | .ok m _ => some m.zu.flags
  | _ => none

/-- Observe one 64-bit word of a fetched outcome (`none` on non-success). -/
def lockWort (a : Adresse) : LockAusgang → Option Wort
  | .ok m _ => read64 m.zu.speicher a
  | _ => none

/-! ## 8. Witnesses: decoded pins and fetched runs.

    Pins evaluate the complete fallback chain on closed bytes: the
    unified dispatcher refuses every locked row, and the locked decoder
    takes each row exactly once. Fetched witnesses run
    `lockByteschritt` from actual executable bytes. -/

/-- Witness XADD bytes: LOCK XADD [rbp+0], rax (no SIB). -/
def pinXadd : List Byte :=
  [natByte 240, natByte 72, natByte 15, natByte 193, natByte 133,
   natByte 0, natByte 0, natByte 0, natByte 0]

/-- Witness CMPXCHG bytes: LOCK CMPXCHG [rbp+0], rcx (no SIB). -/
def pinCmpxchg : List Byte :=
  [natByte 240, natByte 72, natByte 15, natByte 177, natByte 141,
   natByte 0, natByte 0, natByte 0, natByte 0]

/-- Witness MFENCE bytes. -/
def pinMfence : List Byte := [natByte 15, natByte 174, natByte 240]

/-- LOCK XADD with a register destination: parsed #UD shape. -/
def pinRegUd : List Byte :=
  [natByte 240, natByte 72, natByte 15, natByte 193, natByte 192]

/-- LOCK before MFENCE: parsed fence-#UD shape. -/
def pinZaunUd : List Byte :=
  [natByte 240, natByte 15, natByte 174, natByte 240]

/-- Pin: LOCK XADD decodes to the word form with length 9. -/
theorem pin_lock_xadd_decodiert :
    decodeLock pinXadd =
      some (LockAnweisung.ok (.xadd64 .rax .rbp 0) 9, []) := by
  decide

/-- Pin: LOCK CMPXCHG decodes to the word form with length 9. -/
theorem pin_lock_cmpxchg_decodiert :
    decodeLock pinCmpxchg =
      some (LockAnweisung.ok (.cmpxchg64 .rcx .rbp 0) 9, []) := by
  decide

/-- Pin: MFENCE decodes with length 3. -/
theorem pin_lock_mfence_decodiert :
    decodeLock pinMfence =
      some (LockAnweisung.ok .mfence 3, []) := by
  decide

/-- Pin: LOCK on a register destination parses to the #UD marker. -/
theorem pin_lock_reg_ud_decodiert :
    decodeLock pinRegUd =
      some (LockAnweisung.ud .lockAufRegister 5, []) := by
  decide

/-- Pin: LOCK before MFENCE parses to the fence-#UD marker. -/
theorem pin_lock_zaun_ud_decodiert :
    decodeLock pinZaunUd =
      some (LockAnweisung.ud .lockAufZaun 4, []) := by
  decide

/-- Pin: the unified dispatcher refuses the LOCK XADD row. -/
theorem pin_lock_ext_verweigert_xadd :
    decodeExt pinXadd = none := by
  decide

/-- Pin: the unified dispatcher refuses the LOCK CMPXCHG row. -/
theorem pin_lock_ext_verweigert_cmpxchg :
    decodeExt pinCmpxchg = none := by
  decide

/-- Pin: the unified dispatcher refuses the MFENCE row. -/
theorem pin_lock_ext_verweigert_mfence :
    decodeExt pinMfence = none := by
  decide

/-! ## 9. Witness machines and fetched facts. -/

/-- Witness code window executable: 4096..4128. -/
def lockCodeExec (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4128)

/-- Witness data window: 8192..8208. Code is deliberately NOT
    data-accessible: fetch needs execute, never data, permission. -/
def lockDataRW (a : Adresse) : Bool :=
  decide (8192 ≤ a.toNat ∧ a.toNat < 8208)

/-- Witness bytes: program at 4096, one 64-bit word `w` at 8192, zero
    elsewhere. -/
def lockZeugBytes (prog : List Byte) (w : Wort) (a : Adresse) : Byte :=
  if a.toNat < 4096 then BitVec.ofNat 8 0
  else if a.toNat < 4096 + prog.length then
    prog.getD (a.toNat - 4096) (BitVec.ofNat 8 0)
  else if a.toNat < 8192 then BitVec.ofNat 8 0
  else if a.toNat < 8200 then wortByte w (a.toNat - 8192)
  else BitVec.ofNat 8 0

/-- Witness memory: program bytes with the given execute window, data
    word with the given access windows. -/
def lockZeugSpeicher (prog : List Byte) (w : Wort)
    (exec lesbar schreibbar : Adresse → Bool) : Speicher :=
  { bytes := lockZeugBytes prog w
    lesbar := lesbar
    schreibbar := schreibbar
    ausfuehrbar := exec }

/-- Witness registers: rax, rbp and rcx named, everything else zero. -/
def lockZeugReg (raxV rbpV rcxV : Wort) : Register → Wort := fun q =>
  if q = .rax then raxV
  else if q = .rbp then rbpV
  else if q = .rcx then rcxV
  else BitVec.ofNat 64 0

/-- Witness machine: code at 4096, data word `w` at 8192, named
    registers, the given own buffer on core 0. -/
def lockZeug (prog : List Byte) (w : Wort)
    (exec lesbar schreibbar : Adresse → Bool)
    (raxV rbpV rcxV : Wort) (buf0 : List TSOEintrag) : LockMaschine :=
  ⟨{ register := lockZeugReg raxV rbpV rcxV
     flags := witnessFlags
     rip := BitVec.ofNat 64 4096
     speicher := lockZeugSpeicher prog w exec lesbar schreibbar },
   fun c => if c = 0 then buf0 else []⟩

/-- XADD witness: word 10 at 8192, delta 5 in rax, base rbp, empty buffer. -/
def zeugXadd : LockMaschine :=
  lockZeug pinXadd 10 lockCodeExec lockDataRW lockDataRW 5 8192 0 []

/-- FETCHED XADD SUCCESS: from actual bytes, the word moves 10 to 15,
    rax takes the old 10, RIP advances past the 9 bytes, flags follow
    the addition. Memory observably changes and the old value returns
    through the register. -/
theorem zeug_xadd_fetch_ok :
    lockArt (lockByteschritt zeugXadd 0 basisHw basisBereit) = .ok ∧
    lockWort (BitVec.ofNat 64 8192)
      (lockByteschritt zeugXadd 0 basisHw basisBereit) = some 15 ∧
    lockReg .rax (lockByteschritt zeugXadd 0 basisHw basisBereit) =
      some 10 ∧
    lockRip (lockByteschritt zeugXadd 0 basisHw basisBereit) =
      some (BitVec.ofNat 64 4105) ∧
    read64 zeugXadd.zu.speicher (BitVec.ofNat 64 8192) = some 10 := by
  decide

/-- CMPXCHG success witness: word 10, rax 10, new value 7 in rcx. -/
def zeugCmpxchgOk : LockMaschine :=
  lockZeug pinCmpxchg 10 lockCodeExec lockDataRW lockDataRW 10 8192 7 []

/-- FETCHED CMPXCHG SUCCESS: the word moves 10 to 7, rax keeps 10, ZF
    is set through the comparison flags. -/
theorem zeug_cmpxchg_erfolg_ok :
    lockArt (lockByteschritt zeugCmpxchgOk 0 basisHw basisBereit) = .ok ∧
    lockWort (BitVec.ofNat 64 8192)
      (lockByteschritt zeugCmpxchgOk 0 basisHw basisBereit) = some 7 ∧
    lockReg .rax (lockByteschritt zeugCmpxchgOk 0 basisHw basisBereit) =
      some 10 ∧
    lockFlags (lockByteschritt zeugCmpxchgOk 0 basisHw basisBereit) =
      some (sub64 10 10).2 := by
  decide

/-- CMPXCHG failure witness: word 10, rax 11, new value 7 in rcx. -/
def zeugCmpxchgNein : LockMaschine :=
  lockZeug pinCmpxchg 10 lockCodeExec lockDataRW lockDataRW 11 8192 7 []

/-- FETCHED CMPXCHG FAILURE: the word keeps the value 10 (written
    back), rax takes the observed 10, ZF is cleared through the
    comparison flags. -/
theorem zeug_cmpxchg_fehlschlag_ok :
    lockArt (lockByteschritt zeugCmpxchgNein 0 basisHw basisBereit) = .ok ∧
    lockWort (BitVec.ofNat 64 8192)
      (lockByteschritt zeugCmpxchgNein 0 basisHw basisBereit) = some 10 ∧
    lockReg .rax (lockByteschritt zeugCmpxchgNein 0 basisHw basisBereit) =
      some 10 ∧
    lockFlags (lockByteschritt zeugCmpxchgNein 0 basisHw basisBereit) =
      some (sub64 10 11).2 := by
  decide

/-- MFENCE witness: core 0 empty, core 1 holding a pending byte. -/
def zeugZaun : LockMaschine :=
  ⟨{ register := lockZeugReg 0 0 0
     flags := witnessFlags
     rip := BitVec.ofNat 64 4096
     speicher := lockZeugSpeicher pinMfence 0 lockCodeExec lockDataRW
       lockDataRW },
   fun c => if c = 0 then []
     else if c = 1 then
       [⟨BitVec.ofNat 64 0, BitVec.ofNat 8 7⟩]
     else []⟩

/-- FETCHED FENCE: the fence succeeds on core 0, RIP advances past the
    3 bytes, and core 1 keeps its pending store -- a local fence
    drains no foreign buffer. -/
theorem zeug_mfence_ok :
    lockArt (lockByteschritt zeugZaun 0 basisHw basisBereit) = .ok ∧
    lockRip (lockByteschritt zeugZaun 0 basisHw basisBereit) =
      some (BitVec.ofNat 64 4099) ∧
    zeugZaun.puffer 0 = [] ∧ zeugZaun.puffer 1 ≠ [] := by
  decide

/-! ## 10. Planted refusals: malformed, fault and control-state cases. -/

/-- Short execute window: 4096..4099 (cuts the opcode tail). -/
def lockCodeExecKurz (a : Adresse) : Bool :=
  decide (4096 ≤ a.toNat ∧ a.toNat < 4099)

/-- Never executable. -/
def lockCodeNie : Adresse → Bool := fun _ => false

/-- Never accessible as data. -/
def lockDataNie : Adresse → Bool := fun _ => false

/-- Silicon without SSE2: everything else like the baseline. -/
def hwOhneSse2 : HwProfil := ⟨true, true, false, true⟩

/-- One pending byte on core 0. -/
def einEintrag : List TSOEintrag :=
  [⟨BitVec.ofNat 64 0, BitVec.ofNat 8 0⟩]

/-- LOCK on a register destination is fetched as #UD, never executed. -/
theorem zeug_reg_ud_fetched :
    lockArt (lockByteschritt
      (lockZeug pinRegUd 0 lockCodeExec lockDataRW lockDataRW 0 8192 0 [])
      0 basisHw basisBereit) = .udFehler := by
  decide

/-- LOCK before MFENCE is fetched as #UD, never executed. -/
theorem zeug_zaun_ud_fetched :
    lockArt (lockByteschritt
      (lockZeug pinZaunUd 0 lockCodeExec lockDataRW lockDataRW 0 8192 0 [])
      0 basisHw basisBereit) = .udFehler := by
  decide

/-- TRUNCATED-PREFIX REFUSAL: the opcode tail cut by the execute
    boundary has no transition. -/
theorem zeug_stumpf_verweigert :
    lockArt (lockByteschritt
      (lockZeug [natByte 240, natByte 72, natByte 15] 0 lockCodeExecKurz
        lockDataRW lockDataRW 5 8192 0 [])
      0 basisHw basisBereit) = .verweigert := by
  decide

/-- EXECUTE-DENIED REFUSAL: data-accessible bytes without execute
    permission admit no fetch. -/
theorem zeug_ohne_exec_verweigert :
    lockArt (lockByteschritt
      (lockZeug pinXadd 10 lockCodeNie lockDataRW lockDataRW 5 8192 0 [])
      0 basisHw basisBereit) = .verweigert := by
  decide

/-- BUFFER REFUSAL: a pending own store refuses the locked step. -/
theorem zeug_puffer_verweigert :
    lockArt (lockByteschritt
      (lockZeug pinXadd 10 lockCodeExec lockDataRW lockDataRW 5 8192 0
        einEintrag)
      0 basisHw basisBereit) = .verweigert := by
  decide

/-- MISALIGNED REFUSAL: base 8193 is refused as an unsupported profile,
    never as a hardware fault. -/
theorem zeug_unaligned_verweigert :
    lockArt (lockByteschritt
      (lockZeug pinXadd 10 lockCodeExec lockDataRW lockDataRW 5 8193 0 [])
      0 basisHw basisBereit) = .verweigert := by
  decide

/-- SSE2-OFF REFUSAL: without admitted SSE2 the fence is #UD, exactly
    as the manual states. -/
theorem zeug_sse2_aus_ud :
    lockArt (lockByteschritt
      (lockZeug pinMfence 0 lockCodeExec lockDataRW lockDataRW 0 0 0 [])
      0 hwOhneSse2 basisBereit) = .udFehler := by
  decide

/-- READ-FAULT REFUSAL: an unreadable word has no transition, and the
    refusal is the memory class, never #UD. -/
theorem zeug_lesefehler_verweigert :
    lockArt (lockByteschritt
      (lockZeug pinXadd 10 lockCodeExec lockDataNie lockDataRW 5 8192 0 [])
      0 basisHw basisBereit) = .speicherFehler := by
  decide

/-- WRITE-BACK REFUSAL ON FAILURE: a readable but non-writable word
    refuses even the failing comparison, because the manual performs
    the destination write cycle regardless. The accepted stutter would
    answer `false` here; the byte machine demands write permission. -/
theorem zeug_schreibfehler_bei_fehlschlag :
    lockArt (lockByteschritt
      (lockZeug pinCmpxchg 10 lockCodeExec lockDataRW lockDataNie 11 8192
        7 [])
      0 basisHw basisBereit) = .speicherFehler := by
  decide

/-! ## 11. Joint witnesses: every premise together on one run. -/

/-- Joint witness for the XADD success equation and adapter: all
    guards hold together on one reached machine, the fetched run
    changes the word 10 to 15 and returns the old 10 through rax. -/
theorem lockSchrittVoll_xadd_erfolg_zeuge :
    ∃ (m : LockMaschine) (mem' : Speicher),
      m.puffer 0 = [] ∧
      effAddr m.zu .rbp 0 = BitVec.ofNat 64 8192 ∧
      ausgerichtet8 (BitVec.ofNat 64 8192) = true ∧
      read64 m.zu.speicher (BitVec.ofNat 64 8192) = some 10 ∧
      m.zu.register .rax = 5 ∧
      write64 m.zu.speicher (BitVec.ofNat 64 8192) (10 + 5) = some mem' ∧
      lockArt (lockByteschritt m 0 basisHw basisBereit) = .ok ∧
      lockWort (BitVec.ofNat 64 8192)
        (lockByteschritt m 0 basisHw basisBereit) = some 15 ∧
      lockReg .rax (lockByteschritt m 0 basisHw basisBereit) = some 10 ∧
      read64 m.zu.speicher (BitVec.ofNat 64 8192) ≠
        lockWort (BitVec.ofNat 64 8192)
          (lockByteschritt m 0 basisHw basisBereit) := by
  refine ⟨zeugXadd, _, by decide, by decide, by decide, by decide,
    by decide, rfl, zeug_xadd_fetch_ok.1, zeug_xadd_fetch_ok.2.1,
    zeug_xadd_fetch_ok.2.2.1, by decide⟩

/-- Joint witness for the failure adapter (the resolved mismatch): all
    guards hold together, the write-back pins full write permission,
    and the fetched run observes the unchanged word while loading rax. -/
theorem lockVoll_cmpxchg_fehlschlag_zeuge :
    ∃ (m : LockMaschine) (mem' : Speicher),
      m.puffer 0 = [] ∧
      read64 m.zu.speicher (BitVec.ofNat 64 8192) = some 10 ∧
      ausgerichtet8 (BitVec.ofNat 64 8192) = true ∧
      (10 == m.zu.register .rax) = false ∧
      write64 m.zu.speicher (BitVec.ofNat 64 8192) 10 = some mem' ∧
      schreibbar8 m.zu.speicher (BitVec.ofNat 64 8192) = true ∧
      lockArt (lockByteschritt m 0 basisHw basisBereit) = .ok ∧
      lockWort (BitVec.ofNat 64 8192)
        (lockByteschritt m 0 basisHw basisBereit) = some 10 ∧
      lockReg .rax (lockByteschritt m 0 basisHw basisBereit) =
        some 10 := by
  refine ⟨zeugCmpxchgNein, _, by decide, by decide, by decide, by decide,
    rfl, by decide, zeug_cmpxchg_fehlschlag_ok.1,
    zeug_cmpxchg_fehlschlag_ok.2.1,
    zeug_cmpxchg_fehlschlag_ok.2.2.1⟩

/-- Joint witness for the fence: admission holds, the fetched fence
    succeeds past its bytes while the foreign buffer stays pending. -/
theorem lockVoll_mfence_zeuge :
    ∃ (m : LockMaschine),
      m.puffer 0 = [] ∧ m.puffer 1 ≠ [] ∧
      merkmalZugelassen basisHw basisBereit .sseDoppel = true ∧
      lockArt (lockByteschritt m 0 basisHw basisBereit) = .ok ∧
      lockRip (lockByteschritt m 0 basisHw basisBereit) =
        some (BitVec.ofNat 64 4099) := by
  exact ⟨zeugZaun, by decide, by decide, by decide, zeug_mfence_ok.1,
    zeug_mfence_ok.2.1⟩

/- CUTS:
    Producer API (for HardwareExecution660 and typed W/GX consumers):
    `LockForm`, `LockAnweisung`, `LockUdGrund`, `encodeLock`, `lockLen`,
    `decodeLock`, `decodeLockExt`, `LockMaschine`, `toTSO`,
    `LockAusgang`, `lockSchrittVoll`, `lockFetch`, `lockByteschritt`,
    observers `lockArt`/`lockRip`/`lockReg`/`lockByte`/`lockWort`/
    `lockFlags`, round trips `roundtripLock`/`roundtripLock_len_ok`,
    step equations, the four `lockVoll_*_adapter` projections and the
    three `_zeuge` joints with nine planted refusals.
    Manual provenance: Intel SDM 325462-093US Sep 2026, LOCK Vol. 2A
    3-565/3-566, XADD Vol. 2D 6-27/6-28, CMPXCHG Vol. 2A 3-193/3-194,
    MFENCE Vol. 2B 4-15 (local snapshot, verified 2026-10-02).
    Proved here: canonical encode/decode with generic round trips;
    parsed #UD exactly where the manual states it (LOCK on register
    destination, LOCK on MFENCE, fence without SSE2); full execution
    with exchange/add flags, compare ZF plus write-back on failure,
    fence gating on admitted SSE2 and the empty own buffer; projection
    onto the accepted lockSchritt/casSchritt with the failure-path
    mismatch resolved (bytes agree, write permission additionally
    pinned); fetched execution from actual executable bytes through the
    combined decoder; joint memory-changing witnesses; planted
    truncation/execute/buffer/alignment/SSE2/permission refusals.
    NOT proved here, and not claimed:
    - Widths: only the 64-bit word rows (REX.W + 0F C1/B1); the 8/16/
      32-bit XADD/CMPXCHG rows and CMPXCHG8B/16B stay open.
    - Addressing: only mod=2 base-plus-disp32 with the SIB byte exactly
      when the base needs it; mod=0/1, RIP-relative, SIB index/scale
      and segment overrides stay open. Unlocked XADD/CMPXCHG and
      REX-prefixed MFENCE are refused, not modelled.
    - Alignment is a selected-profile contract (`ausgerichtet8`),
      following the accepted LOCK path: the silicon locks arbitrarily
      misaligned fields (LOCK entry), so a misaligned word is an
      admission refusal here, never a fault claim.
    - No W/GX refinement and no per-access linearisation: the bridge
      owns them. No cycle, latency, progress, fairness or retry-bound
      claim: CAS retry stays unbounded, fences order but never pace.
    - No self-modifying-code guard: a locked word overlapping live code
      bytes is not refused by this layer (OPEN).
    - MFENCE orders prior loads/stores before later ones per the manual
      description as far as the TSO model reaches; device, MMIO, DMA,
      non-temporal and speculative-fetch effects are OPEN (the manual
      notes speculation is not ordered wrt MFENCE).
    - Generic arbitrary-input disjointness beyond the pins: the
      combined decoder tries `decodeExt` first (no shadowing by
      construction), and three closed rows are proved refused by it;
      a generic `forall bs, decodeExt (encodeLock f ++ bs) = none`
      is not proved here.
    - Split-lock detection, HLE, CMPXCHG16B alignment faults and
      alignment-check (#AC) control state are OPEN.
    - No source, checker, contract, budget, duty or goal change:
      nothing here speaks about `Vertrag`, `Stmt`, duties or
      `gabbro_ziel`.
-/

#print axioms roundtripLock
#print axioms roundtripLock_len_ok
#print axioms lockSchrittVoll_xadd_erfolg
#print axioms lockSchrittVoll_cmpxchg_erfolg
#print axioms lockSchrittVoll_cmpxchg_fehlschlag
#print axioms lockSchrittVoll_mfence_erfolg
#print axioms lockSchrittVoll_ud
#print axioms lockSchrittVoll_mfence_ohne_sse2
#print axioms lockVoll_xadd_adapter
#print axioms lockVoll_cmpxchg_erfolg_adapter
#print axioms lockVoll_cmpxchg_fehlschlag_adapter
#print axioms lockVoll_mfence_adapter
#print axioms decodeLockExt_lock
#print axioms lockByteschritt_weiter
#print axioms lockSchrittVoll_xadd_erfolg_zeuge
#print axioms lockVoll_cmpxchg_fehlschlag_zeuge
#print axioms lockVoll_mfence_zeuge
#print axioms zeug_xadd_fetch_ok
#print axioms zeug_cmpxchg_erfolg_ok
#print axioms zeug_cmpxchg_fehlschlag_ok
#print axioms zeug_mfence_ok
#print axioms zeug_schreibfehler_bei_fehlschlag

end Gabbro.Grammatik.X86
