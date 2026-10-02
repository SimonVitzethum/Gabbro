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

#print axioms breite_bytes

end Gabbro.Grammatik.X86
