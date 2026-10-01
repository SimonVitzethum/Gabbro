/-
  File:      Grammatik/X86/NarrowOps.lean
  Subject:   8/16/32-bit narrow load/store/move helpers over the canonical vocabulary.

  Lane 335 (wave A1): width-explicit narrow register merge, zero/sign
  extension, profile admission Bool and narrow state helpers. Reuses the
  canonical `Register`/`Breite`/`Flags`/`Speicher`/`Zustand` (`Typen`),
  masks and extension (`Wort`), width-indexed memory (`Speicher`) and the
  pre-state address and register-file helpers (`Ausfuehrung`: `effAddr`,
  `regSet`). Adds no `Befehl` constructor, no encoding, no decoder claim
  (the pilot codec admits 64-bit forms only, BYTE-PILOT.md) and no second
  evaluator of the existing 14 forms: the 64-bit case of every helper is
  definitionally the existing 64-bit operation. Narrow ALU flag snapshots
  are absent by construction (booked, not inherited): every helper below
  preserves the pre-state flags exactly like architectural MOV.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher
import Grammatik.X86.Ausfuehrung

namespace Gabbro.Grammatik.X86

/-- Narrow register merge with architectural upper-bit discipline: 8/16-bit
    writes preserve the unaffected upper bits, a 32-bit write clears the
    upper 32 bits (it carries exactly the low 32-bit truncation), and a
    64-bit write is the full word. Widths are explicit at every use. -/
def mergeRegNarrow (b : Breite) (oldVal newVal : Wort) : Wort :=
  match b with
  | .b8 => (oldVal &&& ~~~(maske .b8)) ||| trunc .b8 newVal
  | .b16 => (oldVal &&& ~~~(maske .b16)) ||| trunc .b16 newVal
  | .b32 => trunc .b32 newVal
  | .b64 => newVal

/-- A 64-bit narrow merge is the full word (the existing 64-bit behaviour). -/
theorem mergeRegNarrow_b64 (oldVal newVal : Wort) :
    mergeRegNarrow .b64 oldVal newVal = newVal := rfl

/-- A 32-bit narrow merge clears the upper 32 bits by construction. -/
theorem mergeRegNarrow_b32 (oldVal newVal : Wort) :
    mergeRegNarrow .b32 oldVal newVal = trunc .b32 newVal := rfl

/-- Explicit extension mode: every narrow load names how the value grows.
    Unknown source signedness never picks one silently (see `SignKind`). -/
inductive ExtendMode where
  | zero | sign
  deriving DecidableEq, Repr

/-- Width-explicit extension reusing the canonical `trunc`/`sext` of `Wort`. -/
def extendNarrow (e : ExtendMode) (b : Breite) (v : Wort) : Wort :=
  match e with
  | .zero => trunc b v
  | .sign => sext b v

/-- Zero extension is truncation. -/
theorem extendNarrow_zero (b : Breite) (v : Wort) :
    extendNarrow .zero b v = trunc b v := rfl

/-- Sign extension reuses the canonical `sext`. -/
theorem extendNarrow_sign (b : Breite) (v : Wort) :
    extendNarrow .sign b v = sext b v := rfl

/-- Masking the low `k` bits is reduction modulo `2^k` (pure Nat fact). -/
theorem narrowMaskMod (n k : Nat) : (n &&& (2 ^ k - 1)) = n % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  exact Bool.and_comm _ _

/-- Canonical truncation is reduction modulo the width modulus. -/
theorem narrowTruncMod (b : Breite) (w : Wort) :
    (trunc b w).toNat = w.toNat % 2 ^ b.bits := by
  cases b with
  | b8 =>
    show (trunc .b8 w).toNat = w.toNat % 2 ^ 8
    have hff : (0xFF : Wort).toNat = 2 ^ 8 - 1 := by decide
    simp only [trunc, maske]
    rw [BitVec.toNat_and, hff, narrowMaskMod]
  | b16 =>
    show (trunc .b16 w).toNat = w.toNat % 2 ^ 16
    have hff : (0xFFFF : Wort).toNat = 2 ^ 16 - 1 := by decide
    simp only [trunc, maske]
    rw [BitVec.toNat_and, hff, narrowMaskMod]
  | b32 =>
    show (trunc .b32 w).toNat = w.toNat % 2 ^ 32
    have hff : (0xFFFFFFFF : Wort).toNat = 2 ^ 32 - 1 := by decide
    simp only [trunc, maske]
    rw [BitVec.toNat_and, hff, narrowMaskMod]
  | b64 =>
    show (trunc .b64 w).toNat = w.toNat % 2 ^ 64
    have hff : (0xFFFFFFFFFFFFFFFF : Wort).toNat = 2 ^ 64 - 1 := by decide
    simp only [trunc, maske]
    rw [BitVec.toNat_and, hff, narrowMaskMod]

/-- Every zero-extended narrow value fits its width. -/
theorem extendNarrow_zero_fits (b : Breite) (v : Wort) :
    (extendNarrow .zero b v).toNat < 2 ^ b.bits := by
  simp only [extendNarrow]
  rw [narrowTruncMod]
  exact Nat.mod_lt _ (by cases b <;> decide)

/-- A 32-bit merge fits 32 bits: the upper half is cleared. -/
theorem mergeRegNarrow_b32_fits (oldVal newVal : Wort) :
    (mergeRegNarrow .b32 oldVal newVal).toNat < 2 ^ 32 := by
  rw [mergeRegNarrow_b32 oldVal newVal, narrowTruncMod]
  exact Nat.mod_lt _ (by decide)

/-- Pinned 8-bit merge: the low byte is taken, the upper bits are kept. -/
theorem probe_mergeRegNarrow_8 :
    mergeRegNarrow .b8 0xABCDEF1234567890 0x11 = 0xABCDEF1234567811 := by
  decide

/-- Pinned 16-bit merge: the low half is taken, the upper bits are kept. -/
theorem probe_mergeRegNarrow_16 :
    mergeRegNarrow .b16 0xABCDEF1234567890 0x1122 = 0xABCDEF1234561122 := by
  decide

/-- Pinned extensions: zero keeps, sign fills, 16-bit zero keeps. -/
theorem probe_extendNarrow :
    extendNarrow .zero .b8 0xFF = 0xFF ∧
    extendNarrow .sign .b8 0x80 = 0xFFFFFFFFFFFFFF80 ∧
    extendNarrow .zero .b16 0x8000 = 0x8000 := by
  decide

/-- Width alignment: the address is a multiple of the width in bytes.
    This is a profile/validator admission check, NOT a hardware fault:
    ordinary x86 loads and stores allow many unaligned accesses. -/
def isAligned (a : Adresse) (b : Breite) : Bool :=
  a.toNat % b.bytes == 0

/-- Carrier crossing: the access does not fit one 8-byte carrier cell.
    A 64-bit covering access over narrow carriers is overlap, never a
    narrow access. -/
def crossesCarrier (a : Adresse) (b : Breite) : Bool :=
  decide ((a.toNat / 8) != ((a.toNat + b.bytes - 1) / 8))

/-- Narrow profile admission: alignment, single-carrier footprint and the
    canonical byte permissions. `writes := true` checks write permission,
    otherwise read permission. Refusal keeps the certified scalar fallback
    (see `scalarFallbackRead`); it never invents a hardware fault. -/
def narrowAdmitted (m : Speicher) (a : Adresse) (b : Breite)
    (writes : Bool) : Bool :=
  isAligned a b && !crossesCarrier a b &&
    (if writes then schreibbarN m a b.bytes else lesbarN m a b.bytes)

/-- Admission refuses a misaligned access. -/
theorem narrowAdmitted_needsAligned (m : Speicher) (a : Adresse)
    (b : Breite) (writes : Bool) (h : isAligned a b = false) :
    narrowAdmitted m a b writes = false := by
  simp [narrowAdmitted, h]

/-- Admission refuses a carrier-crossing access. -/
theorem narrowAdmitted_needsCarrier (m : Speicher) (a : Adresse)
    (b : Breite) (writes : Bool) (h : crossesCarrier a b = true) :
    narrowAdmitted m a b writes = false := by
  simp [narrowAdmitted, h]

/-- Admission refuses a load without read permission. -/
theorem narrowAdmitted_needsReadable (m : Speicher) (a : Adresse)
    (b : Breite) (h : lesbarN m a b.bytes = false) :
    narrowAdmitted m a b false = false := by
  simp [narrowAdmitted, h]

/-- Admission refuses a store without write permission. -/
theorem narrowAdmitted_needsWritable (m : Speicher) (a : Adresse)
    (b : Breite) (h : schreibbarN m a b.bytes = false) :
    narrowAdmitted m a b true = false := by
  simp [narrowAdmitted, h]

/-- The fully permissive witness memory grants every read byte. -/
theorem permReadable (a : Adresse) (n : Nat) :
    lesbarN zeugenSpeicher a n = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold lesbarN
    rw [ih]
    rfl

/-- The fully permissive witness memory grants every written byte. -/
theorem permWritable (a : Adresse) (n : Nat) :
    schreibbarN zeugenSpeicher a n = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold schreibbarN
    rw [ih]
    rfl

/-- Pinned admission: an aligned single-carrier load is admitted. -/
theorem probe_narrowAdmitted_ok :
    narrowAdmitted zeugenSpeicher (BitVec.ofNat 64 8192) .b32 false = true := by
  decide

/-- Pinned refusal: a misaligned load is refused. -/
theorem probe_narrowAdmitted_unaligned :
    narrowAdmitted zeugenSpeicher (BitVec.ofNat 64 8193) .b32 false = false := by
  decide

/-- Pinned carrier check: bytes 6..9 cross a carrier, 8192..8195 do not. -/
theorem probe_crossesCarrier_pin :
    crossesCarrier (BitVec.ofNat 64 6) .b32 = true ∧
    crossesCarrier (BitVec.ofNat 64 8192) .b32 = false := by
  decide

/-- Narrow load with explicit width: the addressed bytes come from the
    canonical width-indexed read, the destination takes them through the
    architectural merge. Flags are preserved exactly like architectural
    MOV; RIP is unchanged (lengths come from decoding only, and no narrow
    decode exists yet). -/
def loadNarrow (s : Zustand) (b : Breite) (dst : Register)
    (a : Adresse) : Option Zustand :=
  match readBreite s.speicher b a with
  | some v => some ({ s with register := regSet s.register dst (mergeRegNarrow b (s.register dst) v) })
  | none => none

/-- Narrow store with explicit width: the low bytes of the source register
    go through the canonical width-indexed write (mask discipline: only
    the addressed low bytes change). Registers, flags and RIP are kept. -/
def storeNarrow (s : Zustand) (b : Breite) (a : Adresse)
    (src : Register) : Option Zustand :=
  match writeBreite s.speicher b a (trunc b (s.register src)) with
  | some m => some ({ s with speicher := m })
  | none => none

/-- Narrow register move with explicit width and the architectural merge.
    Flags and memory are preserved. -/
def moveNarrow (s : Zustand) (b : Breite) (dst src : Register) : Zustand :=
  { s with register := regSet s.register dst (mergeRegNarrow b (s.register dst) (s.register src)) }

/-- Extended narrow load with explicit source and destination widths: the
    source bytes are extended at the SOURCE width, then merged into the
    destination slot at the DESTINATION width. Only a narrower source
    into a wider destination is a hardware move-with-extension form
    (see `extendFormOk`); the function itself stays total. -/
def loadNarrowExtend (s : Zustand) (bsrc bdst : Breite) (e : ExtendMode)
    (dst : Register) (a : Adresse) : Option Zustand :=
  match readBreite s.speicher bsrc a with
  | some v => some ({ s with register := regSet s.register dst (mergeRegNarrow bdst (s.register dst) (extendNarrow e bsrc v)) })
  | none => none

/-- Extension-form gate: the source width must be strictly narrower than
    the destination width. A same- or wider-source "extension" is refused
    by the profile; the plain `loadNarrow` covers equal widths. -/
def extendFormOk (bsrc bdst : Breite) : Bool :=
  bsrc.bytes < bdst.bytes

/-- A successful narrow load lands the merged value in the destination. -/
theorem loadNarrow_success (s : Zustand) (b : Breite) (dst : Register)
    (a : Adresse) (v : Wort)
    (hread : readBreite s.speicher b a = some v) :
    loadNarrow s b dst a =
      some ({ s with register := regSet s.register dst (mergeRegNarrow b (s.register dst) v) }) := by
  unfold loadNarrow
  simp [hread]

/-- A failed narrow read is an explicit refusal. -/
theorem loadNarrow_refused (s : Zustand) (b : Breite) (dst : Register)
    (a : Adresse) (hread : readBreite s.speicher b a = none) :
    loadNarrow s b dst a = none := by
  unfold loadNarrow
  simp [hread]

/-- A successful narrow store carries the masked source word into memory. -/
theorem storeNarrow_success (s : Zustand) (b : Breite) (a : Adresse)
    (src : Register) (m : Speicher)
    (hwr : writeBreite s.speicher b a (trunc b (s.register src)) = some m) :
    storeNarrow s b a src = some ({ s with speicher := m }) := by
  unfold storeNarrow
  simp [hwr]

/-- A failed narrow write is an explicit refusal. -/
theorem storeNarrow_refused (s : Zustand) (b : Breite) (a : Adresse)
    (src : Register)
    (hwr : writeBreite s.speicher b a (trunc b (s.register src)) = none) :
    storeNarrow s b a src = none := by
  unfold storeNarrow
  simp [hwr]

/-- A successful extended load merges the source-extended value. -/
theorem loadNarrowExtend_success (s : Zustand) (bsrc bdst : Breite)
    (e : ExtendMode) (dst : Register) (a : Adresse) (v : Wort)
    (hread : readBreite s.speicher bsrc a = some v) :
    loadNarrowExtend s bsrc bdst e dst a =
      some ({ s with register := regSet s.register dst (mergeRegNarrow bdst (s.register dst) (extendNarrow e bsrc v)) }) := by
  unfold loadNarrowExtend
  simp [hread]

/-- Narrow loads preserve the flags: no narrow flag snapshot is produced. -/
theorem loadNarrow_flags (s s' : Zustand) (b : Breite) (dst : Register)
    (a : Adresse) (v : Wort) (hread : readBreite s.speicher b a = some v)
    (h : loadNarrow s b dst a = some s') :
    s'.flags = s.flags := by
  rw [loadNarrow_success s b dst a v hread] at h
  cases h
  rfl

/-- Narrow loads change no memory byte. -/
theorem loadNarrow_memory (s s' : Zustand) (b : Breite) (dst : Register)
    (a : Adresse) (v : Wort) (hread : readBreite s.speicher b a = some v)
    (h : loadNarrow s b dst a = some s') :
    s'.speicher = s.speicher := by
  rw [loadNarrow_success s b dst a v hread] at h
  cases h
  rfl

/-- Narrow stores preserve the flags. -/
theorem storeNarrow_flags (s s' : Zustand) (b : Breite) (a : Adresse)
    (src : Register) (m : Speicher)
    (hwr : writeBreite s.speicher b a (trunc b (s.register src)) = some m)
    (h : storeNarrow s b a src = some s') :
    s'.flags = s.flags := by
  rw [storeNarrow_success s b a src m hwr] at h
  cases h
  rfl

/-- Narrow stores keep every register. -/
theorem storeNarrow_regs (s s' : Zustand) (b : Breite) (a : Adresse)
    (src q : Register) (m : Speicher)
    (hwr : writeBreite s.speicher b a (trunc b (s.register src)) = some m)
    (h : storeNarrow s b a src = some s') :
    s'.register q = s.register q := by
  rw [storeNarrow_success s b a src m hwr] at h
  cases h
  rfl

/-- Narrow register moves preserve the flags. -/
theorem moveNarrow_flags (s : Zustand) (b : Breite) (dst src : Register) :
    (moveNarrow s b dst src).flags = s.flags := rfl

/-- Narrow register moves change no memory. -/
theorem moveNarrow_memory (s : Zustand) (b : Breite) (dst src : Register) :
    (moveNarrow s b dst src).speicher = s.speicher := rfl

/-- The 64-bit narrow move is the plain register move. -/
theorem moveNarrow_b64 (s : Zustand) (dst src : Register) :
    moveNarrow s .b64 dst src = { s with register := regSet s.register dst (s.register src) } := by
  unfold moveNarrow
  rw [mergeRegNarrow_b64]

/-- The 64-bit narrow load is the existing 64-bit load: no extension, no
    merge, definitionally the canonical read. This is exactly how the one
    target semantics is extended, not a duplicated evaluator. -/
theorem loadNarrow_b64_isRead64 (s : Zustand) (dst : Register)
    (a : Adresse) (v : Wort) (hread : read64 s.speicher a = some v) :
    loadNarrow s .b64 dst a =
      some ({ s with register := regSet s.register dst v }) := by
  have hb : readBreite s.speicher .b64 a = some v := by
    rw [readBreite_b64]
    exact hread
  rw [loadNarrow_success s .b64 dst a v hb, mergeRegNarrow_b64]

/-- The 64-bit narrow store is the existing 64-bit store. -/
theorem storeNarrow_b64_isWrite64 (s : Zustand) (a : Adresse)
    (src : Register) (m : Speicher)
    (hwr : write64 s.speicher a (s.register src) = some m) :
    storeNarrow s .b64 a src = some ({ s with speicher := m }) := by
  have hb : writeBreite s.speicher .b64 a (trunc .b64 (s.register src)) =
      some m := by
    rw [writeBreite_b64, trunc_b64]
    exact hwr
  exact storeNarrow_success s .b64 a src m hb

/-- A successful 32-bit narrow store changes nothing outside its four bytes
    (reuses the canonical frame). -/
theorem storeNarrow_frame_b32 (s s' : Zustand) (a x : Adresse)
    (src : Register) (m : Speicher)
    (hwr : writeBreite s.speicher .b32 a (trunc .b32 (s.register src)) =
      some m)
    (hstep : storeNarrow s .b32 a src = some s')
    (hout : ∀ k : Nat, k < 4 → x ≠ addrOff a k) :
    s'.speicher.bytes x = s.speicher.bytes x := by
  have h32 : write32 s.speicher a (trunc .b32 (s.register src)) = some m :=
    hwr
  rw [storeNarrow_success s .b32 a src m hwr] at hstep
  cases hstep
  exact write32_rahmen s.speicher m a x _ h32 hout

/-- A successful 32-bit narrow store reads back its low 32 bits. -/
theorem storeNarrow_readback_b32 (s : Zustand) (a : Adresse)
    (src : Register) (m : Speicher)
    (hwr : writeBreite s.speicher .b32 a (trunc .b32 (s.register src)) =
      some m)
    (hrd : lesbarN s.speicher a 4 = true) :
    readBreite m .b32 a =
      some (BitVec.ofNat 64 ((trunc .b32 (s.register src)).toNat %
        4294967296)) := by
  have h32 : write32 s.speicher a (trunc .b32 (s.register src)) = some m :=
    hwr
  have h := read32_nach_write32 s.speicher m a
    (trunc .b32 (s.register src)) h32 hrd
  have hrb : readBreite m .b32 a = read32 m a := rfl
  rw [hrb]
  exact h

/-- Narrow load through base plus displacement, evaluated from the
    pre-state register file (reuses `effAddr`, never the post-state). -/
def loadNarrowAtBase (s : Zustand) (b : Breite) (dst base : Register)
    (disp : BitVec 32) : Option Zustand :=
  loadNarrow s b dst (effAddr s base disp)

/-- The base form evaluates its address from the pre-state. -/
theorem loadNarrowAtBase_eq (s : Zustand) (b : Breite) (dst base : Register)
    (disp : BitVec 32) :
    loadNarrowAtBase s b dst base disp =
      loadNarrow s b dst (effAddr s base disp) := rfl

/-- Narrow store through base plus displacement from the pre-state. -/
def storeNarrowAtBase (s : Zustand) (b : Breite) (base src : Register)
    (disp : BitVec 32) : Option Zustand :=
  storeNarrow s b (effAddr s base disp) src

/-- The base store form evaluates its address from the pre-state. -/
theorem storeNarrowAtBase_eq (s : Zustand) (b : Breite) (base src : Register)
    (disp : BitVec 32) :
    storeNarrowAtBase s b base src disp =
      storeNarrow s b (effAddr s base disp) src := rfl

/-- Source signedness as seen by the narrow profile: unknown signedness
    keeps the loud `narrow` guard instead of silently picking an
    extension. Widths stay explicit; nothing is inferred. -/
inductive SignKind where
  | signed | unsigned | unknown
  deriving DecidableEq, Repr

/-- Loud narrow guard: unknown signedness demands the check. -/
def narrowGuard (z : SignKind) : Bool :=
  match z with
  | .unknown => true
  | _ => false

/-- Unknown signedness keeps the guard. -/
theorem narrowGuard_unknown : narrowGuard .unknown = true := rfl

/-- Known signedness needs no guard. -/
theorem narrowGuard_signed : narrowGuard .signed = false := rfl

/-- Known unsignedness needs no guard. -/
theorem narrowGuard_unsigned : narrowGuard .unsigned = false := rfl

/-- Extension is refused unless the source is strictly narrower. -/
theorem extendFormNeedsNarrower (bsrc bdst : Breite)
    (h : decide (bsrc.bytes < bdst.bytes) = false) :
    extendFormOk bsrc bdst = false := by
  simp [extendFormOk, h]

/-- Pinned extension forms: byte to 32 bits extends, the rest is refused. -/
theorem probe_extendFormOk :
    extendFormOk .b8 .b32 = true ∧ extendFormOk .b16 .b64 = true ∧
    extendFormOk .b32 .b8 = false ∧ extendFormOk .b64 .b64 = false := by
  decide

/-- Certified scalar fallback, one byte: permission alone answers. -/
theorem scalarFallbackRead8 (m : Speicher) (a : Adresse)
    (h : lesbarN m a 1 = true) :
    readBreite m .b8 a = some (BitVec.ofNat 64 (m.bytes a).toNat) := by
  unfold readBreite read8
  simp [h]

/-- Certified scalar fallback, two bytes: permission alone answers. -/
theorem scalarFallbackRead16 (m : Speicher) (a : Adresse)
    (h : lesbarN m a 2 = true) :
    readBreite m .b16 a = some (BitVec.ofNat 64 ((m.bytes a).toNat + (m.bytes (addrOff a 1)).toNat * 256)) := by
  unfold readBreite read16
  simp [h]

/-- Certified scalar fallback, four bytes: permission alone answers. -/
theorem scalarFallbackRead32 (m : Speicher) (a : Adresse)
    (h : lesbarN m a 4 = true) :
    readBreite m .b32 a = some (BitVec.ofNat 64 ((m.bytes a).toNat + (m.bytes (addrOff a 1)).toNat * 256 + (m.bytes (addrOff a 2)).toNat * 65536 + (m.bytes (addrOff a 3)).toNat * 16777216)) := by
  unfold readBreite read32
  simp [h]

/-- Certified scalar fallback, eight bytes: permission alone answers. -/
theorem scalarFallbackRead64 (m : Speicher) (a : Adresse)
    (h : lesbar8 m a = true) :
    readBreite m .b64 a = some (bytesWort (readBytes m a)) := by
  unfold readBreite read64
  simp [h]

/-- Pinned fallback: at the misaligned address 8193 the 32-bit admission
    refuses, yet the scalar 32-bit read answers (permissions only). -/
theorem probe_fallback_unaligned :
    narrowAdmitted zeugenSpeicher (BitVec.ofNat 64 8193) .b32 false = false ∧
    readBreite zeugenSpeicher .b32 (BitVec.ofNat 64 8193) = some 0 := by
  constructor
  · decide
  · decide

/-- Width-indexed 32-bit read is the canonical 32-bit read. -/
theorem readBreite_b32_eq (m : Speicher) (a : Adresse) :
    readBreite m .b32 a = read32 m a := rfl

/-- Width-indexed 8-bit read is the canonical 8-bit read. -/
theorem readBreite_b8_eq (m : Speicher) (a : Adresse) :
    readBreite m .b8 a = read8 m a := rfl

/-- Width-indexed 32-bit write is the canonical 32-bit write. -/
theorem writeBreite_b32_eq (m : Speicher) (a : Adresse) (v : Wort) :
    writeBreite m .b32 a v = write32 m a v := rfl

/-- Mixed-width agreement: after a 32-bit store, the low byte reads back
    the stored word's low byte (little-endian spill/fill agreement). -/
theorem spillFillAgree (m m' : Speicher) (a : Adresse) (v : Wort)
    (hwr : write32 m a v = some m') (hrd : lesbarN m a 1 = true) :
    read8 m' a = some (BitVec.ofNat 64 (v.toNat % 256)) := by
  unfold write32 at hwr
  by_cases hc : schreibbarN m a 4 = true
  · rw [if_pos hc] at hwr
    cases hwr
    have hle : lesbarN { m with bytes := writeBytesN m a v 4 } a 1 = true := by
      rw [lesbarN_update]
      exact hrd
    have b0 : writeBytesN m a v 4 a = wortByte v 0 := by
      have hhit := writeBytesN_hit m a v 4 0 (by decide) (by decide)
      rwa [addrOff_null a] at hhit
    unfold read8
    rw [if_pos hle]
    congr 1
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat 64 (writeBytesN m a v 4 a).toNat).toNat = (BitVec.ofNat 64 (v.toNat % 256)).toNat
    rw [b0]
    unfold wortByte
    simp only [BitVec.toNat_ofNat]
    omega
  · rw [if_neg hc] at hwr
    cases hwr

/-- Spilled word: `0x01020304`. -/
def spillVal : Wort := BitVec.ofNat 64 0x01020304

/-- The spilled word fits 32 bits, so masking keeps it. -/
theorem spillVal_trunc : trunc .b32 spillVal = spillVal := by
  decide

/-- The spilled word's low byte is `0x04`. -/
theorem spillVal_low : spillVal.toNat % 256 = 4 := by
  decide

/-- Witness register file: the spill value on every register. -/
def spillRegFile : Register → Wort := fun _ => spillVal

/-- Witness flags: nothing set. -/
def spillFlags : Flags :=
  { cf := false, pf := true, af := some false, zf := false, sf := false, of := false }

/-- Witness start state: spill value live, code at 4096, clean memory. -/
def spillState : Zustand :=
  { register := spillRegFile, flags := spillFlags, rip := BitVec.ofNat 64 4096, speicher := zeugenSpeicher }

/-- The witness memory after the aligned 32-bit spill at address 8192. -/
def spillAfter : Speicher :=
  { zeugenSpeicher with bytes := writeBytesN zeugenSpeicher (BitVec.ofNat 64 8192) spillVal 4 }

/-- Aligned mixed-width spill/fill round-trip with a real memory change:
    the 32-bit spill at 8192 goes through `storeNarrow`, fills back at
    32 bits through `loadNarrow`, agrees at 8 bits (little-endian low
    byte `0x04`), and observably changes memory. -/
theorem spillFillWitness :
    ∃ (s' : Zustand) (w32 : Wort),
      storeNarrow spillState .b32 (BitVec.ofNat 64 8192) Register.rax = some s' ∧
      loadNarrow s' .b32 Register.rbx (BitVec.ofNat 64 8192) = some ({ s' with register := regSet s'.register Register.rbx (mergeRegNarrow .b32 (s'.register Register.rbx) w32) }) ∧
      readBreite s'.speicher .b8 (BitVec.ofNat 64 8192) = some (BitVec.ofNat 64 4) ∧
      w32 = BitVec.ofNat 64 (spillVal.toNat % 4294967296) ∧
      s'.speicher.bytes (BitVec.ofNat 64 8192) ≠ spillState.speicher.bytes (BitVec.ofNat 64 8192) := by
  have hreg : spillState.register Register.rax = spillVal := rfl
  have hwr : writeBreite zeugenSpeicher .b32 (BitVec.ofNat 64 8192) (trunc .b32 (spillState.register Register.rax)) = some spillAfter := by
    rw [hreg, spillVal_trunc, writeBreite_b32_eq]
    unfold write32
    have hc : schreibbarN zeugenSpeicher (BitVec.ofNat 64 8192) 4 = true := permWritable _ _
    rw [if_pos hc]
    rfl
  have hwr32 : write32 zeugenSpeicher (BitVec.ofNat 64 8192) spillVal = some spillAfter := by
    have hcopy := hwr
    rw [hreg, spillVal_trunc, writeBreite_b32_eq] at hcopy
    exact hcopy
  have hread0 := storeNarrow_readback_b32 spillState (BitVec.ofNat 64 8192) Register.rax spillAfter hwr (permReadable _ _)
  rw [hreg, spillVal_trunc] at hread0
  have hagree := spillFillAgree zeugenSpeicher spillAfter (BitVec.ofNat 64 8192) spillVal hwr32 (permReadable _ _)
  rw [spillVal_low] at hagree
  have hagreeB : readBreite spillAfter .b8 (BitVec.ofNat 64 8192) = some (BitVec.ofNat 64 4) := by
    rw [readBreite_b8_eq]
    exact hagree
  have hchanged : spillAfter.bytes (BitVec.ofNat 64 8192) ≠ zeugenSpeicher.bytes (BitVec.ofNat 64 8192) := by
    have hhit := writeBytesN_hit zeugenSpeicher (BitVec.ofNat 64 8192) spillVal 4 0 (by decide) (by decide)
    rw [addrOff_null] at hhit
    show writeBytesN zeugenSpeicher (BitVec.ofNat 64 8192) spillVal 4 (BitVec.ofNat 64 8192) ≠ BitVec.ofNat 8 0
    rw [hhit]
    decide
  refine ⟨{ spillState with speicher := spillAfter }, BitVec.ofNat 64 (spillVal.toNat % 4294967296), ?_, ?_, ?_, rfl, ?_⟩
  · exact storeNarrow_success spillState .b32 (BitVec.ofNat 64 8192) Register.rax spillAfter hwr
  · exact loadNarrow_success _ .b32 _ _ _ hread0
  · exact hagreeB
  · show spillAfter.bytes (BitVec.ofNat 64 8192) ≠ spillState.speicher.bytes (BitVec.ofNat 64 8192)
    exact hchanged

/- CUTS:
    Proved here: width-explicit 8/16/32-bit register merge with the
    architectural upper-bit discipline (32-bit clearing generic, 8/16-bit
    preservation pinned concretely), zero/sign extension reusing the
    canonical `trunc`/`sext` with generic fit facts, the truncation
    bridge, profile admission (`narrowAdmitted`) with generic alignment,
    carrier and permission refusals plus concrete pins, narrow
    load/store/move state helpers reusing the canonical width-indexed
    memory (the 64-bit case is definitionally the existing 64-bit
    operation, not a duplicated evaluator), MOV flag preservation (no
    narrow flag snapshot exists), pre-state base-plus-displacement
    addressing, 32-bit frame and read-back reuse, the loud signedness
    guard, the extension-form gate, permission-only scalar fallbacks with
    a pinned unaligned-fallback probe, and the aligned mixed-width
    spill/fill witness with a real memory change.
    NOT proved here, and not claimed:
    - No narrow encoding or decoding: no `Befehl` constructor is added
      and no codec claim is made (the pilot codec admits 64-bit forms
      only, BYTE-PILOT.md; REX/modrm patterns were inspected as context).
    - No narrow ALU flag snapshots: helpers preserve flags like MOV; the
      generic 8/16-bit merge upper-preservation identity is pinned
      concretely (`probe_mergeRegNarrow_8/16`), its fully generic BitVec
      form stays open.
    - No atomicity claim for multi-byte accesses under concurrency: every
      fact here is sequential over one `Speicher`; per-access TSO
      granularity, alignment/tearing correspondence and the GX refinement
      stay with the TSO bridge (lanes 274/284, OPEN).
    - No source correspondence: nothing here speaks about Gabbro source
      ranges, contracts, duties or lowering (bridge lane 277's business);
      the shared IR of lane 287 is PENDING and no substitute is invented.
    - No hardware verification: alignment, carrier and mask rules are
      STATED executable profile semantics, not verified against silicon.
    - No cost or time transfer: no cycle or latency claim is made.
    - RIP is unchanged by the narrow helpers: instruction lengths come
      from decoding only, and no narrow decode exists yet.
-/

#print axioms mergeRegNarrow_b64
#print axioms mergeRegNarrow_b32
#print axioms extendNarrow_zero
#print axioms extendNarrow_sign
#print axioms narrowMaskMod
#print axioms narrowTruncMod
#print axioms extendNarrow_zero_fits
#print axioms mergeRegNarrow_b32_fits
#print axioms probe_mergeRegNarrow_8
#print axioms probe_mergeRegNarrow_16
#print axioms probe_extendNarrow
#print axioms narrowAdmitted_needsAligned
#print axioms narrowAdmitted_needsCarrier
#print axioms narrowAdmitted_needsReadable
#print axioms narrowAdmitted_needsWritable
#print axioms permReadable
#print axioms permWritable
#print axioms probe_narrowAdmitted_ok
#print axioms probe_narrowAdmitted_unaligned
#print axioms probe_crossesCarrier_pin
#print axioms loadNarrow_success
#print axioms loadNarrow_refused
#print axioms storeNarrow_success
#print axioms storeNarrow_refused
#print axioms loadNarrowExtend_success
#print axioms loadNarrow_flags
#print axioms loadNarrow_memory
#print axioms storeNarrow_flags
#print axioms storeNarrow_regs
#print axioms moveNarrow_flags
#print axioms moveNarrow_memory
#print axioms moveNarrow_b64
#print axioms loadNarrow_b64_isRead64
#print axioms storeNarrow_b64_isWrite64
#print axioms storeNarrow_frame_b32
#print axioms storeNarrow_readback_b32
#print axioms loadNarrowAtBase_eq
#print axioms storeNarrowAtBase_eq
#print axioms narrowGuard_unknown
#print axioms narrowGuard_signed
#print axioms narrowGuard_unsigned
#print axioms extendFormNeedsNarrower
#print axioms probe_extendFormOk
#print axioms scalarFallbackRead8
#print axioms scalarFallbackRead16
#print axioms scalarFallbackRead32
#print axioms scalarFallbackRead64
#print axioms probe_fallback_unaligned
#print axioms readBreite_b32_eq
#print axioms readBreite_b8_eq
#print axioms writeBreite_b32_eq
#print axioms spillFillAgree
#print axioms spillVal_trunc
#print axioms spillVal_low
#print axioms spillFillWitness

end Gabbro.Grammatik.X86
