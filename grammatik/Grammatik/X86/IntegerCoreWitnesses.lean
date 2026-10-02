/-
  File:      Grammatik/X86/IntegerCoreWitnesses.lean
  Subject:   Source correspondence, witnesses and poison probes for the
             ten `IntegerCore.lean` forms (LEA/AND/OR/TEST/NOT/NEG/
             MOVZX×2/MOVSX×3).

  Reused, not redefined: `CoreBefehl`/`coreSchritt`/`encodeCore`/
  `decodeCore`/`leaVal`/`Scale` (`IntegerCore.lean`); `Zahl`, `Zahl.band`/
  `Zahl.bor`/`Zahl.neg`/`Zahl.add`/`Zahl.shl` (`Grammatik/Typen.lean`);
  `zahlWort`/`wortZahl` (`SourceMemory.lean`); `intWort`
  (`ScalarFloat.lean`); `andB`/`orB`/`negW`/`trunc_b64` (`Ganzzahl.lean`/
  `ShiftLogic.lean`/`Wort.lean`); `sub64_wert` (`Wort.lean`);
  `regHigh`/`regLow`/`codeReg`/`natByte`/`rexByte` (`Codec.lean`).
  Nothing here redefines a value/flag computation or a second AND/OR/
  NEG/extension evaluator.
-/
import Grammatik.X86.IntegerCore
import Grammatik.X86.SourceMemory
import Grammatik.X86.ScalarFloat
import Grammatik.Typen

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-! ## 1. SOURCE CORRESPONDENCE: AND/OR, nonnegative values in range.

    For nonnegative source values whose TYPE range fits the unsigned
    64-bit word (`h1 < 2 ^ 64`, `h2 < 2 ^ 64`), the REUSED `Zahl.band`/
    `Zahl.bor` source values equal the REUSED target `andB .b64`/
    `orB .b64` results, read back through the REUSED `zahlWort`. No
    width/sign correspondence beyond `zahlWort`'s own stated domain
    (nonnegative, below `2 ^ 64`) is claimed. -/

/-- `a.n.toNat` fits 64 bits whenever `a`'s type range does. -/
theorem zahl_toNat_lt64 {l h : Int} (h0 : 0 ≤ l) (hh : h < ((2 ^ 64 : Nat) : Int))
    (a : Zahl l h) : a.n.toNat < 2 ^ 64 := by
  have ha0 : 0 ≤ a.n := by have := a.lo_le; omega
  have ha1 : a.n < ((2 ^ 64 : Nat) : Int) := by have := a.le_hi; omega
  exact (Int.toNat_lt ha0).mpr ha1

/-- AND transfer: the REUSED `Zahl.band` value equals the REUSED
    `andB .b64` result, through `zahlWort`. -/
theorem band_zahlWort {l1 h1 l2 h2 : Int} (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
    (hw1 : h1 < ((2 ^ 64 : Nat) : Int)) (hw2 : h2 < ((2 ^ 64 : Nat) : Int))
    (a : Zahl l1 h1) (b : Zahl l2 h2) :
    zahlWort (Zahl.band h0 h0' a b) = andB .b64 (zahlWort a) (zahlWort b) := by
  have hant : a.n.toNat < 2 ^ 64 := zahl_toNat_lt64 h0 hw1 a
  have hbnt : b.n.toNat < 2 ^ 64 := zahl_toNat_lt64 h0' hw2 b
  have hn : (Zahl.band h0 h0' a b).n.toNat = a.n.toNat &&& b.n.toNat := by
    show (((a.n.toNat &&& b.n.toNat : Nat) : Int)).toNat = a.n.toNat &&& b.n.toNat
    simp
  show BitVec.ofNat 64 (Zahl.band h0 h0' a b).n.toNat = andB .b64 (zahlWort a) (zahlWort b)
  rw [hn]
  unfold andB zahlWort
  rw [trunc_b64]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hant, Nat.mod_eq_of_lt hbnt]
  have hand_le : a.n.toNat &&& b.n.toNat ≤ a.n.toNat := Nat.and_le_left
  rw [Nat.mod_eq_of_lt (by omega)]

/-- OR transfer: the REUSED `Zahl.bor` value equals the REUSED
    `orB .b64` result, through `zahlWort` (width witness `w = 64`). -/
theorem bor_zahlWort {l1 h1 l2 h2 : Int} (h0 : 0 ≤ l1) (h0' : 0 ≤ l2)
    (hw1 : h1 < ((2 ^ 64 : Nat) : Int)) (hw2 : h2 < ((2 ^ 64 : Nat) : Int)) :
    ∀ (a : Zahl l1 h1) (b : Zahl l2 h2),
      zahlWort (Zahl.bor 64 h0 h0' hw1 hw2 a b) =
        orB .b64 (zahlWort a) (zahlWort b) := by
  intro a b
  have hant : a.n.toNat < 2 ^ 64 := zahl_toNat_lt64 h0 hw1 a
  have hbnt : b.n.toNat < 2 ^ 64 := zahl_toNat_lt64 h0' hw2 b
  have hn : (Zahl.bor 64 h0 h0' hw1 hw2 a b).n.toNat = a.n.toNat ||| b.n.toNat := by
    show (((a.n.toNat ||| b.n.toNat : Nat) : Int)).toNat = a.n.toNat ||| b.n.toNat
    simp
  show BitVec.ofNat 64 (Zahl.bor 64 h0 h0' hw1 hw2 a b).n.toNat =
    orB .b64 (zahlWort a) (zahlWort b)
  rw [hn]
  unfold orB zahlWort
  rw [trunc_b64]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hant, Nat.mod_eq_of_lt hbnt]
  have hor_lt : a.n.toNat ||| b.n.toNat < 2 ^ 64 := by
    have := Nat.or_lt_two_pow (x := a.n.toNat) (y := b.n.toNat) (n := 64) hant hbnt
    exact this
  rw [Nat.mod_eq_of_lt hor_lt]

/-! ## 2. SOURCE CORRESPONDENCE: NEG, two's complement over any value.

    `Zahl.neg` is defined over ANY range (source values may be
    negative), so the register-level correspondence goes through the
    REUSED `intWort` (two's complement embedding), never `zahlWort`
    (which is lossy outside nonnegative-below-`2^64`). The identity
    holds unconditionally: two's-complement negation commutes with the
    modular embedding for every integer, independent of range (the
    `sMin` overflow is an architectural FLAG fact, `negUeberlauf`
    in `ShiftLogic.lean`, not a value-correspondence gap). -/

/-- NEG transfer: the REUSED `Zahl.neg` value equals the REUSED
    `negW .b64` result, through the REUSED `intWort`, for every
    integer. -/
theorem neg_intWort (n : Int) : intWort (-n) = negW .b64 (intWort n) := by
  have hsub : negW .b64 (intWort n) = (0 : Wort) - intWort n := by
    unfold negW subB
    rw [trunc_b64]
  rw [hsub]
  apply BitVec.eq_of_toNat_eq
  have hsubv : ((0 : Wort) - intWort n).toNat =
      ((2 ^ 64 - (intWort n).toNat) + 0) % 2 ^ 64 := sub64_wert 0 (intWort n)
  rw [hsubv]
  unfold intWort
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h1 : (0 : Int) ≤ n % (2 ^ 64 : Int) := Int.emod_nonneg n (by decide)
  have h2 : n % (2 ^ 64 : Int) < (2 ^ 64 : Int) := Int.emod_lt_of_pos n (by decide)
  have h3 : (0 : Int) ≤ (-n) % (2 ^ 64 : Int) := Int.emod_nonneg (-n) (by decide)
  have h4 : (-n) % (2 ^ 64 : Int) < (2 ^ 64 : Int) := Int.emod_lt_of_pos (-n) (by decide)
  have htoNat1 : (n % (2 ^ 64 : Int)).toNat < 2 ^ 64 := by omega
  have hkey : (-n) % (2 ^ 64 : Int) = (2 ^ 64 - n % (2 ^ 64 : Int)) % (2 ^ 64 : Int) := by
    omega
  have hcast : ((n % (2 ^ 64 : Int)).toNat : Int) = n % (2 ^ 64 : Int) :=
    Int.toNat_of_nonneg h1
  omega

/-! ## 3. SOURCE CORRESPONDENCE: LEA, the address-selection fact of §3A.

    `add a (shl b s)` -- the REUSED `Zahl.add` applied to `a` and the
    REUSED `Zahl.shl` of `b` by the COMPILE-TIME constant
    `scaleShift sc` (the SIB scale field is encoded at compile time,
    never a runtime shift count, so the shift amount is carried as a
    singleton `Zahl`, exactly as `StaerkeReduktion.lean`'s
    `mul_pow2_shl` carries its constant `k`) -- lowers to exactly ONE
    `lea64`, with the same value, whenever the sum fits the unsigned
    64-bit range the target word carries. `disp` stays a plain target
    literal, never a second source value: the fact names what the
    CHECKER must certify before an optimiser may fold `a + (b << s)`
    into one instruction. -/

/-- The singleton-shift value computed by the REUSED `Zahl.shl` is
    exactly `b.n * 2 ^ scaleShift sc` (mirrors `mul_pow2_shl`'s own
    `Int.toNat_natCast` step). -/
theorem shl_scale_wert {l2 h2 : Int} (w : Nat) (sc : Scale)
    (hw1 : h2 < 2 ^ w) (hw2 : ((scaleShift sc : Nat) : Int) < ((w : Nat) : Int))
    (h0' : 0 ≤ l2) (b : Zahl l2 h2) :
    (Zahl.shl w hw1 hw2 h0' (Int.natCast_nonneg _) b
        (⟨((scaleShift sc : Nat) : Int), Int.le_refl _, Int.le_refl _⟩ :
          Zahl ((scaleShift sc : Nat) : Int) ((scaleShift sc : Nat) : Int))).n
      = b.n * 2 ^ scaleShift sc := by
  show b.n * 2 ^ (((scaleShift sc : Nat) : Int)).toNat = b.n * 2 ^ scaleShift sc
  rw [Int.toNat_natCast]

/-- LEA's address-selection fact: the REUSED `Zahl.add a (Zahl.shl …)`
    source value, read back through `zahlWort`, equals the single
    `lea64` step's computed address (`leaVal`), whenever the exact sum
    is nonnegative and below `2 ^ 64` -- the range the checker must
    certify before the fold. -/
theorem lea_ist_add_shl {l1 h1 l2 h2 : Int} (w : Nat) (sc : Scale)
    (hw1 : h2 < 2 ^ w) (hw2 : ((scaleShift sc : Nat) : Int) < ((w : Nat) : Int))
    (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (a : Zahl l1 h1) (b : Zahl l2 h2)
    (s : Zustand) (base idx : Register)
    (hbase : s.register base = zahlWort a) (hidx : s.register idx = zahlWort b)
    (ha64 : h1 < ((2 ^ 64 : Nat) : Int)) (hb64 : h2 < ((2 ^ 64 : Nat) : Int))
    (hsumlo : 0 ≤ a.n + b.n * 2 ^ scaleShift sc)
    (hsumhi : a.n + b.n * 2 ^ scaleShift sc < ((2 ^ 64 : Nat) : Int)) :
    leaVal s base (some (idx, sc)) 0 =
      zahlWort (Zahl.add a
        (Zahl.shl w hw1 hw2 h0' (Int.natCast_nonneg _) b
          (⟨((scaleShift sc : Nat) : Int), Int.le_refl _, Int.le_refl _⟩ :
            Zahl ((scaleShift sc : Nat) : Int) ((scaleShift sc : Nat) : Int)))) := by
  have hant : a.n.toNat < 2 ^ 64 := zahl_toNat_lt64 h0 ha64 a
  have hbnt : b.n.toNat < 2 ^ 64 := zahl_toNat_lt64 h0' hb64 b
  have ha0 : 0 ≤ a.n := by have := a.lo_le; omega
  have hb0 : 0 ≤ b.n := by have := b.lo_le; omega
  have hval : (Zahl.add a
      (Zahl.shl w hw1 hw2 h0' (Int.natCast_nonneg _) b
        (⟨((scaleShift sc : Nat) : Int), Int.le_refl _, Int.le_refl _⟩ :
          Zahl ((scaleShift sc : Nat) : Int) ((scaleShift sc : Nat) : Int)))).n
      = a.n + b.n * 2 ^ scaleShift sc := by
    show a.n + (Zahl.shl w hw1 hw2 h0' (Int.natCast_nonneg _) b
      (⟨((scaleShift sc : Nat) : Int), Int.le_refl _, Int.le_refl _⟩ :
        Zahl ((scaleShift sc : Nat) : Int) ((scaleShift sc : Nat) : Int))).n = _
    rw [shl_scale_wert w sc hw1 hw2 h0' b]
  unfold zahlWort
  simp only [leaVal]
  rw [hval, hbase, hidx]
  apply BitVec.eq_of_toNat_eq
  have hlt64 : scaleShift sc % 64 = scaleShift sc :=
    Nat.mod_eq_of_lt (by have := scaleShift_lt sc; omega)
  have hshl : (shlB .b64 (BitVec.ofNat 64 b.n.toNat) (scaleShift sc)).toNat =
      b.n.toNat * 2 ^ scaleShift sc % 2 ^ 64 := by
    unfold shlB
    simp only [trunc_b64, schiebeZaehler, BitVec.toNat_ofNat, hlt64, Nat.mod_mod,
      Nat.mod_eq_of_lt hbnt]
  have hcastSum : ((a.n + b.n * 2 ^ scaleShift sc : Int)).toNat =
      a.n.toNat + b.n.toNat * 2 ^ scaleShift sc := by
    have hpow0 : (0 : Int) ≤ 2 ^ scaleShift sc := Int.pow_nonneg_two (scaleShift sc)
    have hbnn : 0 ≤ b.n * 2 ^ scaleShift sc := Int.mul_nonneg hb0 hpow0
    have hpowNat : ((2 : Int) ^ scaleShift sc).toNat = 2 ^ scaleShift sc := by
      cases sc <;> decide
    rw [Int.toNat_add ha0 hbnn, Int.toNat_mul hb0 hpow0, hpowNat]
  have hNatSum : a.n.toNat + b.n.toNat * 2 ^ scaleShift sc < 2 ^ 64 := by
    have hlt := (Int.toNat_lt hsumlo).mpr hsumhi
    omega
  have hmain : (zahlWort a + shlB .b64 (zahlWort b) (scaleShift sc) +
      dispWort (0 : BitVec 32) : Wort).toNat =
      a.n.toNat + b.n.toNat * 2 ^ scaleShift sc := by
    have hsum2 : b.n.toNat * 2 ^ scaleShift sc < 2 ^ 64 := by omega
    have hdisp0 : (dispWort (0 : BitVec 32)).toNat = 0 := by decide
    unfold zahlWort
    simp only [BitVec.toNat_add, hdisp0, Nat.add_zero, BitVec.toNat_ofNat, hshl,
      Nat.mod_mod, Nat.mod_eq_of_lt hant, Nat.mod_eq_of_lt hsum2, Nat.mod_eq_of_lt hNatSum]
  rw [hmain, BitVec.toNat_ofNat, hcastSum, Nat.mod_eq_of_lt hNatSum]

/-! ## 4. SOURCE CORRESPONDENCE: TEST, branch on `eq x 0`.

    `test r, r` is AND-for-flags-only; AND is idempotent, so the ZF of
    `test r, r` is exactly the zero test on the register's own value --
    the fact an optimiser needs to lower `eq x 0` to `test`/`je`
    instead of a separate compare against the literal zero. -/

/-- AND is idempotent at full width: `andB .b64 x x = x`. -/
theorem andB_b64_self (x : Wort) : andB .b64 x x = x := by
  unfold andB
  rw [BitVec.and_self, trunc_b64]

/-- `test r, r`'s ZF is exactly `eq (register r) 0`: the ZF of the
    REUSED `andW .b64 x x` flag snapshot reads the register's own
    value, not a second comparison. -/
theorem test_self_zf (x : Wort) :
    (andW .b64 x x).2.zf = zfTest x := by
  show (logikFlags .b64 (andB .b64 x x)).zf = zfTest x
  rw [andB_b64_self]
  rfl

/-- Instantiated through the step: `testReg64 r r` sets the resulting
    `flags.zf` to exactly the zero test of `r`'s pre-state value. -/
theorem core_testReg64_self_zf (d : CoreDecodiert) (s s' : Zustand)
    (r : Register) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .testReg64 r r) (hstep : coreSchritt d s = some s') :
    s'.flags.zf = zfTest (s.register r) := by
  rw [core_testReg64 d s r r hok h] at hstep
  cases hstep
  show (andW .b64 (s.register r) (s.register r)).2.zf = zfTest (s.register r)
  rw [test_self_zf]

/-! ## 5. Witnesses: each covered form on a concrete, non-degenerate
    state with a visibly changed value. -/

/-- Witness registers: `rax = 0xF0`, `rcx = 0x0F`, `rbx` the data
    address, `rsp` the stack top. -/
def coreWitReg : Register → Wort := fun q =>
  if q = Register.rax then 0xF0
  else if q = Register.rcx then 0x0F
  else if q = Register.rbx then BitVec.ofNat 64 8192
  else if q = Register.rsp then BitVec.ofNat 64 8192
  else BitVec.ofNat 64 0

/-- Witness flags: nothing set. -/
def coreWitFlags : Flags :=
  { cf := false, pf := true, af := some false, zf := false, sf := false, of := false }

/-- Witness start state: code at 4096, clean permissive memory. -/
def coreWitState : Zustand :=
  { register := coreWitReg, flags := coreWitFlags, rip := BitVec.ofNat 64 4096,
    speicher := zeugenSpeicher }

/-- AND witness: `0xF0 & 0x0F = 0`, ZF set, RIP advances. -/
theorem witness_and :
    ((coreSchritt ⟨.andReg64 .rax .rcx, 3⟩ coreWitState).map
        (fun s => s.register .rax) = some 0) ∧
    ((coreSchritt ⟨.andReg64 .rax .rcx, 3⟩ coreWitState).map
        (fun s => s.flags.zf) = some true) ∧
    ((coreSchritt ⟨.andReg64 .rax .rcx, 3⟩ coreWitState).map
        (fun s => s.rip) = some (BitVec.ofNat 64 4099)) := by
  decide

/-- OR witness: `0xF0 | 0x0F = 0xFF`, sign set (bit 7, but full-width
    sign is bit 63, so SF is clear), ZF clear. -/
theorem witness_or :
    ((coreSchritt ⟨.orReg64 .rax .rcx, 3⟩ coreWitState).map
        (fun s => s.register .rax) = some 0xFF) ∧
    ((coreSchritt ⟨.orReg64 .rax .rcx, 3⟩ coreWitState).map
        (fun s => s.flags.zf) = some false) := by
  decide

/-- TEST witness: `0xF0 & 0x0F = 0` for flags only, RAX itself is
    UNCHANGED (no write-back), ZF set. -/
theorem witness_test :
    ((coreSchritt ⟨.testReg64 .rax .rcx, 3⟩ coreWitState).map
        (fun s => s.register .rax) = some 0xF0) ∧
    ((coreSchritt ⟨.testReg64 .rax .rcx, 3⟩ coreWitState).map
        (fun s => s.flags.zf) = some true) := by
  decide

/-- NOT witness: `~0xF0 = 0xFFFFFFFFFFFFFF0F` at full width, flags
    UNCHANGED from the pre-state (architectural NOT touches no flag). -/
theorem witness_not :
    ((coreSchritt ⟨.notReg64 .rax, 3⟩ coreWitState).map
        (fun s => s.register .rax) = some 0xFFFFFFFFFFFFFF0F) ∧
    ((coreSchritt ⟨.notReg64 .rax, 3⟩ coreWitState).map
        (fun s => s.flags) = some coreWitFlags) := by
  decide

/-- NEG witness: `-0xF0` wraps to `0xFFFFFFFFFFFFFF10`, CF set (nonzero
    operand), OF clear (not the signed minimum). -/
theorem witness_neg :
    ((coreSchritt ⟨.negReg64 .rax, 3⟩ coreWitState).map
        (fun s => s.register .rax) = some 0xFFFFFFFFFFFFFF10) ∧
    ((coreSchritt ⟨.negReg64 .rax, 3⟩ coreWitState).map
        (fun s => s.flags.cf) = some true) ∧
    ((coreSchritt ⟨.negReg64 .rax, 3⟩ coreWitState).map
        (fun s => s.flags.of) = some false) := by
  decide

/-- MOVZX-from-8 witness: the low byte `0xF0` of `rax` zero-extends to
    `0xF0`, upper bits cleared, flags unchanged. -/
theorem witness_movzx8 :
    ((coreSchritt ⟨.movzx64From8 .rbx .rax, 4⟩ coreWitState).map
        (fun s => s.register .rbx) = some 0xF0) := by
  decide

/-- MOVZX-from-16 witness: the low 16 bits `0x00F0` zero-extend to
    `0x00F0`. -/
theorem witness_movzx16 :
    ((coreSchritt ⟨.movzx64From16 .rbx .rax, 4⟩ coreWitState).map
        (fun s => s.register .rbx) = some 0x00F0) := by
  decide

/-- MOVSX-from-8 witness: the low byte `0xF0` (negative as a signed
    byte) sign-extends to `0xFFFFFFFFFFFFFFF0`. -/
theorem witness_movsx8 :
    ((coreSchritt ⟨.movsx64From8 .rbx .rax, 4⟩ coreWitState).map
        (fun s => s.register .rbx) = some 0xFFFFFFFFFFFFFFF0) := by
  decide

/-- MOVSX-from-16 witness: the low 16 bits `0x00F0` (nonnegative as a
    signed word) sign-extend to `0x00F0` (no fill). -/
theorem witness_movsx16 :
    ((coreSchritt ⟨.movsx64From16 .rbx .rax, 4⟩ coreWitState).map
        (fun s => s.register .rbx) = some 0x00F0) := by
  decide

/-- MOVSXD (`movsx64From32`) witness: the low 32 bits of a negative
    32-bit value fill the upper half on sign extension. -/
theorem witness_movsxd :
    ((coreSchritt ⟨.movsx64From32 .rbx .rax, 3⟩
        { coreWitState with register := fun q =>
          if q = .rax then 0xFFFFFFFF80000000 else coreWitReg q }).map
      (fun s => s.register .rbx) = some 0xFFFFFFFF80000000) := by
  decide

/-- LEA witness: `rax + rcx * 2 ^ 2 + 0x10` with `rax = 0xF0`,
    `rcx = 0x0F`, landing at `0xF0 + 0x3C + 0x10 = 0x13C`, flags and
    memory untouched (LEA never dereferences). -/
theorem witness_lea :
    ((coreSchritt ⟨.lea64 .rbx .rax (some (.rcx, .s4)) 16, 8⟩
        coreWitState).map (fun s => s.register .rbx) = some 0x13C) ∧
    ((coreSchritt ⟨.lea64 .rbx .rax (some (.rcx, .s4)) 16, 8⟩
        coreWitState).map (fun s => s.flags) = some coreWitFlags) ∧
    ((coreSchritt ⟨.lea64 .rbx .rax (some (.rcx, .s4)) 16, 8⟩
        coreWitState).map (fun s => s.speicher.bytes (BitVec.ofNat 64 8192)) =
      some (coreWitState.speicher.bytes (BitVec.ofNat 64 8192))) := by
  decide

/-! ## 6. Poison probes: refused by construction.

    Each probe is a concrete refusal the validator/decoder makes,
    checked by `decide`/`rfl`, never an invented hardware fault. -/

/-- LEA with `rsp` as the index is refused: the canonical bytes for
    `some (.rsp, sc)` decode back to `none` (the SIB "no index"
    collision named by `leaIndexOk`/CUTS in `IntegerCore.lean`), so a
    round trip through the codec silently loses the index -- exactly
    why the admission `coreValid`/`leaIndexOk` refuses this input
    before it ever reaches the encoder. -/
theorem poison_lea_rsp_index (dst base : Register) (sc : Scale)
    (disp : BitVec 32) :
    decodeCore (encodeCore (.lea64 dst base (some (Register.rsp, sc)) disp)) =
      some (⟨.lea64 dst base none disp, 8⟩, []) ∧
    leaIndexOk (some (Register.rsp, sc)) = false ∧
    coreValid (.lea64 dst base (some (Register.rsp, sc)) disp) = false := by
  refine ⟨?_, rfl, rfl⟩
  have hrex := rexCoreBits_rexByteX (regHigh dst) (regHigh Register.rsp) (regHigh base)
    (regHigh_lt dst) (regHigh_lt Register.rsp) (regHigh_lt base)
  have hdst := codeReg_regHigh_regLow dst
  have hbase := codeReg_regHigh_regLow base
  show decodeCore
      (([rexByteX (regHigh dst) (regHigh Register.rsp) (regHigh base), natByte 141,
        modrmMem (regLow dst) 4,
        sibByte (scaleShift sc) (regLow Register.rsp) (regLow base)] ++
        leBytes32 disp) ++ ([] : List Byte)) = _
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have h141 : (byteNat (natByte 141) == 141) = true := by decide
  simp only [decodeCore, hrex, decodeCoreTail, h141, if_true]
  simp only [decodeCoreLea]
  have hmmField : byteNat (modrmMem (regLow dst) 4) / 64 = 2 ∧
      byteNat (modrmMem (regLow dst) 4) % 8 = 4 ∧
      byteNat (modrmMem (regLow dst) 4) / 8 % 8 = regLow dst % 8 := by
    unfold modrmMem
    have h1 : regLow dst % 8 < 8 := Nat.mod_lt _ (by decide)
    have hlt : 128 + 8 * (regLow dst % 8) + 4 % 8 < 256 := by omega
    have heq : byteNat (natByte (128 + 8 * (regLow dst % 8) + 4 % 8)) =
        128 + 8 * (regLow dst % 8) + 4 % 8 := byteNat_natByte_of_lt _ hlt
    rw [heq]; refine ⟨by omega, by omega, by omega⟩
  have hcond1 : (byteNat (modrmMem (regLow dst) 4) / 64 == 2) = true := by
    rw [hmmField.1]; decide
  have hcond2 : (byteNat (modrmMem (regLow dst) 4) % 8 == 4) = true := by
    rw [hmmField.2.1]; decide
  rw [if_pos ⟨hcond1, hcond2⟩]
  have hsibField :
      byteNat (sibByte (scaleShift sc) (regLow Register.rsp) (regLow base)) / 8 % 8
        = regLow Register.rsp % 8 ∧
      byteNat (sibByte (scaleShift sc) (regLow Register.rsp) (regLow base)) % 8
        = regLow base % 8 := by
    unfold sibByte
    have h1 : regLow Register.rsp % 8 < 8 := Nat.mod_lt _ (by decide)
    have h2 : regLow base % 8 < 8 := Nat.mod_lt _ (by decide)
    have h3 : scaleShift sc < 4 := scaleShift_lt sc
    have hlt :
        64 * scaleShift sc + 8 * (regLow Register.rsp % 8) + regLow base % 8 < 256 := by
      omega
    have heq : byteNat
        (natByte (64 * scaleShift sc + 8 * (regLow Register.rsp % 8) + regLow base % 8))
        = 64 * scaleShift sc + 8 * (regLow Register.rsp % 8) + regLow base % 8 :=
      byteNat_natByte_of_lt _ hlt
    rw [heq]; exact ⟨by omega, by omega⟩
  rw [hmmField.2.2, hsibField.1, hsibField.2]
  have hmodDst : regLow dst % 8 = regLow dst := Nat.mod_eq_of_lt (regLow_lt dst)
  have hmodBase : regLow base % 8 = regLow base := Nat.mod_eq_of_lt (regLow_lt base)
  have hrsplow : regLow Register.rsp % 8 = regLow Register.rsp :=
    Nat.mod_eq_of_lt (regLow_lt Register.rsp)
  rw [hmodDst, hmodBase, hrsplow, hdst, hbase]
  rw [parseLe32_leBytes32]
  simp only [show (regHigh Register.rsp * 8 + regLow Register.rsp == 4) = true
    from by decide, if_true]

/-- A MOVZX/MOVSX byte-extension row WITHOUT a canonical REX prefix
    (the legacy high-byte-register path in 32-bit mode, where `0F B6`
    on a bare ModRM could name `AH`/`BH`/`CH`/`DH`) is refused outright:
    this codec always carries a REX byte, so no high-byte register
    form is ever reachable. -/
theorem poison_highbyte_no_rex :
    decodeCore [natByte 15, natByte 182, natByte 193] = none ∧
    decodeCore [natByte 15, natByte 190, natByte 193] = none := by
  refine ⟨rfl, rfl⟩

/-- A REX.X bit set on any non-LEA opcode is refused: the only form
    carrying a third extension bit is LEA (opcode `141`); here the
    opcode is AND's `33`. -/
theorem poison_rex_x_non_lea :
    decodeCore [natByte 74, natByte 33, natByte 193] = none := rfl

/-- A Group-3 row (opcode `247`) with an extension digit outside
    `{2, 3}` is no covered core form: digit `/5` (bare `IMUL` has no
    one-operand row here) refuses. -/
theorem poison_f7_wrong_digit :
    decodeCore [natByte 72, natByte 247, natByte 233] = none := rfl

/-- A register-indirect (mod ≠ 3) ModRM after AND's opcode is not a
    covered form: this codec admits register-direct ALU rows only. -/
theorem poison_and_memory_mode :
    decodeCore [natByte 72, natByte 33, natByte 1] = none := rfl

/-- LEA without a SIB byte (`rm ≠ 4`, i.e. a plain register-direct or
    base-only ModRM) is not canonical: every covered LEA forces the
    SIB byte. -/
theorem poison_lea_no_sib :
    decodeCore [natByte 72, natByte 141, natByte 192] = none := rfl

/-- A truncated LEA (missing the SIB byte entirely) refuses. -/
theorem poison_lea_truncated :
    decodeCore [natByte 72, natByte 141, natByte 132] = none := rfl

/-- A truncated AND row (ModRM byte missing) refuses. -/
theorem poison_and_truncated :
    decodeCore [natByte 72, natByte 33] = none := rfl

/-- A non-canonical REX byte value (`71`, just below the admitted
    `72..79` window) refuses every covered form outright. -/
theorem poison_rex_below_window :
    decodeCore [natByte 71, natByte 33, natByte 193] = none := rfl

/- CUTS:
   Proved here: AND/OR source-value transfer for nonnegative values in
   64-bit range (`band_zahlWort`/`bor_zahlWort`, through the REUSED
   `zahlWort`); NEG source-value transfer for EVERY integer (through
   the REUSED `intWort`, two's complement, unconditional -- the
   `sMin`/overflow story stays an architectural FLAG fact, already
   named by `NegGueltig`/`negUeberlauf` in `ShiftLogic.lean`); the
   LEA address-selection fact (`lea_ist_add_shl`: the REUSED
   `Zahl.add`/`Zahl.shl` singleton-shift value equals the single
   `lea64` step's address, through `zahlWort`, exactly when the exact
   sum is nonnegative and below `2 ^ 64`); the TEST branch-on-zero fact
   (`test_self_zf`/`core_testReg64_self_zf`); eleven witnesses covering
   every one of the ten forms on a concrete, jointly nondegenerate
   state (AND/OR/TEST/NOT/NEG/LEA/MOVZX×2/MOVSX×2/MOVSXD, each with a
   visible value and, where architecturally defined, flag change); and
   nine poison probes (the `rsp`-as-LEA-index collision, the
   unreachable legacy high-byte path, REX.X on a non-LEA opcode, a
   wrong Group-3 digit, a memory-mode ModRM, a missing SIB byte, two
   truncations and a below-window REX byte).
   NOT proved here, and not claimed:
   - No OR transfer beyond the stated nonnegative-in-range domain, and
     no AND/OR/NEG transfer through anything but `zahlWort`/`intWort`
     themselves (their own lossiness outside that domain is inherited,
     not re-proved).
   - No `Expr`-level syntax rewrite for LEA (unlike
     `StaerkeReduktion.lean`'s `staerkeMul`): `lea_ist_add_shl` is a
     VALUE fact over `Zahl.add`/`Zahl.shl`, not a typed `Expr → Expr`
     transform with its own evaluator witness; a later lowering lane
     owns that rewrite, exactly as `StaerkeReduktion.lean`'s own CUTS
     leaves `div`/`rem` syntax rewrites open.
   - No hardware correspondence: encodings are the stated canonical
     subset of `IntegerCore.lean`; this file adds no new byte form.
   - No TSO/concurrency bridge, no cost transfer, no ABI/image claim.
   - No new hardware or software assumption and no checker rule: no
     diagnostic, poison-probe, example or CLI number is taken.
-/

#print axioms zahl_toNat_lt64
#print axioms band_zahlWort
#print axioms bor_zahlWort
#print axioms neg_intWort
#print axioms shl_scale_wert
#print axioms lea_ist_add_shl
#print axioms andB_b64_self
#print axioms test_self_zf
#print axioms core_testReg64_self_zf
#print axioms witness_and
#print axioms witness_or
#print axioms witness_test
#print axioms witness_not
#print axioms witness_neg
#print axioms witness_movzx8
#print axioms witness_movzx16
#print axioms witness_movsx8
#print axioms witness_movsx16
#print axioms witness_movsxd
#print axioms witness_lea
#print axioms poison_lea_rsp_index
#print axioms poison_highbyte_no_rex
#print axioms poison_rex_x_non_lea
#print axioms poison_f7_wrong_digit
#print axioms poison_and_memory_mode
#print axioms poison_lea_no_sib
#print axioms poison_lea_truncated
#print axioms poison_and_truncated
#print axioms poison_rex_below_window

end Gabbro.Grammatik.X86
