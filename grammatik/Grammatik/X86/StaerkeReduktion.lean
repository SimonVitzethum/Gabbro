/-
  File:      Grammatik/X86/StaerkeReduktion.lean
  Subject:   Range-justified integer strength reduction (lane 311).

  Multiplication/division/remainder by a power of two become shifts/masks
  ONLY where the source range proofs justify them: nonneg operands for
  `mul`/`div`/`rem` (the `M102`/`M137` side conditions carried by the
  syntax itself), a divisor `2 ^ k` that is never zero, and shift counts
  below the machine width. Signed division/remainder (`sdiv`/`srem`) are
  REFUSED: truncation differs from shift for negative numerators. No
  reassociation, no floats, no inferred contracts.

  Target helpers are the REAL canonical word operations (`BitVec` shifts
  and `&&&` over `Grammatik/X86/Typen.lean`'s `Wort`).
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Target left shift: the canonical word shift. -/
def shlW (x : Wort) (k : Nat) : Wort := x <<< k

/-- Target logical right shift: the canonical word shift. -/
def shrW (x : Wort) (k : Nat) : Wort := x >>> k

/-- Target remainder mask for `2 ^ k`: the low `k` bits set. -/
def maskW (k : Nat) : Wort := BitVec.ofNat 64 (2 ^ k - 1)

/-- Probe: `3 << 2` is `12` on real words. -/
theorem probe_shlW : shlW 3 2 = 12 := by decide

/-! ## 1. The mask identity: `n % 2 ^ k` is `n &&& (2 ^ k - 1)`.

    Bit-for-bit: both sides keep exactly the low `k` bits
    (`Nat.testBit_mod_two_pow`, `Nat.testBit_two_pow_sub_one`). -/

/-- Remainder by a power of two is masking with the low-bit mask. -/
theorem mod_pow2_and_mask (n k : Nat) : n % 2 ^ k = n &&& (2 ^ k - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_and, Nat.testBit_two_pow_sub_one,
    Bool.and_comm (decide (i < k)) (n.testBit i)]

/-! ## 2. Source value correspondence: `mul`/`div`/`rem` by `2 ^ k`.

    Each theorem keeps the FULL source side conditions as premises
    (`hw1`/`hw2`/`h0`: the width and nonnegativity the syntax already
    demands) and forwards them to the shift/mask side, so no check is
    weakened. The divisor `2 ^ k` is never zero, hence no new fault and
    no removed fault. -/

/-- `a * 2 ^ k` is `a << k`: the shift value is the product value.

    Every premise is a source side condition, forwarded to `Zahl.shl`. -/
theorem mul_pow2_shl (w k : Nat) (l1 h1 : Int)
    (hw1 : h1 < 2 ^ w) (hw2 : ((k : Nat) : Int) < ((w : Nat) : Int))
    (h0 : 0 ≤ l1)
    (a : Zahl l1 h1) :
    (Zahl.shl w hw1 hw2 h0 (Int.natCast_nonneg k) a (⟨((k : Nat) : Int), Int.le_refl _, Int.le_refl _⟩ : Zahl ((k : Nat) : Int) ((k : Nat) : Int))).n
      = (Zahl.mul a (⟨((2 : Int) ^ k), Int.le_refl _, Int.le_refl _⟩ : Zahl ((2 : Int) ^ k) ((2 : Int) ^ k))).n := by
  show a.n * 2 ^ (((k : Nat) : Int)).toNat = a.n * (2 ^ k)
  rw [Int.toNat_natCast]

/-- `a / 2 ^ k` is `a >> k` for nonneg `a`: truncation and shift agree
    exactly where the source rule (`M102`, nonneg numerator) holds.
    The divisor `2 ^ k` is proved `>= 1` inline, never assumed. -/
theorem div_pow2_shr (w k : Nat) (l1 h1 : Int)
    (hw1 : h1 < 2 ^ w) (hw2 : ((k : Nat) : Int) < ((w : Nat) : Int))
    (h0 : 0 ≤ l1)
    (a : Zahl l1 h1) :
    (Zahl.shr w hw1 hw2 h0 (Int.natCast_nonneg k) a (⟨((k : Nat) : Int), Int.le_refl _, Int.le_refl _⟩ : Zahl ((k : Nat) : Int) ((k : Nat) : Int))).n
      = (Zahl.div h0 (by have h : 1 ≤ 2 ^ k := Nat.one_le_two_pow; exact_mod_cast h) a (⟨((2 : Int) ^ k), Int.le_refl _, Int.le_refl _⟩ : Zahl ((2 : Int) ^ k) ((2 : Int) ^ k))).n := by
  have ha : 0 ≤ a.n := by have := a.lo_le; omega
  show a.n / 2 ^ (((k : Nat) : Int)).toNat = a.n.tdiv (2 ^ k)
  rw [Int.toNat_natCast, Int.tdiv_eq_ediv_nonneg ha]

/-- `a % 2 ^ k` is `a &&& (2 ^ k - 1)`: the remainder value is the
    masked value, through `mod_pow2_and_mask`. -/
theorem rem_pow2_band (k : Nat) (l1 h1 : Int)
    (h0 : 0 ≤ l1)
    (a : Zahl l1 h1) :
    (Zahl.band h0 (Int.natCast_nonneg (2 ^ k - 1)) a
      (⟨((((2 ^ k - 1 : Nat))) : Int), Int.le_refl _, Int.le_refl _⟩ : Zahl ((((2 ^ k - 1 : Nat))) : Int) ((((2 ^ k - 1 : Nat))) : Int))).n
      = (Zahl.rem h0 (by have h : 1 ≤ 2 ^ k := Nat.one_le_two_pow; exact_mod_cast h) a
      (⟨((((2 ^ k : Nat))) : Int), Int.le_refl _, Int.le_refl _⟩ : Zahl ((((2 ^ k : Nat))) : Int) ((((2 ^ k : Nat))) : Int))).n := by
  have ha : 0 ≤ a.n := by have := a.lo_le; omega
  have h1k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hnn : (0 : Int) ≤ ((((2 ^ k : Nat))) : Int) := by exact_mod_cast Nat.zero_le _
  have hne : ((((2 ^ k : Nat))) : Int) ≠ 0 := by
    have hp : (1 : Int) ≤ ((((2 ^ k : Nat))) : Int) := by exact_mod_cast h1k
    omega
  have key : (a.n.tmod ((((2 ^ k : Nat))) : Int)).toNat = a.n.toNat % 2 ^ k := by
    rw [Int.tmod_eq_emod_of_nonneg ha, Int.toNat_emod ha hnn, Int.toNat_natCast]
  have hbr : (0 : Int) ≤ a.n.tmod ((((2 ^ k : Nat))) : Int) := by
    rw [Int.tmod_eq_emod_of_nonneg ha]; exact Int.emod_nonneg _ hne
  have lift := congrArg (fun n : Nat => ((n : Int))) key
  rw [mod_pow2_and_mask] at lift
  rw [Int.toNat_of_nonneg hbr] at lift
  have goal_eq : ((((a.n.toNat &&& Int.toNat (((2 ^ k - 1 : Nat)) : Int)))) : Int)
      = a.n.tmod ((((2 ^ k : Nat))) : Int) := by
    rw [Int.toNat_natCast]; exact lift.symm
  exact goal_eq

/-! ## 3. Refusal: NO strength reduction for `sdiv`/`srem`.

    Truncation (`tdiv`) and shift/floor (`ediv`, `/`) disagree on
    negative numerators, so an arithmetic-shift lowering of signed
    division would change the value. This lane rewrites nothing signed:
    the counterexample below is the reason, checked by `decide`. -/

/-- `-3 / 2` truncates to `-1` but floors (shifts) to `-2`: a shift
    lowering of `sdiv` would be wrong, so `sdiv`/`srem` stay. -/
theorem sdiv_kein_shift : (-3 : Int).tdiv 2 = -1 ∧ (-3 : Int) / 2 = -2 := by
  decide

/-! ## 4. Word bridges: the target shifts/masks read back as the source values.

    `shlW` is exact only under checked nonoverflow (`shlW_keinUeberlauf`:
    the product fits 64 bits -- the machine-width check); `shrW` and the
    mask read back unconditionally at the `toNat` level, and `shrW_breite`
    additionally pins the count below the operand width and below 64, so
    a count the hardware would mask cannot slip through silently. -/

/-- Target shift reads back as product-modulo-`2 ^ 64`. -/
theorem shlW_toNat (x : Wort) (k : Nat) :
    (shlW x k).toNat = x.toNat * 2 ^ k % 2 ^ 64 := by
  simp [shlW, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

/-- Checked nonoverflow: where the product fits 64 bits, the target
    shift IS the product -- the exact transfer `mul_pow2_shl` needs. -/
theorem shlW_keinUeberlauf (x : Wort) (k : Nat)
    (h : x.toNat * 2 ^ k < 2 ^ 64) :
    (shlW x k).toNat = x.toNat * 2 ^ k := by
  rw [shlW_toNat, Nat.mod_eq_of_lt h]

/-- Target logical shift reads back as division by `2 ^ k`. -/
theorem shrW_toNat (x : Wort) (k : Nat) :
    (shrW x k).toNat = x.toNat / 2 ^ k := by
  simp [shrW, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- Width-checked shift: the operand fits its `Breite`, the count is
    below the width (the source `hw2` shape) and hence below 64, and
    the shifted value stays in the width. -/
theorem shrW_breite (b : Breite) (x : Wort) (k : Nat)
    (hx : x.toNat < 2 ^ b.bits) (hk : k < b.bits) :
    (shrW x k).toNat = x.toNat / 2 ^ k ∧ (shrW x k).toNat < 2 ^ b.bits ∧ k < 64 := by
  have hval : (shrW x k).toNat = x.toNat / 2 ^ k := by
    simp [shrW, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  refine ⟨hval, ?_, ?_⟩
  · have hle := Nat.div_le_self (x.toNat) (2 ^ k)
    omega
  · have hb : b.bits ≤ 64 := by cases b <;> decide
    omega

/-- The mask word holds exactly the low `k` bits, for `k ≤ 64`. -/
theorem maskW_toNat (k : Nat) (hk : k ≤ 64) :
    (maskW k).toNat = 2 ^ k - 1 := by
  have hle : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk
  have hlt : 2 ^ k - 1 < 2 ^ 64 := by omega
  simp [maskW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- Target mask reads back as remainder by `2 ^ k`, for `k ≤ 64`. -/
theorem maskW_and (x : Wort) (k : Nat) (hk : k ≤ 64) :
    (x &&& maskW k).toNat = x.toNat % 2 ^ k := by
  rw [BitVec.toNat_and, maskW_toNat k hk, mod_pow2_and_mask]

/-! ## 5. The syntax rewrite: `a * 2 ^ k` becomes `a << k`.

    `staerkeMul` is an actual source-syntax rewrite (typed `Expr` to
    typed `Expr`); `staerkeMul_behält` proves the evaluated value is
    preserved against the REAL `eval`, by `mul_pow2_shl`. Only the
    `mul` shape gets a rewrite: `div`/`rem` keep their source form at
    the syntax level (their value correspondence of §2 is what a later
    lowering lane builds on), and `sdiv`/`srem` are refused (§3). -/

/-- The rewrite: `a * 2 ^ k` becomes `a << k` (shift amount as literal). -/
def staerkeMul {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {l1 h1 : Int}
    (w k : Nat)
    (hw1 : h1 < 2 ^ w) (hw2 : ((k : Nat) : Int) < ((w : Nat) : Int))
    (h0 : 0 ≤ l1)
    (a : Expr D Γ Λ (.int l1 h1)) :
    Expr D Γ Λ (.int 0 (h1 * 2 ^ (((k : Nat) : Int)).toNat)) :=
  .shl w hw1 hw2 h0 (Int.natCast_nonneg k) a (.lit ((k : Nat) : Int))

/-- The rewrite preserves the evaluated value against the real `eval`. -/
theorem staerkeMul_behält {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {l1 h1 : Int}
    (w k : Nat)
    (hw1 : h1 < 2 ^ w) (hw2 : ((k : Nat) : Int) < ((w : Nat) : Int))
    (h0 : 0 ≤ l1)
    (a : Expr D Γ Λ (.int l1 h1)) (σ₀ σ : World D) (ρ : Env D Γ) :
    (eval σ₀ (staerkeMul w k hw1 hw2 h0 a) σ ρ).n
      = (eval σ₀ (.mul a (.lit ((2 : Int) ^ k))) σ ρ).n :=
  mul_pow2_shl w k l1 h1 hw1 hw2 h0 (eval σ₀ a σ ρ)

/-- Joint witness: ALL premises of `staerkeMul_behält` instantiated
    together on the non-degenerate reference program `refD` (whose
    `einzahlen` writes its table, `refEin_schreibt`): `3 * 2 ^ 2`
    becomes `3 << 2`, both evaluating to `12`. -/
theorem staerkeMul_behält_zeuge :
    ∃ (w k : Nat) (hw1 : (3 : Int) < 2 ^ w) (hw2 : ((k : Nat) : Int) < ((w : Nat) : Int)) (h0 : 0 ≤ (3 : Int))
      (a : Expr refD [] [] (.int 3 3)) (σ₀ σ : World refD) (ρ : Env refD []),
      (eval σ₀ (staerkeMul w k hw1 hw2 h0 a) σ ρ).n
        = (eval σ₀ (.mul a (.lit ((2 : Int) ^ k))) σ ρ).n
      ∧ (vertragVon refD refEin).schreibt () = true := by
  refine ⟨8, 2, by decide, by decide, by decide, .lit 3,
    refSp0.welt [], refSp0.welt [], Env.nil,
    staerkeMul_behält 8 2 (by decide) (by decide) (by decide) (.lit 3)
      (refSp0.welt []) (refSp0.welt []) Env.nil,
    refEin_schreibt ()⟩

/-! ## 6. Operand and memory probes: the target words really move.

    Nonzero values that visibly change (`12 >> 2 = 3`, masking `0xFF`
    to `0xF`), plus a memory round-trip: the shifted word is stored
    through the REAL `write64`/`read64` and observably changes the byte
    at the address. -/

/-- Probe: `12 >> 2` is `3` on real words. -/
theorem probe_shrW : shrW 12 2 = 3 := by decide

/-- Probe: masking `0xFF` with the `2 ^ 4` mask gives `0xF`. -/
theorem probe_maskW : ((0xFF : Wort) &&& maskW 4) = 15 := by decide

/-- The shifted word goes through real memory: stored with `write64`,
    read back with `read64`, and the byte at the address changes. -/
theorem speicher_shlW_rueck :
    ∃ (m' : Speicher),
      write64 zeugenSpeicher 0 (shlW 3 2) = some m' ∧ read64 m' 0 = some 12 ∧
        zeugenSpeicher.bytes 0 ≠ m'.bytes 0 := by
  have hw : shlW 3 2 = 12 := probe_shlW
  have hwr : write64 zeugenSpeicher 0 (shlW 3 2)
      = some { zeugenSpeicher with bytes := writeBytes zeugenSpeicher 0 (shlW 3 2) } := by
    unfold write64
    have hc : schreibbar8 zeugenSpeicher 0 = true := rfl
    rw [if_pos hc]
  refine ⟨_, hwr, ?_, ?_⟩
  · have hrd := read64_nach_write64 zeugenSpeicher _ 0 (shlW 3 2) hwr rfl
    rw [hw] at hrd
    exact hrd
  · have hhit :=
      writeBytesN_hit zeugenSpeicher 0 (shlW 3 2) 8 0 (by decide) (by decide)
    rw [addrOff_null (0 : Adresse)] at hhit
    show BitVec.ofNat 8 0 ≠ writeBytes zeugenSpeicher 0 (shlW 3 2) 0
    unfold writeBytes
    rw [hhit]
    decide

/- CUTS:
   - No actual-byte claim: correspondence stops at the canonical `Wort`
     (`BitVec 64`) operations and `write64`/`read64` memory. Encoding,
     decoding, RIP stepping, ELF loading and execution of emitted bytes
     stay with the validation lanes; `dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md`
     §§0-5 own that transfer.
   - No `div`/`rem` syntax rewrite: §2 proves their VALUES equal the
     shift/mask values, but no `Expr`-level rewrite function is given
     (a later lowering lane owns it, with its own witness).
   - No signed reduction anywhere: `sdiv`/`srem` are refused by
     `sdiv_kein_shift`, not lowered.
   - No reassociation, no floats, no contract inference: the result
     RANGE of the rewritten `shl` (`0 .. h1 * 2 ^ k`) differs textually
     from the source `mul` range (four corners); only the VALUES are
     proved equal. Range transfer is the checker's `M104` business.
   - No concurrency, log, budget or time transfer: single-expression
     value correspondence only; `FolgeG`/budget/concurrency stay out.
   - Hardware count masking (counts `≥ 64`/`≥ 32` masked on silicon,
     zero in the model) is NOT bridged: `shrW_breite` pins counts below
     the width instead, so a masked count cannot slip through.
-/

#print axioms mod_pow2_and_mask
#print axioms mul_pow2_shl
#print axioms div_pow2_shr
#print axioms rem_pow2_band
#print axioms sdiv_kein_shift
#print axioms shlW_toNat
#print axioms shlW_keinUeberlauf
#print axioms shrW_toNat
#print axioms shrW_breite
#print axioms maskW_toNat
#print axioms maskW_and
#print axioms staerkeMul_behält
#print axioms staerkeMul_behält_zeuge
#print axioms probe_shlW
#print axioms probe_shrW
#print axioms probe_maskW
#print axioms speicher_shlW_rueck

end Gabbro.Grammatik.X86
