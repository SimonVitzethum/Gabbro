/-
  File:      Grammatik/CFormen.lean
  Subject:   The C semantics of the emitted forms (plan step 2, T4), the
             core: C integer types and C's conversion rules, the operator
             semantics with its UB inventory, the expression and statement
             syntax of the emitted subset, and its semantics on the block
             memory of `CSpeicher.lean`.

  The three passes of T4 build on this file:
    `CFormenI.lean`  -- pass (i): the near-neighbour forms and their
                        correspondence to Gabbro, plus `cCorr_block`;
    `CFormenM.lean`  -- pass (ii): the medium forms;
    `CFormenH.lean`  -- pass (iii): the hard forms.
  The syntax is closed here because Lean inductives are: every emitted
  form of all three passes has its constructor in this file, and its
  correspondence lemma in the file of its pass.

  WHAT THE EMITTED C IS, measured (emit.rs, read 2026-09-13, and one run
  of `target/debug/gabbro emit` on `beispiele/104-referenz.gab`)
    * integers: `uintN_t`/`intN_t`/`bool`, decimal literals of type `int`
      (a `u` suffix only above 2^63 - 1, `czahl`), every arithmetic
      operator printed bare (`a + b`), so C's integer promotions and usual
      arithmetic conversions decide the type an operator computes in --
      `uint8_t + uint8_t` computes in `int`, `uint32_t - int` in
      `uint32_t`. The model makes the computation type explicit at each
      operator node (`CX.bin op t l r`) and gives C's rules (`CIT.promote`,
      `uac`) so a certificate can check the annotation.
    * conversions: the explicit casts `(T)(e)` of `verenge`, `~`,
      `wrap_c`, `saturation_c`, and the implicit ones at `=`, `return` and
      argument passing (C11 6.3.1.3: modular into unsigned, identity into
      signed when the value fits, implementation-defined otherwise --
      stuck here).
    * statements: `=` and `op=` on a place, `T x = e;`, `if`/`else if`,
      `switch`/`case … break;`, `return`, `goto m_ende`/`goto m_weiter`
      (the only jumps: `leave`/`next`, labels at the loop end and body
      end), `for (…; c; step)` in every emitted shape (`retry`,
      `for (;;)`, the counting `traverse` header), calls, `(void)x;`.
  UB MEANS STUCK, as in `CSpeicher.lean`: every operator, conversion and
  access that C11 leaves undefined or implementation-defined in a way the
  subset must not depend on has no successor (`OpUB`, `ConvUB`, and the
  memory inventory of `CSpeicher.lean`).
-/
import Grammatik.CSpeicher

namespace Gabbro.Grammatik

/-! ## 1. C integer types and their ranges -/

/-- A C integer type: signedness and width (`uint8_t` … `int64_t`; `bool`
    is `uint8_t` for storage and `int` after promotion). -/
structure CIT where
  sgn : Bool
  w : CWidth
  deriving DecidableEq, Repr

namespace CIT

def lo (t : CIT) : Int := cLo t.sgn t.w
def hi (t : CIT) : Int := cHi t.sgn t.w
def ty (t : CIT) : CTy := .int t.sgn t.w
def bits (t : CIT) : Nat := t.w.bits

def u8 : CIT := ⟨false, .w8⟩
def u16 : CIT := ⟨false, .w16⟩
def u32 : CIT := ⟨false, .w32⟩
def u64 : CIT := ⟨false, .w64⟩
def i8 : CIT := ⟨true, .w8⟩
def i16 : CIT := ⟨true, .w16⟩
def i32 : CIT := ⟨true, .w32⟩
def i64 : CIT := ⟨true, .w64⟩

/-- The integer promotions (C11 6.3.1.1p2): every type narrower than
    `int` becomes `int` (all its values fit). -/
def promote (t : CIT) : CIT :=
  match t.w with
  | .w8 => i32
  | .w16 => i32
  | _ => t

/-- Does the type hold every integer of `lo .. hi`? The emitter's range
    guarantee at an operator (`M104`: "the result range must fit the
    width of the operands") is stated with this. -/
def holds (t : CIT) (lo hi : Int) : Prop := t.lo ≤ lo ∧ hi ≤ t.hi

instance (t : CIT) (lo hi : Int) : Decidable (t.holds lo hi) :=
  inferInstanceAs (Decidable (_ ∧ _))

end CIT

/-- The usual arithmetic conversions (C11 6.3.1.8) on the promoted
    operand types: same signedness -- the wider; otherwise the unsigned
    one if it is at least as wide, else the signed one (a wider signed
    type holds every value of a narrower unsigned one). -/
def uac (a b : CIT) : CIT :=
  let a' := a.promote
  let b' := b.promote
  if a'.sgn = b'.sgn then (if a'.w.bits ≤ b'.w.bits then b' else a')
  else
    let u := if a'.sgn then b' else a'
    let s := if a'.sgn then a' else b'
    if s.w.bits ≤ u.w.bits then u else s

/-- The pitfalls, computed: two `uint8_t` add in `int`; `uint32_t` against
    an `int` literal computes unsigned; `int64_t` against `uint32_t`
    computes signed. -/
theorem uac_werte :
    uac CIT.u8 CIT.u8 = CIT.i32 ∧ uac CIT.u16 CIT.u8 = CIT.i32 ∧
    uac CIT.u32 CIT.i32 = CIT.u32 ∧ uac CIT.i64 CIT.u32 = CIT.i64 ∧
    uac CIT.u64 CIT.i64 = CIT.u64 ∧ uac CIT.u32 CIT.u32 = CIT.u32 := by
  decide

theorem two_pow_pos' (n : Nat) : (0 : Int) < 2 ^ n := by
  have h0 : (0 : Nat) < 2 ^ n := Nat.pow_pos (by decide)
  have e : ((2 ^ n : Nat) : Int) = (2 : Int) ^ n := by simp
  omega

theorem CIT.lo_u {t : CIT} (h : t.sgn = false) : t.lo = 0 := by
  unfold CIT.lo cLo; rw [h]; rfl

theorem CIT.hi_u {t : CIT} (h : t.sgn = false) : t.hi = 2 ^ t.bits - 1 := by
  unfold CIT.hi cHi CIT.bits; rw [h]; rfl

theorem CIT.lo_le_zero (t : CIT) : t.lo ≤ 0 := by
  unfold CIT.lo cLo
  have := two_pow_pos' (t.w.bits - 1)
  split <;> omega

theorem CIT.hi_nonneg (t : CIT) : 0 ≤ t.hi := by
  unfold CIT.hi cHi
  have := two_pow_pos' t.w.bits
  have := two_pow_pos' (t.w.bits - 1)
  split <;> omega

/-- Unsigned wrap is the identity on the range. -/
theorem cWrap_of_range (w : CWidth) (v : Int) (h0 : 0 ≤ v) (h1 : v < 2 ^ w.bits) :
    cWrap w v = v := by
  show ((v % 2 ^ w.bits) + 2 ^ w.bits) % 2 ^ w.bits = v
  have e : (v + 2 ^ w.bits) % 2 ^ w.bits = v % 2 ^ w.bits := by
    have := Int.add_mul_emod_self_right v 1 (2 ^ w.bits)
    rwa [Int.one_mul] at this
  rw [Int.emod_eq_of_lt h0 h1, e, Int.emod_eq_of_lt h0 h1]

/-! ## 2. Conversions (C11 6.3.1.3) -/

/-- Conversion of an integer to type `t`: the value if it fits; modulo
    `2^w` into an unsigned type; STUCK into a signed type it does not fit
    (implementation-defined, 6.3.1.3p3 -- the subset must not depend on
    it). -/
def conv (t : CIT) (v : Int) : Option Int :=
  if t.lo ≤ v ∧ v ≤ t.hi then some v
  else if t.sgn = true then none else some (cWrap t.w v)

/-- The conversion UB inventory: a value outside a signed target. -/
inductive ConvUB (t : CIT) (v : Int) : Prop where
  | signed (hs : t.sgn = true) (h : v < t.lo ∨ t.hi < v)

theorem conv_id {t : CIT} {v : Int} (h : t.lo ≤ v ∧ v ≤ t.hi) : conv t v = some v := by
  unfold conv; rw [if_pos h]

theorem conv_none_iff (t : CIT) (v : Int) : conv t v = none ↔ ConvUB t v := by
  unfold conv
  constructor
  · intro h
    by_cases hr : t.lo ≤ v ∧ v ≤ t.hi
    · rw [if_pos hr] at h; exact absurd h (by simp)
    · rw [if_neg hr] at h
      by_cases hs : t.sgn = true
      · exact .signed hs (by omega)
      · rw [if_neg hs] at h; exact absurd h (by simp)
  · intro h
    cases h with
    | signed hs h => rw [if_neg (by omega), if_pos hs]

/-- Into an unsigned type the conversion never gets stuck and always lands
    in the range. -/
theorem conv_u {t : CIT} (hs : t.sgn = false) (v : Int) :
    ∃ r, conv t v = some r ∧ 0 ≤ r ∧ r ≤ t.hi := by
  unfold conv
  have hlo := CIT.lo_u hs
  have hhi := CIT.hi_u hs
  have hp := two_pow_pos' t.bits
  by_cases hr : t.lo ≤ v ∧ v ≤ t.hi
  · exact ⟨v, by rw [if_pos hr], by omega, hr.2⟩
  · rw [if_neg hr, if_neg (by rw [hs]; decide)]
    refine ⟨_, rfl, ?_, ?_⟩
    · show 0 ≤ ((v % 2 ^ t.w.bits) + 2 ^ t.w.bits) % 2 ^ t.w.bits
      exact Int.emod_nonneg _ (by unfold CIT.bits at hp; omega)
    · show ((v % 2 ^ t.w.bits) + 2 ^ t.w.bits) % 2 ^ t.w.bits ≤ t.hi
      have := Int.emod_lt_of_pos ((v % 2 ^ t.w.bits) + 2 ^ t.w.bits)
        (show (0:Int) < 2 ^ t.w.bits from hp)
      unfold CIT.bits at hhi; omega

/-! ## 3. The operators and their UB inventory

Lane 128's `cBinApply` is NOT reused: it computes signed `/` and `%` with
Lean's `Int./` and `Int.%`, which round toward minus infinity
(`Int.ediv`), where C truncates toward zero (C11 6.5.5p6: `-7 / 2 == -3`,
Lean `-7 / 2 = -4`); and it makes every bitwise operator on a signed type
stuck, which would make `a & b` on two `uint8_t` (computed in `int`) UB.
Here `/` and `%` are `Int.tdiv`/`Int.tmod`, and a bitwise operator is
defined on non-negative operands of any signedness. -/

/-- `a op b` with both operands already converted to the computation type
    `t`. `none` is STUCK. -/
def cArith (op : CBinOp) (t : CIT) (a b : Int) : Option Int :=
  match op with
  | .add => conv t (a + b)
  | .sub => conv t (a - b)
  | .mul => conv t (a * b)
  | .div => if b = 0 ∨ (t.sgn = true ∧ a = t.lo ∧ b = -1) then none else some (a.tdiv b)
  | .mod => if b = 0 ∨ (t.sgn = true ∧ a = t.lo ∧ b = -1) then none else some (a.tmod b)
  | .band => if 0 ≤ a ∧ 0 ≤ b then some ((a.toNat &&& b.toNat : Nat) : Int) else none
  | .bor => if 0 ≤ a ∧ 0 ≤ b then some ((a.toNat ||| b.toNat : Nat) : Int) else none
  | .bxor => if 0 ≤ a ∧ 0 ≤ b then some ((a.toNat ^^^ b.toNat : Nat) : Int) else none
  | .shl =>
      if 0 ≤ b ∧ b < (t.bits : Int) ∧ 0 ≤ a then
        (if t.sgn = true then
          (if a * 2 ^ b.toNat ≤ t.hi then some (a * 2 ^ b.toNat) else none)
         else some (cWrap t.w (a * 2 ^ b.toNat)))
      else none
  | .shr => if 0 ≤ b ∧ b < (t.bits : Int) ∧ 0 ≤ a then some (a / 2 ^ b.toNat) else none

/-- The operator UB inventory. Each constructor is one C11 undefined
    behaviour or one implementation-defined case the subset must not
    reach:
    - `ovAdd`/`ovSub`/`ovMul` -- signed overflow (6.5p5);
    - `divZero`               -- `/` or `%` by zero (6.5.5p5);
    - `divOvf`                -- `INT_MIN / -1` and `INT_MIN % -1` (6.5.5p6);
    - `shiftRange`            -- a shift count outside `0 ..< width` (6.5.7p3);
    - `shiftNeg`              -- a shift of a negative value (6.5.7p4-5:
                                 undefined left, implementation-defined right);
    - `shlOvf`                -- a signed left shift whose result does not
                                 fit (6.5.7p4);
    - `bitNeg`                -- `&`/`|`/`^` on a negative operand
                                 (representation-dependent, 6.2.6.2; the
                                 checker's `M137` admits only `0 ..`). -/
inductive OpUB (t : CIT) : CBinOp → Int → Int → Prop where
  | ovAdd (a b : Int) (hs : t.sgn = true) (h : a + b < t.lo ∨ t.hi < a + b) : OpUB t .add a b
  | ovSub (a b : Int) (hs : t.sgn = true) (h : a - b < t.lo ∨ t.hi < a - b) : OpUB t .sub a b
  | ovMul (a b : Int) (hs : t.sgn = true) (h : a * b < t.lo ∨ t.hi < a * b) : OpUB t .mul a b
  | divZero (op : CBinOp) (a b : Int) (hop : op = .div ∨ op = .mod) (h : b = 0) : OpUB t op a b
  | divOvf (op : CBinOp) (a b : Int) (hop : op = .div ∨ op = .mod) (hs : t.sgn = true)
      (ha : a = t.lo) (hb : b = -1) : OpUB t op a b
  | shiftRange (op : CBinOp) (a b : Int) (hop : op = .shl ∨ op = .shr)
      (h : b < 0 ∨ (t.bits : Int) ≤ b) : OpUB t op a b
  | shiftNeg (op : CBinOp) (a b : Int) (hop : op = .shl ∨ op = .shr) (h : a < 0) : OpUB t op a b
  | shlOvf (a b : Int) (hs : t.sgn = true) (hb : 0 ≤ b) (h : t.hi < a * 2 ^ b.toNat) :
      OpUB t .shl a b
  | bitNeg (op : CBinOp) (a b : Int) (hop : op = .band ∨ op = .bor ∨ op = .bxor)
      (h : a < 0 ∨ b < 0) : OpUB t op a b

/-- UB is stuck. -/
theorem opUB_stuck {t : CIT} {op : CBinOp} {a b : Int} (h : OpUB t op a b) :
    cArith op t a b = none := by
  cases h with
  | ovAdd _ _ hs h => exact (conv_none_iff t _).mpr (.signed hs h)
  | ovSub _ _ hs h => exact (conv_none_iff t _).mpr (.signed hs h)
  | ovMul _ _ hs h => exact (conv_none_iff t _).mpr (.signed hs h)
  | divZero _ _ _ hop h =>
      rcases hop with e | e <;> subst e <;> simp only [cArith] <;> rw [if_pos (Or.inl h)]
  | divOvf _ _ _ hop hs ha hb =>
      rcases hop with e | e <;> subst e <;> simp only [cArith] <;>
        rw [if_pos (Or.inr ⟨hs, ha, hb⟩)]
  | shiftRange _ _ _ hop h =>
      rcases hop with e | e <;> subst e <;> simp only [cArith] <;> rw [if_neg (by omega)]
  | shiftNeg _ _ _ hop h =>
      rcases hop with e | e <;> subst e <;> simp only [cArith] <;> rw [if_neg (by omega)]
  | shlOvf _ _ hs hb h =>
      simp only [cArith]
      by_cases hc : 0 ≤ b ∧ b < (t.bits : Int) ∧ 0 ≤ a
      · rw [if_pos hc, if_pos hs, if_neg (by omega)]
      · rw [if_neg hc]
  | bitNeg _ _ _ hop h =>
      rcases hop with e | e | e <;> subst e <;> simp only [cArith] <;> rw [if_neg (by omega)]

/-- Stuck is UB: the inventory is complete for the operators. -/
theorem opUB_of_stuck {t : CIT} {op : CBinOp} {a b : Int} (h : cArith op t a b = none) :
    OpUB t op a b := by
  cases op with
  | add =>
      obtain ⟨hs, hr⟩ := (conv_none_iff t _).mp h
      exact .ovAdd a b hs hr
  | sub =>
      obtain ⟨hs, hr⟩ := (conv_none_iff t _).mp h
      exact .ovSub a b hs hr
  | mul =>
      obtain ⟨hs, hr⟩ := (conv_none_iff t _).mp h
      exact .ovMul a b hs hr
  | div =>
      simp only [cArith] at h
      by_cases hc : b = 0 ∨ (t.sgn = true ∧ a = t.lo ∧ b = -1)
      · rcases hc with hz | ⟨hs, ha, hb⟩
        · exact .divZero _ a b (Or.inl rfl) hz
        · exact .divOvf _ a b (Or.inl rfl) hs ha hb
      · rw [if_neg hc] at h; exact absurd h (by simp)
  | mod =>
      simp only [cArith] at h
      by_cases hc : b = 0 ∨ (t.sgn = true ∧ a = t.lo ∧ b = -1)
      · rcases hc with hz | ⟨hs, ha, hb⟩
        · exact .divZero _ a b (Or.inr rfl) hz
        · exact .divOvf _ a b (Or.inr rfl) hs ha hb
      · rw [if_neg hc] at h; exact absurd h (by simp)
  | band =>
      simp only [cArith] at h
      by_cases hc : 0 ≤ a ∧ 0 ≤ b
      · rw [if_pos hc] at h; exact absurd h (by simp)
      · exact .bitNeg _ a b (Or.inl rfl) (by omega)
  | bor =>
      simp only [cArith] at h
      by_cases hc : 0 ≤ a ∧ 0 ≤ b
      · rw [if_pos hc] at h; exact absurd h (by simp)
      · exact .bitNeg _ a b (Or.inr (Or.inl rfl)) (by omega)
  | bxor =>
      simp only [cArith] at h
      by_cases hc : 0 ≤ a ∧ 0 ≤ b
      · rw [if_pos hc] at h; exact absurd h (by simp)
      · exact .bitNeg _ a b (Or.inr (Or.inr rfl)) (by omega)
  | shl =>
      simp only [cArith] at h
      by_cases hc : 0 ≤ b ∧ b < (t.bits : Int) ∧ 0 ≤ a
      · rw [if_pos hc] at h
        by_cases hs : t.sgn = true
        · rw [if_pos hs] at h
          by_cases hv : a * 2 ^ b.toNat ≤ t.hi
          · rw [if_pos hv] at h; exact absurd h (by simp)
          · exact .shlOvf a b hs hc.1 (by omega)
        · rw [if_neg hs] at h; exact absurd h (by simp)
      · by_cases ha : a < 0
        · exact .shiftNeg _ a b (Or.inl rfl) ha
        · exact .shiftRange _ a b (Or.inl rfl) (by omega)
  | shr =>
      simp only [cArith] at h
      by_cases hc : 0 ≤ b ∧ b < (t.bits : Int) ∧ 0 ≤ a
      · rw [if_pos hc] at h; exact absurd h (by simp)
      · by_cases ha : a < 0
        · exact .shiftNeg _ a b (Or.inr rfl) ha
        · exact .shiftRange _ a b (Or.inr rfl) (by omega)

theorem cArith_none_iff (op : CBinOp) (t : CIT) (a b : Int) :
    cArith op t a b = none ↔ OpUB t op a b :=
  ⟨opUB_of_stuck, opUB_stuck⟩

/-- C's truncating division against lane 128's: they differ on a negative
    dividend (the finding in the section header, computed). -/
theorem tdiv_ne_ediv : cArith .div CIT.i32 (-7) 2 = some (-3) ∧
    cBinApply .div true .w32 (-7) 2 = some (-4) := by
  decide

/-- The comparison operators; the result is an `int` `0` or `1`. -/
inductive CCmp where
  | lt | le | gt | ge | eq | ne
  deriving DecidableEq, Repr

def CCmp.app : CCmp → Int → Int → Bool
  | .lt, a, b => decide (a < b)
  | .le, a, b => decide (a ≤ b)
  | .gt, a, b => decide (b < a)
  | .ge, a, b => decide (b ≤ a)
  | .eq, a, b => decide (a = b)
  | .ne, a, b => decide (a ≠ b)

/-- A truth value as a C `int`. -/
def b2i (b : Bool) : Int := if b then 1 else 0

/-! ## 4. The expressions of the emitted subset -/

/-- The C local environment: parameters and locals whose address is never
    taken, holding integers or pointers; a declared-but-unwritten local is
    `undef`. -/
def CLok := Nat → CVal

def lokUpd (ρ : CLok) (x : Nat) (v : CVal) : CLok := fun y => if y = x then v else ρ y

/-- C's truth test on a scalar (6.8.4.1p2: "compares unequal to 0"). A
    pointer of the model is never null (null has no provenance). -/
def truth : CVal → Option Bool
  | .int v => some (decide (v ≠ 0))
  | .ptr _ => some true
  | .undef => none

/-- The emitted expressions. Each constructor is one emitted shape; the
    comments name it. Types the C compiler would infer from declarations
    are explicit (`t`, `τ`), so the node says what C computes. -/
inductive CX where
  /-- A decimal literal (`czahl`: `100`, `100u`; `true`/`false` are 1/0). -/
  | lit (v : Int)
  /-- A local or parameter, read. Reading an unwritten local is UB 8. -/
  | var (x : Nat)
  /-- `(T)(e)`: explicit conversion (`verenge`, `~`, `wrap_c`, `u64(a)`),
      also the implicit one of a declaration made explicit. -/
  | cast (t : CIT) (e : CX)
  /-- `l op r` in computation type `t` (after promotion and the usual
      arithmetic conversions): both operands converted to `t`. -/
  | bin (op : CBinOp) (t : CIT) (l r : CX)
  /-- `l < r` etc. in comparison type `t`; an `int` `0`/`1`. -/
  | cmp (op : CCmp) (t : CIT) (l r : CX)
  /-- `!(e)`. -/
  | lnot (e : CX)
  /-- `l && r`, short-circuit (6.5.13p4). -/
  | land (l r : CX)
  /-- `l || r`, short-circuit (6.5.14p4). -/
  | lor (l r : CX)
  /-- `c ? a : b`, result converted to `t` (6.5.15p5). -/
  | cond (t : CIT) (c a b : CX)
  /-- `~e` at the promoted type `t` (the emitter writes `(T)~(T)(x)`, which
      is `cast T (cpl (promote T) (cast T x))`). -/
  | cpl (t : CIT) (e : CX)
  /-- `sizeof(…)`: a `size_t` constant the layout computes. -/
  | szof (n : Nat)
  /-- `&obj` or the decay of a static object (`T_speicher`, `g`, a `static
      const` table, an arena's storage). -/
  | addr (b : CBlk)
  /-- `&x` of a local of the current frame (out-parameters, `&_cxN`, a
      by-value struct local `x.f`). -/
  | addrL (x : Nat)
  /-- `&p->f` / `&x.f`: a field at byte offset `off`. -/
  | fld (p : CX) (off : Nat)
  /-- `&p->slots[i].f`: record `i` of `n` (checked), field at `off`,
      records `ss` bytes apart. -/
  | slotA (p : CX) (i : CX) (n ss off : Nat)
  /-- `&a[i]`: element `i` of `n` (checked), `es` bytes each. -/
  | idx (p : CX) (i : CX) (n es : Nat)
  /-- `p + k` on a byte pointer (`v->bytes + K`, `d->basis + K`). -/
  | padd (p : CX) (k : CX)
  /-- The value of the object at address `p` (lvalue conversion, a plain
      load of a cell of type `τ`). -/
  | ld (p : CX) (τ : CTy)
  /-- `*(volatile uintN_t *)(p)`: a volatile load, an observation. -/
  | vld (p : CX) (τ : CTy)
  /-- `atomic_load_explicit(p, o)`, and the implicit `seq_cst` load of a
      bare `_Atomic` name. -/
  | ald (p : CX) (τ : CTy) (o : COrd)
  /-- `(volatile uint8_t *)(uintptr_t)a`: the handle of device `d`. -/
  | devH (d : Nat) (a : Int)
  /-- `__builtin_trap()`: a defined abort, no successor (the byte helpers'
      bound check; unreachable under the checker's bound). -/
  | trap
  deriving Repr

variable (L : CLayout) (orc : DevOrc) (fr : Nat)

/-- EXPRESSION SEMANTICS on the block memory, frame `fr`, locals `ρ`:
    the value and the state after the observations the expression made
    (volatile and atomic loads append to the trace; nothing else changes).
    Operands are evaluated left to right; C leaves the order unspecified,
    which matters only for two observing subexpressions in one full
    expression (CUTS). `none` is STUCK. -/
def ev : CX → CSt → CLok → Option (CVal × CSt)
  | .lit v, st, _ => some (.int v, st)
  | .var x, st, ρ =>
      match ρ x with
      | .undef => none
      | .int v => some (.int v, st)
      | .ptr p => some (.ptr p, st)
  | .cast t e, st, ρ =>
      match ev e st ρ with
      | some (.int a, st1) =>
          match conv t a with
          | some b => some (.int b, st1)
          | none => none
      | _ => none
  | .bin op t l r, st, ρ =>
      match ev l st ρ with
      | some (.int a, st1) =>
          match ev r st1 ρ with
          | some (.int b, st2) =>
              match conv t a, conv t b with
              | some a', some b' =>
                  match cArith op t a' b' with
                  | some c => some (.int c, st2)
                  | none => none
              | _, _ => none
          | _ => none
      | _ => none
  | .cmp op t l r, st, ρ =>
      match ev l st ρ with
      | some (.int a, st1) =>
          match ev r st1 ρ with
          | some (.int b, st2) =>
              match conv t a, conv t b with
              | some a', some b' => some (.int (b2i (op.app a' b')), st2)
              | _, _ => none
          | _ => none
      | _ => none
  | .lnot e, st, ρ =>
      match ev e st ρ with
      | some (v, st1) =>
          match truth v with
          | some b => some (.int (b2i (!b)), st1)
          | none => none
      | none => none
  | .land l r, st, ρ =>
      match ev l st ρ with
      | some (v, st1) =>
          match truth v with
          | some false => some (.int 0, st1)
          | some true =>
              match ev r st1 ρ with
              | some (w, st2) =>
                  match truth w with
                  | some b => some (.int (b2i b), st2)
                  | none => none
              | none => none
          | none => none
      | none => none
  | .lor l r, st, ρ =>
      match ev l st ρ with
      | some (v, st1) =>
          match truth v with
          | some true => some (.int 1, st1)
          | some false =>
              match ev r st1 ρ with
              | some (w, st2) =>
                  match truth w with
                  | some b => some (.int (b2i b), st2)
                  | none => none
              | none => none
          | none => none
      | none => none
  | .cond t c a b, st, ρ =>
      match ev c st ρ with
      | some (v, st1) =>
          match truth v with
          | some true =>
              match ev a st1 ρ with
              | some (.int x, st2) =>
                  match conv t x with
                  | some y => some (.int y, st2)
                  | none => none
              | _ => none
          | some false =>
              match ev b st1 ρ with
              | some (.int x, st2) =>
                  match conv t x with
                  | some y => some (.int y, st2)
                  | none => none
              | _ => none
          | none => none
      | none => none
  | .cpl t e, st, ρ =>
      match ev e st ρ with
      | some (.int a, st1) =>
          match conv t a with
          | some a' => some (.int (if t.sgn then -a' - 1 else t.hi - a'), st1)
          | none => none
      | _ => none
  | .szof n, st, _ => some (.int n, st)
  | .addr b, st, _ => some (.ptr ⟨b, 0⟩, st)
  | .addrL x, st, _ => some (.ptr ⟨.stk fr x, 0⟩, st)
  | .fld p off, st, ρ =>
      match ev p st ρ with
      | some (.ptr q, st1) =>
          match ptrAdd L q off 1 with
          | some q' => some (.ptr q', st1)
          | none => none
      | _ => none
  | .slotA p i n ss off, st, ρ =>
      match ev p st ρ with
      | some (.ptr q, st1) =>
          match ev i st1 ρ with
          | some (.int k, st2) =>
              if 0 ≤ k ∧ k < (n : Int) then
                match ptrAdd L q (k * ss + off) 1 with
                | some q' => some (.ptr q', st2)
                | none => none
              else none
          | _ => none
      | _ => none
  | .idx p i n es, st, ρ =>
      match ev p st ρ with
      | some (.ptr q, st1) =>
          match ev i st1 ρ with
          | some (.int k, st2) =>
              if 0 ≤ k ∧ k < (n : Int) then
                match ptrAdd L q (k * es) 1 with
                | some q' => some (.ptr q', st2)
                | none => none
              else none
          | _ => none
      | _ => none
  | .padd p k, st, ρ =>
      match ev p st ρ with
      | some (.ptr q, st1) =>
          match ev k st1 ρ with
          | some (.int m, st2) =>
              match ptrAdd L q m 1 with
              | some q' => some (.ptr q', st2)
              | none => none
          | _ => none
      | _ => none
  | .ld p τ, st, ρ =>
      match ev p st ρ with
      | some (.ptr q, st1) =>
          match bLoad L st1 q τ with
          | some v => some (v, st1)
          | none => none
      | _ => none
  | .vld p τ, st, ρ =>
      match ev p st ρ with
      | some (.ptr q, st1) =>
          match vLoad L orc st1 q τ with
          | some (v, st2) => some (.int v, st2)
          | none => none
      | _ => none
  | .ald p τ o, st, ρ =>
      match ev p st ρ with
      | some (.ptr q, st1) =>
          match aLoad L st1 q τ o with
          | some (v, st2) => some (.int v, st2)
          | none => none
      | _ => none
  | .devH d a, st, _ =>
      match devHandle L d a with
      | some q => some (.ptr q, st)
      | none => none
  | .trap, _, _ => none

/-- Memory and liveness of two states agree: what every correspondence
    reads. Expressions change neither. -/
def SameML (st st' : CSt) : Prop := st'.mem = st.mem ∧ st'.live = st.live

theorem SameML.refl (st : CSt) : SameML st st := ⟨rfl, rfl⟩

theorem SameML.trans {a b c : CSt} (h1 : SameML a b) (h2 : SameML b c) : SameML a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem vLoad_same {st st' : CSt} {p : CPtr} {τ : CTy} {v : Int}
    (h : vLoad L orc st p τ = some (v, st')) : SameML st st' := by
  unfold vLoad at h
  cases hc : accOk L st p τ .vol with
  | false => rw [hc] at h; exact absurd h (by simp)
  | true =>
      rw [if_pos hc] at h
      cases τ with
      | ptr => exact absurd h (by simp)
      | int sgn w =>
          cases sgn with
          | true => exact absurd h (by simp)
          | false =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, h2⟩ := h
              subst h2
              exact ⟨rfl, rfl⟩

theorem aLoad_same {st st' : CSt} {p : CPtr} {τ : CTy} {o : COrd} {v : Int}
    (h : aLoad L st p τ o = some (v, st')) : SameML st st' := by
  unfold aLoad at h
  cases hc : (accOk L st p τ .atom && o.loadOk) with
  | false => rw [hc] at h; exact absurd h (by simp)
  | true =>
      rw [if_pos hc] at h
      cases hm : st.mem p.blk p.off.toNat with
      | int w =>
          rw [hm] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, h2⟩ := h
          subst h2
          exact ⟨rfl, rfl⟩
      | ptr _ => rw [hm] at h; exact absurd h (by simp)
      | undef => rw [hm] at h; exact absurd h (by simp)

/-- EXPRESSIONS CHANGE NO MEMORY: an evaluation keeps every cell and
    every lifetime; only the trace may grow. -/
theorem ev_same : ∀ (c : CX) (st : CSt) (ρ : CLok) (v : CVal) (st' : CSt),
    ev L orc fr c st ρ = some (v, st') → SameML st st' := by
  intro c
  induction c with
  | lit n => intro st ρ v st' h; simp only [ev, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact SameML.refl _
  | var x =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · exact absurd h (by simp)
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact SameML.refl _
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact SameML.refl _
  | cast t e ih =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · rename_i a st1 he
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact ih _ _ _ _ he
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | bin op t l r ihl ihr =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · rename_i a st1 hl
        split at h
        · rename_i b st2 hr
          split at h
          · split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
              exact (ihl _ _ _ _ hl).trans (ihr _ _ _ _ hr)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | cmp op t l r ihl ihr =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · rename_i a st1 hl
        split at h
        · rename_i b st2 hr
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
            exact (ihl _ _ _ _ hl).trans (ihr _ _ _ _ hr)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | lnot e ih =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · rename_i a st1 he
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact ih _ _ _ _ he
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | land l r ihl ihr =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · rename_i a st1 hl
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact ihl _ _ _ _ hl
        · split at h
          · rename_i w st2 hr
            split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
              exact (ihl _ _ _ _ hl).trans (ihr _ _ _ _ hr)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | lor l r ihl ihr =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · rename_i a st1 hl
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact ihl _ _ _ _ hl
        · split at h
          · rename_i w st2 hr
            split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
              exact (ihl _ _ _ _ hl).trans (ihr _ _ _ _ hr)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | cond t c a b ihc iha ihb =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · rename_i x st1 hc
        split at h
        · split at h
          · rename_i y st2 ha
            split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
              exact (ihc _ _ _ _ hc).trans (iha _ _ _ _ ha)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · split at h
          · rename_i y st2 hb
            split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
              exact (ihc _ _ _ _ hc).trans (ihb _ _ _ _ hb)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | cpl t e ih =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · rename_i a st1 he
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact ih _ _ _ _ he
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | szof n => intro st ρ v st' h; simp only [ev, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact SameML.refl _
  | addr b => intro st ρ v st' h; simp only [ev, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact SameML.refl _
  | addrL x => intro st ρ v st' h; simp only [ev, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact SameML.refl _
  | fld p off ih =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · rename_i q st1 hp
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact ih _ _ _ _ hp
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | slotA p i n ss off ihp ihi =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · rename_i q st1 hp
        split at h
        · rename_i k st2 hi
          split at h
          · split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
              exact (ihp _ _ _ _ hp).trans (ihi _ _ _ _ hi)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | idx p i n es ihp ihi =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · rename_i q st1 hp
        split at h
        · rename_i k st2 hi
          split at h
          · split at h
            · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
              exact (ihp _ _ _ _ hp).trans (ihi _ _ _ _ hi)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | padd p k ihp ihk =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · rename_i q st1 hp
        split at h
        · rename_i m st2 hk
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
            exact (ihp _ _ _ _ hp).trans (ihk _ _ _ _ hk)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | ld p τ ih =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · rename_i q st1 hp
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact ih _ _ _ _ hp
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | vld p τ ih =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · rename_i q st1 hp
        split at h
        · rename_i w st2 hv
          simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
          exact (ih _ _ _ _ hp).trans (vLoad_same L orc hv)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | ald p τ o ih =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · rename_i q st1 hp
        split at h
        · rename_i w st2 hv
          simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]
          exact (ih _ _ _ _ hp).trans (aLoad_same L hv)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
  | devH d a =>
      intro st ρ v st' h
      simp only [ev] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact SameML.refl _
      · exact absurd h (by simp)
  | trap => intro st ρ v st' h; simp [ev] at h

/-! ## 5. The statements of the emitted subset -/

/-- The only jump targets the emitter writes, per loop mark `m`:
    `m_weiter: ;` as the last statement of the loop body and `m_ende: ;`
    right after the loop (emit.rs 9664/9671, 9921/9925). `goto` is emitted
    for `leave m`/`next m` only (9235) and for the `exchange update` body
    (10017, `_cnN_fertig`, a jump to the end of its own block). -/
inductive CLbl where
  | weiter (m : Nat)
  | ende (m : Nat)
  deriving DecidableEq, Repr

/-- The emitted statements. -/
inductive CS where
  | skip
  | seq (a b : CS)
  /-- `e;` -- a call kept for its effect, or `(void)x;`. -/
  | expr (e : CX)
  /-- `T x = e;` and `x = e;` on a local: the value converted to `τ`. -/
  | set (x : Nat) (τ : CTy) (e : CX)
  /-- `lv = e;` on a place in memory (`k->slots[i].f = e;`,
      `T_speicher.slots[i].f = e;`, `g = e;`, `*_wert = e;`). -/
  | store (p : CX) (τ : CTy) (e : CX)
  /-- `(*(volatile uintN_t *)(p)) = e;` -/
  | vstore (p : CX) (τ : CTy) (e : CX)
  /-- `atomic_store_explicit(p, e, o);` and the implicit `seq_cst` store
      `g = e;` to a bare `_Atomic` name. -/
  | astore (p : CX) (τ : CTy) (o : COrd) (e : CX)
  /-- `ok = atomic_compare_exchange_{strong,weak}_explicit(p, ex, des,
      os, of);` -- `ex` points to the expected local `_cxN`, which a
      failure overwrites with the value seen. -/
  | acas (ok : Nat) (p : CX) (τ : CTy) (ex : CX) (des : CX) (os of : COrd)
  | ite (c : CX) (a b : CS)
  /-- `switch (e) { case k: { … } break; … }` -- no `default`, no
      fall-through (every arm ends in `break;`, 10775/10837). -/
  | sw (e : CX) (arms : List (Int × CS))
  /-- `return;` / `return e;` (converted to the declared return type). -/
  | ret (e : Option (CTy × CX))
  | brk
  | cont
  | goto (l : CLbl)
  /-- `for (; c; step) { body m_weiter: ; } m_ende: ;` -- every emitted
      loop: `retry` (9658), `for (;;)` (`c = 1`, `step = skip`), the
      counting `traverse` header (after its initialisation, `CS.forUp`). -/
  | forC (c : CX) (step : CS) (body : CS) (m : Nat)
  /-- `f(a, b);`, `T x = f(a, b);`. -/
  | call (f : Nat) (args : List CX) (dst : Option (Nat × CTy))
  /-- A foreign call: `L_nimm();`, `L_gib();`, an `extern fn`, the
      syscall stub. Its effect is an ASSUMPTION (the relation `XR`),
      bounded by its declared frame (`CFormenH.lean`). -/
  | ext (n : Nat) (args : List CX) (dst : Option (Nat × CTy))

/-- The counting loop the `traverse` header writes:
    `for (uint32_t v = lo; v < hi; v += 1) body`. The increment is
    `v = v + 1` in `t` (`uac t int = t` for the emitted `uint32_t` and
    `uint64_t`). -/
def CS.forUp (x : Nat) (t : CIT) (lo hi : CX) (body : CS) (m : Nat) : CS :=
  .seq (.set x t.ty lo)
    (.forC (.cmp .lt t (.var x) hi) (.set x t.ty (.bin .add t (.var x) (.lit 1))) body m)

/-- `for (;;) body` (`forever`, the CAS loop). -/
def CS.loop (body : CS) (m : Nat) : CS := .forC (.lit 1) .skip body m

/-- How a statement ends. -/
inductive COut where
  | norm (st : CSt) (ρ : CLok)
  | ret (st : CSt) (v : Option CVal)
  | brk (st : CSt) (ρ : CLok)
  | cont (st : CSt) (ρ : CLok)
  | jump (l : CLbl) (st : CSt) (ρ : CLok)

/-- Every outcome but the normal one leaves a sequence. -/
def COut.abrupt : COut → Bool
  | .norm _ _ => false
  | _ => true

/-- After a loop body: the next iteration (the body finished, `continue`d,
    or jumped to its own `m_weiter`, the last statement of the body). -/
def COut.weiter (m : Nat) : COut → Option (CSt × CLok)
  | .norm st ρ => some (st, ρ)
  | .cont st ρ => some (st, ρ)
  | .jump (.weiter m') st ρ => if m' = m then some (st, ρ) else none
  | _ => none

/-- After a loop body: the loop is over with this outcome -- `break;` or a
    jump to its own `m_ende` (right after the loop) end it normally; a
    `return` or a jump to an OUTER label leaves it as it is. -/
def COut.raus (m : Nat) : COut → Option COut
  | .brk st ρ => some (.norm st ρ)
  | .jump (.ende m') st ρ => if m' = m then some (.norm st ρ) else some (.jump (.ende m') st ρ)
  | .jump (.weiter m') st ρ => if m' = m then none else some (.jump (.weiter m') st ρ)
  | .ret st v => some (.ret st v)
  | _ => none

/-- A `switch` arm's closing `break;` ends the switch. -/
def COut.unbreak : COut → COut
  | .brk st ρ => .norm st ρ
  | o => o

/-- Conversion at `=`, `return` and argument passing (6.5.16.1p2). -/
def convV : CTy → CVal → Option CVal
  | .int s w, .int v =>
      match conv ⟨s, w⟩ v with
      | some b => some (.int b)
      | none => none
  | .ptr, .ptr p => some (.ptr p)
  | _, _ => none

/-- Arguments, left to right (pure in the emitted calls; CUTS). -/
def evArgs : List CX → CSt → CLok → Option (List CVal × CSt)
  | [], st, _ => some ([], st)
  | e :: es, st, ρ =>
      match ev L orc fr e st ρ with
      | some (v, st1) =>
          match evArgs es st1 ρ with
          | some (vs, st2) => some (v :: vs, st2)
          | none => none
      | none => none

/-- Where a call's answer goes. -/
def putDst : Option (Nat × CTy) → Option CVal → CLok → Option CLok
  | none, _, ρ => some ρ
  | some (x, τ), some v, ρ =>
      match convV τ v with
      | some v' => some (lokUpd ρ x v')
      | none => none
  | some _, none, _ => none

/-- A call's meaning: function, state, arguments, final state, answer. -/
def CCallR := Nat → CSt → List CVal → CSt → Option CVal → Prop

/-- STATEMENT SEMANTICS (big-step): `Exec CR XR s st ρ o` -- from state
    `st` and locals `ρ`, statement `s` ends with `o`. No derivation is
    STUCK or divergence. `CR` gives the meaning of calls to functions of
    the unit (built by `CallAt`), `XR` of foreign calls (an assumption). -/
inductive Exec (CR XR : CCallR) : CS → CSt → CLok → COut → Prop where
  | skip {st ρ} : Exec CR XR .skip st ρ (.norm st ρ)
  | seqN {a b st ρ st1 ρ1 o} (h1 : Exec CR XR a st ρ (.norm st1 ρ1))
      (h2 : Exec CR XR b st1 ρ1 o) : Exec CR XR (.seq a b) st ρ o
  | seqX {a b st ρ o} (h1 : Exec CR XR a st ρ o) (hx : o.abrupt = true) :
      Exec CR XR (.seq a b) st ρ o
  | expr {e st ρ v st1} (h : ev L orc fr e st ρ = some (v, st1)) :
      Exec CR XR (.expr e) st ρ (.norm st1 ρ)
  | set {x τ e st ρ v st1 v'} (h : ev L orc fr e st ρ = some (v, st1))
      (hc : convV τ v = some v') : Exec CR XR (.set x τ e) st ρ (.norm st1 (lokUpd ρ x v'))
  | store {p τ e st ρ q st1 v st2 v' st3} (hp : ev L orc fr p st ρ = some (.ptr q, st1))
      (he : ev L orc fr e st1 ρ = some (v, st2)) (hc : convV τ v = some v')
      (hs : bStore L st2 q τ v' = some st3) : Exec CR XR (.store p τ e) st ρ (.norm st3 ρ)
  | vstore {p τ e st ρ q st1 v st2 n st3} (hp : ev L orc fr p st ρ = some (.ptr q, st1))
      (he : ev L orc fr e st1 ρ = some (v, st2)) (hc : convV τ v = some (.int n))
      (hs : vStore L st2 q τ n = some st3) : Exec CR XR (.vstore p τ e) st ρ (.norm st3 ρ)
  | astore {p τ o e st ρ q st1 v st2 n st3} (hp : ev L orc fr p st ρ = some (.ptr q, st1))
      (he : ev L orc fr e st1 ρ = some (v, st2)) (hc : convV τ v = some (.int n))
      (hs : aStore L st2 q τ o n = some st3) : Exec CR XR (.astore p τ o e) st ρ (.norm st3 ρ)
  | acas {ok p τ ex des os of st ρ q st1 qx st2 v st3 d e0 b seen st4 st5}
      (hp : ev L orc fr p st ρ = some (.ptr q, st1))
      (hx : ev L orc fr ex st1 ρ = some (.ptr qx, st2))
      (hd : ev L orc fr des st2 ρ = some (v, st3)) (hc : convV τ v = some (.int d))
      (hl : bLoad L st3 qx τ = some (.int e0))
      (ha : aCas L st3 q τ os of e0 d = some (b, seen, st4))
      (hw : (if b then some st4 else bStore L st4 qx τ (.int seen)) = some st5) :
      Exec CR XR (.acas ok p τ ex des os of) st ρ (.norm st5 (lokUpd ρ ok (.int (b2i b))))
  | iteT {c a b st ρ v st1 o} (hc : ev L orc fr c st ρ = some (v, st1))
      (ht : truth v = some true) (h : Exec CR XR a st1 ρ o) : Exec CR XR (.ite c a b) st ρ o
  | iteF {c a b st ρ v st1 o} (hc : ev L orc fr c st ρ = some (v, st1))
      (ht : truth v = some false) (h : Exec CR XR b st1 ρ o) : Exec CR XR (.ite c a b) st ρ o
  | swHit {e arms st ρ k st1 s o} (he : ev L orc fr e st ρ = some (.int k, st1))
      (hl : arms.lookup k = some s) (h : Exec CR XR s st1 ρ o) :
      Exec CR XR (.sw e arms) st ρ o.unbreak
  | swMiss {e arms st ρ k st1} (he : ev L orc fr e st ρ = some (.int k, st1))
      (hl : arms.lookup k = none) : Exec CR XR (.sw e arms) st ρ (.norm st1 ρ)
  | retN {st ρ} : Exec CR XR (.ret none) st ρ (.ret st none)
  | retS {τ e st ρ v st1 v'} (he : ev L orc fr e st ρ = some (v, st1))
      (hc : convV τ v = some v') : Exec CR XR (.ret (some (τ, e))) st ρ (.ret st1 (some v'))
  | brk {st ρ} : Exec CR XR .brk st ρ (.brk st ρ)
  | cont {st ρ} : Exec CR XR .cont st ρ (.cont st ρ)
  | goto {l st ρ} : Exec CR XR (.goto l) st ρ (.jump l st ρ)
  | forDone {c step body m st ρ v st1} (hc : ev L orc fr c st ρ = some (v, st1))
      (hf : truth v = some false) : Exec CR XR (.forC c step body m) st ρ (.norm st1 ρ)
  | forStep {c step body m st ρ v st1 o1 st2 ρ2 st3 ρ3 o}
      (hc : ev L orc fr c st ρ = some (v, st1)) (ht : truth v = some true)
      (hb : Exec CR XR body st1 ρ o1) (hw : o1.weiter m = some (st2, ρ2))
      (hs : Exec CR XR step st2 ρ2 (.norm st3 ρ3))
      (hr : Exec CR XR (.forC c step body m) st3 ρ3 o) : Exec CR XR (.forC c step body m) st ρ o
  | forExit {c step body m st ρ v st1 o1 o}
      (hc : ev L orc fr c st ρ = some (v, st1)) (ht : truth v = some true)
      (hb : Exec CR XR body st1 ρ o1) (hx : o1.raus m = some o) :
      Exec CR XR (.forC c step body m) st ρ o
  | call {f args dst st ρ vs st1 st2 rv ρ'} (ha : evArgs L orc fr args st ρ = some (vs, st1))
      (hc : CR f st1 vs st2 rv) (hd : putDst dst rv ρ = some ρ') :
      Exec CR XR (.call f args dst) st ρ (.norm st2 ρ')
  | ext {n args dst st ρ vs st1 st2 rv ρ'} (ha : evArgs L orc fr args st ρ = some (vs, st1))
      (hc : XR n st1 vs st2 rv) (hd : putDst dst rv ρ = some ρ') :
      Exec CR XR (.ext n args dst) st ρ (.norm st2 ρ')

/-- A C function of the unit: its parameters (local and declared type),
    the locals whose address it takes (stack blocks of its frame), and
    its body. -/
structure CFun where
  params : List (Nat × CTy)
  locals : List Nat
  body : CS

/-- Parameter passing: each argument converted to its parameter's type
    (6.5.2.2p7); every other local starts unwritten. -/
def bindParams : List (Nat × CTy) → List CVal → Option CLok
  | [], [] => some (fun _ => .undef)
  | (x, τ) :: ps, v :: vs =>
      match convV τ v, bindParams ps vs with
      | some v', some ρ => some (lokUpd ρ x v')
      | _, _ => none
  | _, _ => none

/-- The functions of a unit, by number. -/
def CProg := Nat → Option CFun

/-- THE C CALL, at call depth `n`: the callee runs in frame `n` (its
    address-taken locals are the blocks `stk n x`, alive and unwritten on
    entry, dead after the return), with the callees it calls at depth
    `n - 1`. Falling off the end of a `void` function is `return;`. The
    depth is Gabbro's `rufAt` fuel, so the two call trees line up. -/
def CallAt (XR : CCallR) (Pr : CProg) : Nat → CCallR
  | 0 => fun _ _ _ _ _ => False
  | n + 1 => fun f st vs st' rv =>
      ∃ (F : CFun) (ρ0 : CLok) (o : COut), Pr f = some F ∧ bindParams F.params vs = some ρ0 ∧
        Exec L orc (n + 1) (CallAt XR Pr n) XR F.body (enterFrame st (n + 1) F.locals) ρ0 o ∧
        ∃ st1, (o = .ret st1 rv ∨ (rv = none ∧ ∃ ρ1, o = .norm st1 ρ1)) ∧
          st' = leaveFrame st1 (n + 1)

/-
CUTS: what this file does not do, by name.
- EVALUATION ORDER is fixed left to right. C leaves the order of operand
  evaluation unspecified (6.5p3), which is observable only through two
  observing subexpressions (volatile or atomic loads) in one full
  expression; the model does not check that there is at most one.
- NO DETERMINISM THEOREM for `Exec`: it is deterministic given `CR`, `XR`
  and the device oracle (every rule's premises fix the outcome), but that
  is not proved; the correspondence lemmas therefore say "the C statement
  has a run that …", not "every run".
- CALLS IN EXPRESSIONS are not a form: `CX` has no call node. The
  emitter's pure helpers (`_gabbro_sat_*`, the byte readers `gabbro_le32`
  …, the bank and format accessors) are proved as functions of their
  arguments (their bodies run by `Exec`, or their return expression
  inlined), not at the call site.
- `goto` is modelled only in the two emitted shapes (a jump to the end of
  the current loop body or to right after the loop), as a labelled
  outcome that the loop of that label consumes. The `exchange update`
  body's `goto _cnN_fertig` (a jump to the end of its own block) is not
  modelled.
- `~` on a negative signed operand, `>>` of a negative value and bitwise
  operators on negative operands are stuck (representation-dependent in
  C11); the checker's `M137` never produces them.
- FRAMES are numbered by call depth (`CallAt`): the stack discipline, not
  fresh block identities; a pointer into a dead frame revives when a call
  at the same depth reuses the frame number (CSpeicher.lean's CUT).
- Lane 128's `cBinApply` computes signed `/` and `%` with Euclidean
  rounding, which is not C's (`tdiv_ne_ediv`); `CSemantik.lean` is left
  as it is (its theorems are about unsigned `uint32_t`, where the two
  agree), and this file does not use it.
-/

#print axioms uac_werte
#print axioms conv_none_iff
#print axioms opUB_stuck
#print axioms opUB_of_stuck
#print axioms cArith_none_iff
#print axioms tdiv_ne_ediv
#print axioms ev_same

end Gabbro.Grammatik
