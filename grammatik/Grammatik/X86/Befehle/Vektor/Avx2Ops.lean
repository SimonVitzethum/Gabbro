/-
  File:      Grammatik/X86/Avx2Ops.lean
  Subject:   AVX2 256-bit integer operation semantics (pure functions).

  Lane 1239 (Tier 3, first OPTIONAL selected-CPU profile): pure semantic
  functions on 256-bit values, modelled as a pair of 128-bit halves, for
  the integer ops VPADD/VPSUB B/W/D/Q, VPAND/VPOR/VPXOR/VPANDN,
  VPCMPEQ B/W/D/Q, VPSLL/VPSRL/VPSRA by immediate. Each half reuses the
  accepted `Vektor` lane vocabulary (`vecAdd`, `vecSub`, `vecAnd`,
  `vecOr`, `vecXor`); nothing is redefined. No shuffle/permute, no
  gather, no FMA. No decoder, no register file, no machine step here:
  those belong to the sibling AVX2 pieces (Vex, State, Mem).

  Manual provenance (checked 2026-10-05, clone-local
  `.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
  Intel SDM 325462-093US September 2026): VPANDN operand order
  `DEST := (NOT SRC1) AND SRC2` (lines 40830, 74796-74797); VPCMPEQ
  equal lanes fill with FFH else 0 (lines 75960-75989); PSLLW/D/Q
  `COUNT > 15/31/63` zeroes the destination (lines 85640-85714);
  PSRAW/D `COUNT > 15/31` clamps to `16/32` so lanes become their
  sign fill (lines 86274-86325); VPSRAQ exists EVEX-only, never VEX
  (lines 86120-86129 vs 86511-86530: no VEX.256 VPSRAQ row).
  VEX.256 immediate shifts act per 128-bit lane (VPSLLW/D/Q ymm
  rows, lines 85485-85504). No page or quotation beyond these line
  citations is claimed; silicon correspondence stays OPEN (see CUTS).
-/
import Grammatik.X86.Befehle.Vektor.VectorIntegerHardwareForms
import Grammatik.X86.Befehle.Vektor.VectorHardwareProfile
import Grammatik.X86.Flags.FeatureProfile

namespace Gabbro.Grammatik.X86

/-- A 256-bit AVX2 integer value: the low and high 128-bit halves.
    AVX2 integer ops act within each 128-bit lane, so the pair is the
    faithful shape (no cross-half carry exists by construction). -/
abbrev Ymm := Vektor × Vektor

/-- Low 128-bit half of a 256-bit value. -/
def ymmLo (y : Ymm) : Vektor := y.1

/-- High 128-bit half of a 256-bit value. -/
def ymmHi (y : Ymm) : Vektor := y.2

/-! ## 1. 256-bit integer add/sub/logic, per 128-bit half.

  Each half reuses the accepted 128-bit lane operator; the old evaluator
  is lifted, never redefined. `ymmAndn x y` is `(NOT x) AND y` (Intel
  VPANDN operand order), complement taken within the lane width. -/

/-- VPADD B/W/D/Q over 256 bits: accepted lane add per half. -/
def ymmAdd (b : Breite) (x y : Ymm) : Ymm :=
  (vecAdd b x.1 y.1, vecAdd b x.2 y.2)

/-- VPSUB B/W/D/Q over 256 bits: accepted lane sub per half. -/
def ymmSub (b : Breite) (x y : Ymm) : Ymm :=
  (vecSub b x.1 y.1, vecSub b x.2 y.2)

/-- VPAND over 256 bits: accepted lane and per half. -/
def ymmAnd (b : Breite) (x y : Ymm) : Ymm :=
  (vecAnd b x.1 y.1, vecAnd b x.2 y.2)

/-- VPOR over 256 bits: accepted lane or per half. -/
def ymmOr (b : Breite) (x y : Ymm) : Ymm :=
  (vecOr b x.1 y.1, vecOr b x.2 y.2)

/-- VPXOR over 256 bits: accepted lane xor per half. -/
def ymmXor (b : Breite) (x y : Ymm) : Ymm :=
  (vecXor b x.1 y.1, vecXor b x.2 y.2)

/-- VPANDN over 256 bits: `(NOT x) AND y` per lane. Both lane values are
    below `2 ^ w`, so xor with `2 ^ w - 1` is the width-local complement
    (no accepted ANDN model exists to reuse; this is built from the
    accepted `laneNat`/`vecMk` vocabulary only). -/
def ymmAndn (b : Breite) (x y : Ymm) : Ymm :=
  (vecMk b (fun i => (laneNat b x.1 i ^^^ (2 ^ b.bits - 1)) &&& laneNat b y.1 i),
   vecMk b (fun i => (laneNat b x.2 i ^^^ (2 ^ b.bits - 1)) &&& laneNat b y.2 i))

/-- VPCMPEQ of one 128-bit half: the lane is all-ones on equality and
    zero otherwise (Intel SDM: equal lanes fill with 1s). -/
def vecCmpeq (b : Breite) (x y : Vektor) : Vektor :=
  vecMk b (fun i => if laneNat b x i == laneNat b y i then 2 ^ b.bits - 1 else 0)

/-- VPCMPEQ B/W/D/Q over 256 bits. -/
def ymmCmpeq (b : Breite) (x y : Ymm) : Ymm :=
  (vecCmpeq b x.1 y.1, vecCmpeq b x.2 y.2)

/-! ## 2. Half agreement: each 128-bit half IS the accepted SSE2 word.

  The exact agreement statement this file owes: both halves of every
  256-bit op are definitionally the accepted 128-bit packed operator
  applied to the corresponding halves. -/

/-- Both halves of a 256-bit add are the accepted packed add. -/
theorem ymmAdd_halb (b : Breite) (x y : Ymm) :
    (ymmAdd b x y).1 = vecAdd b x.1 y.1 ∧
      (ymmAdd b x y).2 = vecAdd b x.2 y.2 := ⟨rfl, rfl⟩

/-- Both halves of a 256-bit sub are the accepted packed sub. -/
theorem ymmSub_halb (b : Breite) (x y : Ymm) :
    (ymmSub b x y).1 = vecSub b x.1 y.1 ∧
      (ymmSub b x y).2 = vecSub b x.2 y.2 := ⟨rfl, rfl⟩

/-- Both halves of a 256-bit and are the accepted packed and. -/
theorem ymmAnd_halb (b : Breite) (x y : Ymm) :
    (ymmAnd b x y).1 = vecAnd b x.1 y.1 ∧
      (ymmAnd b x y).2 = vecAnd b x.2 y.2 := ⟨rfl, rfl⟩

/-- Both halves of a 256-bit or are the accepted packed or. -/
theorem ymmOr_halb (b : Breite) (x y : Ymm) :
    (ymmOr b x y).1 = vecOr b x.1 y.1 ∧
      (ymmOr b x y).2 = vecOr b x.2 y.2 := ⟨rfl, rfl⟩

/-- Both halves of a 256-bit xor are the accepted packed xor. -/
theorem ymmXor_halb (b : Breite) (x y : Ymm) :
    (ymmXor b x y).1 = vecXor b x.1 y.1 ∧
      (ymmXor b x y).2 = vecXor b x.2 y.2 := ⟨rfl, rfl⟩

/-- Both halves of a 256-bit compare are the half compare. -/
theorem ymmCmpeq_halb (b : Breite) (x y : Ymm) :
    (ymmCmpeq b x y).1 = vecCmpeq b x.1 y.1 ∧
      (ymmCmpeq b x y).2 = vecCmpeq b x.2 y.2 := ⟨rfl, rfl⟩

/-! ## 3. Immediate shifts, per 128-bit half.

  Silicon facts (Intel SDM Vol. 2B, VPSLLW/D/Q, VPSRLW/D/Q, VPSRAW/D
  immediate forms): the count is an imm8; a count at or past the element
  width zeroes every lane for the LOGICAL shifts, while the ARITHMETIC
  shift fills every lane with its sign bit. Each 128-bit lane shifts
  independently. No VPSLLB/VPSRLB encoding exists (kept total at bound 7
  and documented, never claimed as an instruction); no VPSRAQ encoding
  exists in AVX2 (arithmetic is W/D only, stated in CUTS). -/

/-- Logical shift left of one 128-bit half by an immediate count:
    zero past the width, modular lane shift below it. -/
def vecShlImm (b : Breite) (v : Vektor) (c : Nat) : Vektor :=
  if b.bits ≤ c then 0 else vecMk b (fun i => laneNat b v i * 2 ^ c)

/-- Logical shift right of one 128-bit half by an immediate count. -/
def vecShrImm (b : Breite) (v : Vektor) (c : Nat) : Vektor :=
  if b.bits ≤ c then 0 else vecMk b (fun i => laneNat b v i / 2 ^ c)

/-- Arithmetic shift right of one lane value (two's complement, shift
    toward negative infinity): positives shift down, negatives round
    away from zero within the width. -/
def sraLane (w x c : Nat) : Nat :=
  if x < 2 ^ (w - 1) then x / 2 ^ c
  else 2 ^ w - (2 ^ w - x + 2 ^ c - 1) / 2 ^ c

/-- Arithmetic shift right of one 128-bit half by an immediate count:
    past the width every lane becomes its sign fill (0 or all-ones). -/
def vecSraImm (b : Breite) (v : Vektor) (c : Nat) : Vektor :=
  if b.bits ≤ c then
    vecMk b (fun i => if laneNat b v i < 2 ^ (b.bits - 1) then 0 else 2 ^ b.bits - 1)
  else vecMk b (fun i => sraLane b.bits (laneNat b v i) c)

/-- VPSLLW/D/Q over 256 bits (VPSLLB has no encoding; bound 7 kept
    total and never claimed as an instruction). -/
def ymmSll (b : Breite) (x : Ymm) (c : Nat) : Ymm :=
  (vecShlImm b x.1 c, vecShlImm b x.2 c)

/-- VPSRLW/D/Q over 256 bits. -/
def ymmSrl (b : Breite) (x : Ymm) (c : Nat) : Ymm :=
  (vecShrImm b x.1 c, vecShrImm b x.2 c)

/-- VPSRAW/D over 256 bits (no VPSRAQ encoding in AVX2). -/
def ymmSra (b : Breite) (x : Ymm) (c : Nat) : Ymm :=
  (vecSraImm b x.1 c, vecSraImm b x.2 c)

/-- A saturated logical shift left is the zero word. -/
theorem vecShlImm_satt (b : Breite) (v : Vektor) (c : Nat)
    (hc : b.bits ≤ c) : vecShlImm b v c = 0 := by
  unfold vecShlImm
  rw [if_pos hc]

/-- A saturated logical shift right is the zero word. -/
theorem vecShrImm_satt (b : Breite) (v : Vektor) (c : Nat)
    (hc : b.bits ≤ c) : vecShrImm b v c = 0 := by
  unfold vecShrImm
  rw [if_pos hc]

/-- An admitted logical shift left is the modular lane shift. -/
theorem laneNat_shlImm (b : Breite) (v : Vektor) (c i : Nat)
    (hc : ¬ b.bits ≤ c) (hi : i < laneCount b) :
    laneNat b (vecShlImm b v c) i =
      (laneNat b v i * 2 ^ c) % 2 ^ b.bits := by
  unfold vecShlImm
  rw [if_neg hc]
  exact laneGet_mk b _ i hi

/-- An admitted logical shift right is the lane quotient. -/
theorem laneNat_shrImm (b : Breite) (v : Vektor) (c i : Nat)
    (hc : ¬ b.bits ≤ c) (hi : i < laneCount b) :
    laneNat b (vecShrImm b v c) i =
      (laneNat b v i / 2 ^ c) % 2 ^ b.bits := by
  unfold vecShrImm
  rw [if_neg hc]
  exact laneGet_mk b _ i hi

/-- AGREEMENT: at 64-bit lanes the 256-bit shift halves ARE the accepted
    SSE2 saturating shifts (`vecShlQ`/`vecShrQ` saturate past 63, which
    is exactly the `.b64` bound). -/
theorem vecShlImm_b64 (v : Vektor) (c : Nat) :
    vecShlImm .b64 v c = vecShlQ v c := by
  have hb : Breite.bits .b64 = 64 := rfl
  unfold vecShlImm vecShlQ
  rw [hb]
  by_cases h : 64 ≤ c
  · have h2 : 63 < c := by omega
    simp [h, h2]
  · have h2 : ¬ 63 < c := by omega
    simp [h, h2]

/-- AGREEMENT: the 64-bit logical shift right halves agree. -/
theorem vecShrImm_b64 (v : Vektor) (c : Nat) :
    vecShrImm .b64 v c = vecShrQ v c := by
  have hb : Breite.bits .b64 = 64 := rfl
  unfold vecShrImm vecShrQ
  rw [hb]
  by_cases h : 64 ≤ c
  · have h2 : 63 < c := by omega
    simp [h, h2]
  · have h2 : ¬ 63 < c := by omega
    simp [h, h2]

/-! ## 4. Lane separation: no carry crosses lanes or halves.

  Each lane of the result depends only on the same-lane inputs (and the
  half it sits in); every other lane and the other half may vary freely.
  The 256-bit halves never interact: each half equation mentions only
  its own half. -/

/-- Lane separation for 256-bit add, low half. -/
theorem ymmAdd_allein_lo (b : Breite) (x x' y y' : Ymm) (i : Nat)
    (hx : laneNat b x.1 i = laneNat b x'.1 i)
    (hy : laneNat b y.1 i = laneNat b y'.1 i)
    (hi : i < laneCount b) :
    laneNat b (ymmAdd b x y).1 i =
      laneNat b (ymmAdd b x' y').1 i :=
  vecAdd_allein b x.1 x'.1 y.1 y'.1 i hx hy hi

/-- Lane separation for 256-bit add, high half. -/
theorem ymmAdd_allein_hi (b : Breite) (x x' y y' : Ymm) (i : Nat)
    (hx : laneNat b x.2 i = laneNat b x'.2 i)
    (hy : laneNat b y.2 i = laneNat b y'.2 i)
    (hi : i < laneCount b) :
    laneNat b (ymmAdd b x y).2 i =
      laneNat b (ymmAdd b x' y').2 i :=
  vecAdd_allein b x.2 x'.2 y.2 y'.2 i hx hy hi

/-- Lane separation for 256-bit sub, low half (no borrow crosses). -/
theorem ymmSub_allein_lo (b : Breite) (x x' y y' : Ymm) (i : Nat)
    (hx : laneNat b x.1 i = laneNat b x'.1 i)
    (hy : laneNat b y.1 i = laneNat b y'.1 i)
    (hi : i < laneCount b) :
    laneNat b (ymmSub b x y).1 i =
      laneNat b (ymmSub b x' y').1 i :=
  vecSub_allein b x.1 x'.1 y.1 y'.1 i hx hy hi

/-- Lane separation for 256-bit sub, high half. -/
theorem ymmSub_allein_hi (b : Breite) (x x' y y' : Ymm) (i : Nat)
    (hx : laneNat b x.2 i = laneNat b x'.2 i)
    (hy : laneNat b y.2 i = laneNat b y'.2 i)
    (hi : i < laneCount b) :
    laneNat b (ymmSub b x y).2 i =
      laneNat b (ymmSub b x' y').2 i :=
  vecSub_allein b x.2 x'.2 y.2 y'.2 i hx hy hi

/-- Each low-half add lane is the modular lane sum (hence same-lane
    inputs only). -/
theorem ymmAdd_lane_lo (b : Breite) (x y : Ymm) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (ymmAdd b x y).1 i =
      (laneNat b x.1 i + laneNat b y.1 i) % 2 ^ b.bits :=
  laneNat_add b x.1 y.1 i hi

/-- Each high-half add lane is the modular lane sum. -/
theorem ymmAdd_lane_hi (b : Breite) (x y : Ymm) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (ymmAdd b x y).2 i =
      (laneNat b x.2 i + laneNat b y.2 i) % 2 ^ b.bits :=
  laneNat_add b x.2 y.2 i hi

/-- Each low-half and lane is the lane conjunction. -/
theorem ymmAnd_lane_lo (b : Breite) (x y : Ymm) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (ymmAnd b x y).1 i =
      ((laneNat b x.1 i) &&& (laneNat b y.1 i)) % 2 ^ b.bits :=
  laneNat_and b x.1 y.1 i hi

/-- Each low-half or lane is the lane disjunction. -/
theorem ymmOr_lane_lo (b : Breite) (x y : Ymm) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (ymmOr b x y).1 i =
      ((laneNat b x.1 i) ||| (laneNat b y.1 i)) % 2 ^ b.bits :=
  laneNat_or b x.1 y.1 i hi

/-- Each low-half xor lane is the lane xor. -/
theorem ymmXor_lane_lo (b : Breite) (x y : Ymm) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (ymmXor b x y).1 i =
      ((laneNat b x.1 i) ^^^ (laneNat b y.1 i)) % 2 ^ b.bits :=
  laneNat_xor b x.1 y.1 i hi

/-- A compare lane is all-ones exactly on lane equality. -/
theorem laneNat_cmpeq (b : Breite) (x y : Vektor) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (vecCmpeq b x y) i =
      (if laneNat b x i == laneNat b y i then 2 ^ b.bits - 1 else 0) := by
  unfold vecCmpeq
  rw [laneGet_mk b _ i hi]
  by_cases h : laneNat b x i == laneNat b y i
  · rw [if_pos h]
    have hpos := laneMod_pos b
    have hlt : 2 ^ b.bits - 1 < 2 ^ b.bits := by omega
    rw [Nat.mod_eq_of_lt hlt]
  · rw [if_neg h, Nat.zero_mod]

/-- Comparing a word with itself yields all-ones in every lane. -/
theorem vecCmpeq_selbst (b : Breite) (x : Vektor) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (vecCmpeq b x x) i = 2 ^ b.bits - 1 := by
  rw [laneNat_cmpeq b x x i hi, if_pos (beq_self_eq_true _)]

/-! ## 5. Algebraic laws (only where true).

  Commutativity holds per lane for add/and/or/xor (never for sub,
  shifts or compare); identities: add-zero and and-allones. Each law is
  stated per lane, reusing the accepted `laneNat_*` equations, so no
  law can smuggle a cross-lane effect. -/

/-- 256-bit add commutes, low half. -/
theorem ymmAdd_comm_lo (b : Breite) (x y : Ymm) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (ymmAdd b x y).1 i = laneNat b (ymmAdd b y x).1 i := by
  rw [ymmAdd_lane_lo b x y i hi, ymmAdd_lane_lo b y x i hi]
  exact congrArg (· % 2 ^ b.bits) (Nat.add_comm _ _)

/-- 256-bit add commutes, high half. -/
theorem ymmAdd_comm_hi (b : Breite) (x y : Ymm) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (ymmAdd b x y).2 i = laneNat b (ymmAdd b y x).2 i := by
  rw [ymmAdd_lane_hi b x y i hi, ymmAdd_lane_hi b y x i hi]
  exact congrArg (· % 2 ^ b.bits) (Nat.add_comm _ _)

/-- 256-bit and commutes, low half. -/
theorem ymmAnd_comm_lo (b : Breite) (x y : Ymm) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (ymmAnd b x y).1 i = laneNat b (ymmAnd b y x).1 i := by
  rw [ymmAnd_lane_lo b x y i hi, ymmAnd_lane_lo b y x i hi]
  exact congrArg (· % 2 ^ b.bits) (Nat.and_comm _ _)

/-- 256-bit or commutes, low half. -/
theorem ymmOr_comm_lo (b : Breite) (x y : Ymm) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (ymmOr b x y).1 i = laneNat b (ymmOr b y x).1 i := by
  rw [ymmOr_lane_lo b x y i hi, ymmOr_lane_lo b y x i hi]
  exact congrArg (· % 2 ^ b.bits) (Nat.or_comm _ _)

/-- 256-bit xor commutes, low half. -/
theorem ymmXor_comm_lo (b : Breite) (x y : Ymm) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (ymmXor b x y).1 i = laneNat b (ymmXor b y x).1 i := by
  rw [ymmXor_lane_lo b x y i hi, ymmXor_lane_lo b y x i hi]
  exact congrArg (· % 2 ^ b.bits) (Nat.xor_comm _ _)

/-- Adding the zero word is the identity, low half. -/
theorem ymmAdd_zero_lo (b : Breite) (x : Ymm) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (ymmAdd b x (0, 0)).1 i = laneNat b x.1 i := by
  rw [ymmAdd_lane_lo b x (0, 0) i hi]
  have hz : laneNat b (0 : Vektor) i = 0 := by simp [laneNat]
  rw [hz, Nat.add_zero, Nat.mod_eq_of_lt (laneNat_lt b x.1 i)]

/-- The all-ones word: every lane is `2 ^ w - 1`. -/
def vecEins (b : Breite) : Vektor := vecMk b (fun _ => 2 ^ b.bits - 1)

/-- Every lane of the all-ones word reads back. -/
theorem laneNat_eins (b : Breite) (i : Nat) (hi : i < laneCount b) :
    laneNat b (vecEins b) i = 2 ^ b.bits - 1 := by
  unfold vecEins
  rw [laneGet_mk b _ i hi]
  have hpos := laneMod_pos b
  have hlt : 2 ^ b.bits - 1 < 2 ^ b.bits := by omega
  rw [Nat.mod_eq_of_lt hlt]

/-- AND with all-ones is the identity, low half. -/
theorem ymmAnd_eins_lo (b : Breite) (x : Ymm) (i : Nat)
    (hi : i < laneCount b) :
    laneNat b (ymmAnd b x (vecEins b, vecEins b)).1 i =
      laneNat b x.1 i := by
  rw [ymmAnd_lane_lo b x (vecEins b, vecEins b) i hi,
    laneNat_eins b i hi, mask_and_eq_mod,
    Nat.mod_mod, Nat.mod_eq_of_lt (laneNat_lt b x.1 i)]

/-! ## 6. Tier-3 admission: the named-CPU-profile gate.

  DESIGN §6 Tier 3: AVX2 VEX/YMM is the first OPTIONAL selected-CPU
  profile, enabled only by silicon AVX2 (which always carries SSE2),
  XCR0 XMM+YMM readiness, CR4.OSXSAVE and OS vector state; an absent
  form is a refused encoding, never a silent fallback. Setup and
  context-switch save/restore stay user/binding logic: these are
  checked inputs, never assumed-correct behaviour. -/

/-- AVX control freedom: legacy SSE freedom plus OSXSAVE enabled
    (without OSXSAVE every VEX form faults #UD). -/
def kontrollAvxFrei (k : KontrollBild) : Bool :=
  kontrollSseFrei k && k.cr4Osxsave

/-- AVX control freedom implies legacy SSE control freedom. -/
theorem kontrollAvxFrei_braucht_legacy (k : KontrollBild)
    (h : kontrollAvxFrei k = true) :
    kontrollSseLegacyFrei k = true := by
  cases e1 : !k.cr0Em <;> cases e2 : !k.cr0Ts <;>
    cases e3 : k.cr4Osfxsr <;> cases e4 : k.cr4Osxsave <;>
    simp_all [kontrollAvxFrei, kontrollSseFrei, kontrollSseLegacyFrei]

/-- Tier-3 AVX2 readiness: silicon AVX2 and SSE2, XCR0 XMM+YMM,
    AVX control freedom, OS vector state. This is the PROFILE-level
    gate over the accepted `CpuMerkmal`/`Xcr0Bild`/`KontrollBild`
    vocabulary. Its namesake `CpuFeatureHardwareForms.avx2Bereit` is
    the LEAF-level version over raw CPUID leaves and XCR0 bits; no
    mapping between the two levels is constructed here (that bridge
    belongs to the State/integration work, see CUTS). -/
def avx2TierBereit (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (b : BereitProfil) : Bool :=
  cpu.hatAvx && cpu.hatSse2 && xcr0AvxBereit x && kontrollAvxFrei k && b.osXmm

/-- Full Tier-3 admission: the finite packed-integer profile AND AVX2
    readiness. Either side alone admits nothing. -/
def avx2TierZugelassen (hw : HwProfil) (b : BereitProfil) (cpu : CpuMerkmal)
    (x : Xcr0Bild) (k : KontrollBild) : Bool :=
  merkmalZugelassen hw b .paketInt128 && avx2TierBereit cpu x k b

/-- No AVX2 silicon bit, no admission. -/
theorem avx2Tier_ohne_avx (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (hcpu : cpu.hatAvx = false) :
    avx2TierZugelassen hw b cpu x k = false := by
  unfold avx2TierZugelassen avx2TierBereit
  rw [hcpu]
  simp

/-- No SSE2 silicon bit, no admission (AVX2 silicon always carries it). -/
theorem avx2Tier_ohne_sse2 (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (hcpu : cpu.hatSse2 = false) :
    avx2TierZugelassen hw b cpu x k = false := by
  unfold avx2TierZugelassen avx2TierBereit
  rw [hcpu]
  simp

/-- No XCR0 AVX readiness, no admission. -/
theorem avx2Tier_ohne_xcr0 (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (hx : xcr0AvxBereit x = false) :
    avx2TierZugelassen hw b cpu x k = false := by
  unfold avx2TierZugelassen avx2TierBereit
  rw [hx]
  simp

/-- No AVX control freedom, no admission. -/
theorem avx2Tier_ohne_kontrolle (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (hk : kontrollAvxFrei k = false) :
    avx2TierZugelassen hw b cpu x k = false := by
  unfold avx2TierZugelassen avx2TierBereit
  rw [hk]
  simp

/-- No OS vector state, no admission. -/
theorem avx2Tier_ohne_osxmm (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (hos : b.osXmm = false) :
    avx2TierZugelassen hw b cpu x k = false := by
  unfold avx2TierZugelassen avx2TierBereit
  rw [hos]
  simp

/-- No finite-profile side, no admission. -/
theorem avx2Tier_ohne_merkmal (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (hm : merkmalZugelassen hw b .paketInt128 = false) :
    avx2TierZugelassen hw b cpu x k = false := by
  unfold avx2TierZugelassen
  rw [hm]
  simp

/-- SAFE REFINEMENT: Tier-3 admission implies the legacy SSE2 gate, so
    every admitted 128-bit half-word carries the accepted SSE2 meaning.
    The Tier-3 gate stays strictly stronger (see `avx2Tier_strikt`). -/
theorem avx2Tier_verfeinert_legacy (hw : HwProfil) (b : BereitProfil)
    (cpu : CpuMerkmal) (x : Xcr0Bild) (k : KontrollBild)
    (h : avx2TierZugelassen hw b cpu x k = true) :
    vektorLegacyZugelassen hw b cpu k = true := by
  cases hm : merkmalZugelassen hw b .paketInt128 <;>
    cases ha : cpu.hatAvx <;> cases hs : cpu.hatSse2 <;>
    cases hx : xcr0AvxBereit x <;> cases hk : kontrollAvxFrei k <;>
    cases ho : b.osXmm <;>
    simp_all [avx2TierZugelassen, avx2TierBereit, vektorLegacyZugelassen,
      hwSse2LegacyBereit, kontrollAvxFrei, kontrollSseFrei,
      kontrollSseLegacyFrei]

/-- Named AVX2 CPU profile: silicon AVX2 and SSE2 present. -/
def avx2Cpu : CpuMerkmal := ⟨true, true⟩

/-- Named AVX2 XCR0: x87, SSE and AVX state enabled. -/
def avx2Xcr0 : Xcr0Bild := ⟨true, true, true⟩

/-- ADMITTED: the named profile with OS state admits Tier 3. -/
theorem avx2Tier_basis_zugelassen :
    avx2TierZugelassen basisHw vecZeugeBereit avx2Cpu avx2Xcr0
        basisKontrolle = true := by
  decide

/-- STRICTNESS: legacy SSE2 admits where Tier 3 refuses (the baseline
    CPU has no AVX2 bit): the default profile refuses VEX by
    construction, exactly as Tier 3 demands. -/
theorem avx2Tier_strikt :
    vektorLegacyZugelassen basisHw vecZeugeBereit basisCpu
          basisKontrolle = true ∧
      avx2TierZugelassen basisHw vecZeugeBereit basisCpu basisXcr0
          basisKontrolle = false := by
  exact ⟨by decide, by decide⟩

/-! ## 7. Witnesses with carry/overflow lanes (all `decide`).

  Every witness pins concrete 256-bit values where one lane
  carries/overflows while another lane and the other half stay
  independent. -/

/-- OVERFLOW: byte lane 0 wraps (`0xFF + 1 = 0`) in the low half while
    lane 1 adds independently and the high half is untouched by the
    low-half carry. -/
theorem ymmAdd_spur_ueberlauf :
    laneNat .b8 (ymmAdd .b8
      (vecMk .b8 (fun i => if i = 0 then 255 else if i = 1 then 5 else 0),
       vecMk .b8 (fun _ => 7))
      (vecMk .b8 (fun i => if i = 0 then 1 else if i = 1 then 7 else 0),
       vecMk .b8 (fun _ => 9))).1 0 = 0 ∧
    laneNat .b8 (ymmAdd .b8
      (vecMk .b8 (fun i => if i = 0 then 255 else if i = 1 then 5 else 0),
       vecMk .b8 (fun _ => 7))
      (vecMk .b8 (fun i => if i = 0 then 1 else if i = 1 then 7 else 0),
       vecMk .b8 (fun _ => 9))).1 1 = 12 ∧
    laneNat .b8 (ymmAdd .b8
      (vecMk .b8 (fun i => if i = 0 then 255 else if i = 1 then 5 else 0),
       vecMk .b8 (fun _ => 7))
      (vecMk .b8 (fun i => if i = 0 then 1 else if i = 1 then 7 else 0),
       vecMk .b8 (fun _ => 9))).2 0 = 16 ∧
    laneNat .b8 (ymmAdd .b8
      (vecMk .b8 (fun i => if i = 0 then 255 else if i = 1 then 5 else 0),
       vecMk .b8 (fun _ => 7))
      (vecMk .b8 (fun i => if i = 0 then 1 else if i = 1 then 7 else 0),
       vecMk .b8 (fun _ => 9))).2 3 = 16 := by
  decide

/-- QWORD OVERFLOW across both halves: each 64-bit lane wraps or adds
    on its own (`2^64 - 1 + 1 = 0` low, `10 + 5 = 15` high-low). -/
theorem ymmAdd_spur_qword_ueberlauf :
    laneNat .b64 (ymmAdd .b64
      (vecMk .b64 (fun i => if i = 0 then 18446744073709551615 else 3),
       vecMk .b64 (fun i => if i = 0 then 10 else 20))
      (vecMk .b64 (fun i => if i = 0 then 1 else 4),
       vecMk .b64 (fun i => if i = 0 then 5 else 6))).1 0 = 0 ∧
    laneNat .b64 (ymmAdd .b64
      (vecMk .b64 (fun i => if i = 0 then 18446744073709551615 else 3),
       vecMk .b64 (fun i => if i = 0 then 10 else 20))
      (vecMk .b64 (fun i => if i = 0 then 1 else 4),
       vecMk .b64 (fun i => if i = 0 then 5 else 6))).1 1 = 7 ∧
    laneNat .b64 (ymmAdd .b64
      (vecMk .b64 (fun i => if i = 0 then 18446744073709551615 else 3),
       vecMk .b64 (fun i => if i = 0 then 10 else 20))
      (vecMk .b64 (fun i => if i = 0 then 1 else 4),
       vecMk .b64 (fun i => if i = 0 then 5 else 6))).2 0 = 15 ∧
    laneNat .b64 (ymmAdd .b64
      (vecMk .b64 (fun i => if i = 0 then 18446744073709551615 else 3),
       vecMk .b64 (fun i => if i = 0 then 10 else 20))
      (vecMk .b64 (fun i => if i = 0 then 1 else 4),
       vecMk .b64 (fun i => if i = 0 then 5 else 6))).2 1 = 26 := by
  decide

/-- BORROW: lane 0 borrows and wraps (`0 - 1 = 0xFF`) while lane 1 and
    the high half subtract independently. -/
theorem ymmSub_spur_borg :
    laneNat .b8 (ymmSub .b8
      (vecMk .b8 (fun i => if i = 0 then 0 else if i = 1 then 5 else 0),
       vecMk .b8 (fun _ => 100))
      (vecMk .b8 (fun i => if i = 0 then 1 else if i = 1 then 2 else 0),
       vecMk .b8 (fun _ => 30))).1 0 = 255 ∧
    laneNat .b8 (ymmSub .b8
      (vecMk .b8 (fun i => if i = 0 then 0 else if i = 1 then 5 else 0),
       vecMk .b8 (fun _ => 100))
      (vecMk .b8 (fun i => if i = 0 then 1 else if i = 1 then 2 else 0),
       vecMk .b8 (fun _ => 30))).1 1 = 3 ∧
    laneNat .b8 (ymmSub .b8
      (vecMk .b8 (fun i => if i = 0 then 0 else if i = 1 then 5 else 0),
       vecMk .b8 (fun _ => 100))
      (vecMk .b8 (fun i => if i = 0 then 1 else if i = 1 then 2 else 0),
       vecMk .b8 (fun _ => 30))).2 0 = 70 := by
  decide

/-- SATURATE, NOT MASK at 256 bits: count 16 zeroes a nonzero word
    half, where masked semantics would leave it unchanged. -/
theorem ymmSll_spur_saettigung :
    ymmSll .b16 (BitVec.ofNat 128 0xFF, BitVec.ofNat 128 0xFF00) 16 =
      (0, 0) := by
  decide

/-- Boundary shift: one doubles every 64-bit lane in both halves
    (low half `(1, 1) -> (2, 2)`, high half `(4, 3) -> (8, 6)`). -/
theorem ymmSll_spur_eins :
    laneNat .b64 (ymmSll .b64
      (BitVec.ofNat 128 0x00000000000000010000000000000001,
       BitVec.ofNat 128 0x00000000000000030000000000000004) 1).1 0 = 2 ∧
    laneNat .b64 (ymmSll .b64
      (BitVec.ofNat 128 0x00000000000000010000000000000001,
       BitVec.ofNat 128 0x00000000000000030000000000000004) 1).1 1 = 2 ∧
    laneNat .b64 (ymmSll .b64
      (BitVec.ofNat 128 0x00000000000000010000000000000001,
       BitVec.ofNat 128 0x00000000000000030000000000000004) 1).2 0 = 8 ∧
    laneNat .b64 (ymmSll .b64
      (BitVec.ofNat 128 0x00000000000000010000000000000001,
       BitVec.ofNat 128 0x00000000000000030000000000000004) 1).2 1 = 6 := by
  decide

/-- SIGN FILL: a past-width arithmetic shift makes the negative lane
    all-ones and the positive lane zero (SDM clamp to 16/32). -/
theorem ymmSra_spur_vorzeichen :
    laneNat .b16 (ymmSra .b16
      (vecMk .b16 (fun i => if i = 0 then 0x8000 else 0x0001),
       vecMk .b16 (fun _ => 0)) 20).1 0 = 0xFFFF ∧
    laneNat .b16 (ymmSra .b16
      (vecMk .b16 (fun i => if i = 0 then 0x8000 else 0x0001),
       vecMk .b16 (fun _ => 0)) 20).1 1 = 0 := by
  decide

/-- ADMITTED arithmetic shift: `0xFF00 (-256) >> 4 = 0xFFF0 (-16)`. -/
theorem ymmSra_spur_zugelassen :
    laneNat .b16 (ymmSra .b16
      (vecMk .b16 (fun _ => 0xFF00),
       vecMk .b16 (fun _ => 0)) 4).1 0 = 0xFFF0 := by
  decide

/-- COMPARE: differing lanes give zero, equal lanes all-ones, in both
    halves. -/
theorem ymmCmpeq_spur :
    laneNat .b8 (ymmCmpeq .b8
      (vecMk .b8 (fun i => if i = 0 then 170 else 240),
       vecMk .b8 (fun _ => 1))
      (vecMk .b8 (fun i => if i = 0 then 85 else 240),
       vecMk .b8 (fun _ => 1))).1 0 = 0 ∧
    laneNat .b8 (ymmCmpeq .b8
      (vecMk .b8 (fun i => if i = 0 then 170 else 240),
       vecMk .b8 (fun _ => 1))
      (vecMk .b8 (fun i => if i = 0 then 85 else 240),
       vecMk .b8 (fun _ => 1))).1 1 = 255 ∧
    laneNat .b8 (ymmCmpeq .b8
      (vecMk .b8 (fun i => if i = 0 then 170 else 240),
       vecMk .b8 (fun _ => 1))
      (vecMk .b8 (fun i => if i = 0 then 85 else 240),
       vecMk .b8 (fun _ => 1))).2 0 = 255 := by
  decide

/-- ANDN: `(NOT 0xAA) AND 0xFF = 0x55` in the lane. -/
theorem ymmAndn_spur :
    laneNat .b8 (ymmAndn .b8
      (vecMk .b8 (fun _ => 0xAA), vecMk .b8 (fun _ => 0))
      (vecMk .b8 (fun _ => 0xFF), vecMk .b8 (fun _ => 0))).1 0 = 0x55 := by
  decide

/- CUTS: what is not proved here.

   - Pure semantics only: no VEX decoder/encoder (sibling Vex piece),
     no YMM register file, no VZEROUPPER/VZEROALL, no 128-bit
     zeroing/p preservation rule (SIBLING State piece), no 256-bit
     loads/stores and no TSO/memory connection (sibling Mem piece).
     In particular there is NO `HwAdapter`, no `HwSchritt` embedding
     and no `HwWf` preservation in this file: the generic MECHANISM
     paragraph of the lane task is not discharged here, deliberately,
     because the lane is registered as one of four INDEPENDENT pieces
     whose FILE SCOPE is pure semantic functions. A reviewer that
     wants the adapter must assign it to the Mem/State integration,
     not to this file.
   - No per-lane equation theorem for `vecSraImm`/`sraLane` in the
     admitted range: saturation shape and admitted values are pinned
     by `ymmSra_spur_vorzeichen`/`ymmSra_spur_zugelassen` only. A
     general `SignExtend` correspondence lemma is open.
   - `vecShlImm`/`vecShrImm`/`vecSraImm` at `.b8` and `vecSraImm` at
     `.b64` are mathematically total but have NO AVX2 encoding
     (no byte imm-shift exists; VPSRAQ is EVEX-only per the cited
     lines); they are never claimed as instructions.
   - The Tier-3 gate is a data predicate over checked inputs, not a
     CPUID/XCR0 probe: measured CPUID bits, OS save/restore and
     context-switch code stay user/binding logic. Profile selection
     (`waehle`), image mapping, decode coverage, TSO/GX refinement,
     source correspondence, budget transfer and timing stay open.
     No bridge between the profile-level `avx2TierBereit` and the
     leaf-level `CpuFeatureHardwareForms.avx2Bereit` is constructed.
   - Silicon correspondence beyond the cited extract lines is OPEN:
     the theorems are self-consistency of the stated functions, not
     hardware proofs. No claim about VEX prefix bytes, fault classes
     (#UD/#GP/#NM), exception types or transition penalties is made
     here.
-/

#print axioms ymmAdd_halb
#print axioms ymmSub_halb
#print axioms ymmAnd_halb
#print axioms ymmOr_halb
#print axioms ymmXor_halb
#print axioms ymmCmpeq_halb
#print axioms vecShlImm_satt
#print axioms vecShrImm_satt
#print axioms laneNat_shlImm
#print axioms laneNat_shrImm
#print axioms vecShlImm_b64
#print axioms vecShrImm_b64
#print axioms ymmAdd_allein_lo
#print axioms ymmAdd_allein_hi
#print axioms ymmSub_allein_lo
#print axioms ymmSub_allein_hi
#print axioms ymmAdd_lane_lo
#print axioms ymmAdd_lane_hi
#print axioms ymmAnd_lane_lo
#print axioms ymmOr_lane_lo
#print axioms ymmXor_lane_lo
#print axioms laneNat_cmpeq
#print axioms vecCmpeq_selbst
#print axioms ymmAdd_comm_lo
#print axioms ymmAdd_comm_hi
#print axioms ymmAnd_comm_lo
#print axioms ymmOr_comm_lo
#print axioms ymmXor_comm_lo
#print axioms ymmAdd_zero_lo
#print axioms laneNat_eins
#print axioms ymmAnd_eins_lo
#print axioms kontrollAvxFrei_braucht_legacy
#print axioms avx2Tier_ohne_avx
#print axioms avx2Tier_ohne_sse2
#print axioms avx2Tier_ohne_xcr0
#print axioms avx2Tier_ohne_kontrolle
#print axioms avx2Tier_ohne_osxmm
#print axioms avx2Tier_ohne_merkmal
#print axioms avx2Tier_verfeinert_legacy
#print axioms avx2Tier_basis_zugelassen
#print axioms avx2Tier_strikt
#print axioms ymmAdd_spur_ueberlauf
#print axioms ymmAdd_spur_qword_ueberlauf
#print axioms ymmSub_spur_borg
#print axioms ymmSll_spur_saettigung
#print axioms ymmSll_spur_eins
#print axioms ymmSra_spur_vorzeichen
#print axioms ymmSra_spur_zugelassen
#print axioms ymmCmpeq_spur
#print axioms ymmAndn_spur

end Gabbro.Grammatik.X86
