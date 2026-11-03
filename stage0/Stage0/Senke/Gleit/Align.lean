/- Operand alignment for software binary64 addition (`Block.float`, `op = .add`).

    On the finite path (dispatcher silent) both operands are exact dyadics
    (`wertExakt`): `softNum` is the signed numerator uniformly over null,
    subnormal and normal (`softWertExakt_*` prove it against the kernel, one
    class at a time), `softExp` the true binary exponent, `softGap` how far the
    smaller operand shifts, and `softShiftA` which side that is. `softJamQuot`
    and `softJamSticky` are the Nat shadows of the existing word jam
    (`floatShiftJamWord`, reused as IR below); `softJam_exact` keeps the
    discarded remainder exact. `softAlignAdd_exact` replays the shared kernel
    identity `floatAdd_align` in directional form. IR is directional too
    (`alignGapL`, `alignShiftL`, both `WordCode`): the caller orders the
    operands, so no branch reasoning enters this piece; the `wennL` selection
    over `softShiftA` lands with the composition. -/
module
public import Grammatik.Bausteine.Gleitkomma.GleitkommaBits
public import Stage0.Senke.Ausdruck.Aggregat.Hilfena
public import Stage0.Senke.Ausdruck.Gleit.Komposition
public import Stage0.Senke.Ausdruck.Gleit.Schieben
public import Stage0.Senke.Ausdruck.Arithmetik.AddSub
public import Stage0.Senke.Gleit.Add
public import Stage0.Senke.Gleit.Unpack
@[expose] public section


namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik
open Gleitkomma
open Runner.IR Runner.Mem
variable [Kern] {D : Deklaration} {L : Lay D}

/-- Significand magnitude: hidden one for normals, bare fraction otherwise
    (zero and subnormals share the zero-exponent form). -/
def softSig (bexp frac : Nat) : Nat := if bexp = 0 then frac else 2 ^ 52 + frac

/-- Signed exact numerator: sign times significand, uniform over null,
    subnormal and normal (null contributes zero whatever its sign). -/
def softNum (s : Bool) (bexp frac : Nat) : Int :=
  (if s then (-1 : Int) else 1) * (((if bexp = 0 then 0 else 2 ^ 52 : Nat)) + (frac : Int))

/-- True binary exponent of the exact value: null is zero, subnormals sit at
    the format floor, normals at biased minus bias and significand width. -/
def softExp (bexp frac : Nat) : Int :=
  if bexp = 0 then (if frac = 0 then 0 else -1074) else (bexp : Int) - 1075

/-- Alignment gap: how far the smaller operand shifts, in the exact form
    `floatAdd_align` scales by (no negative gaps). -/
def softGap (ea eb : Int) : Nat :=
  if ea ≤ eb then (eb - ea).toNat else (ea - eb).toNat

/-- Shift the smaller operand: true while `a` aligns down to `b`. Ties keep
    `a` (shifting `b` by zero is the same pair); the composer takes the common
    exponent as the maximum. -/
def softShiftA (ea eb : Int) : Bool := decide (ea ≤ eb)

/-- Jammed quotient shadow: the smaller significand divided down by the gap. -/
def softJamQuot (s gap : Nat) : Nat := s / 2 ^ gap

/-- Sticky shadow: whether the gap division discarded anything nonzero. -/
def softJamSticky (s gap : Nat) : Bool := decide (s % 2 ^ gap ≠ 0)

/-- Zero decodes to the zero class. -/
theorem softKlasse_null (s : Bool) :
    klasse f64 ⟨s, 0, 0⟩ = Klasse.null := by
  show (if (0 : Nat) = f64.bexpMax then
      (if (0 : Nat) = 0 then Klasse.unendlich else Klasse.nan)
    else if (0 : Nat) = 0 then
      (if (0 : Nat) = 0 then Klasse.null else Klasse.subnormal)
    else Klasse.normal) = Klasse.null
  decide

/-- Zero exponent with nonzero fraction decodes to subnormal. -/
theorem softKlasse_subnormal (s : Bool) (f : Nat) (hf : f ≠ 0) :
    klasse f64 ⟨s, 0, f⟩ = Klasse.subnormal := by
  have hbmax : f64.bexpMax = 2047 := rfl
  show (if (0 : Nat) = f64.bexpMax then
      (if f = 0 then Klasse.unendlich else Klasse.nan)
    else if (0 : Nat) = 0 then
      (if f = 0 then Klasse.null else Klasse.subnormal)
    else Klasse.normal) = Klasse.subnormal
  rw [hbmax]
  simp [hf]

/-- Nonzero, non-maximal exponent decodes to normal. -/
theorem softKlasse_normal (s : Bool) (e f : Nat) (he0 : e ≠ 0) (heM : e ≠ 2047) :
    klasse f64 ⟨s, e, f⟩ = Klasse.normal := by
  have hbmax : f64.bexpMax = 2047 := rfl
  show (if e = f64.bexpMax then
      (if f = 0 then Klasse.unendlich else Klasse.nan)
    else if e = 0 then
      (if f = 0 then Klasse.null else Klasse.subnormal)
    else Klasse.normal) = Klasse.normal
  rw [hbmax]
  simp [he0, heM]

/-- The kernel exact value of zero (verbatim kernel form). -/
theorem softWertExakt_null (s : Bool) :
    wertExakt f64 ⟨s, 0, 0⟩ = some ⟨0, 0⟩ := by
  unfold wertExakt
  rw [softKlasse_null s]

/-- The kernel exact value of a subnormal (verbatim kernel form). -/
theorem softWertExakt_subnormal (s : Bool) (f : Nat) (hf : f ≠ 0) :
    wertExakt f64 ⟨s, 0, f⟩ =
      some ⟨(if s then (-1 : Int) else 1) * (f : Int),
        f64.emin - ((f64.p : Int) - 1)⟩ := by
  have hsg : (⟨s, 0, f⟩ : GBits f64).sign = s := rfl
  have hfr : (⟨s, 0, f⟩ : GBits f64).frac = f := rfl
  unfold wertExakt
  rw [hsg, hfr, softKlasse_subnormal s f hf]

/-- The kernel exact value of a normal (verbatim kernel form). -/
theorem softWertExakt_normal (s : Bool) (e f : Nat) (he0 : e ≠ 0) (heM : e ≠ 2047) :
    wertExakt f64 ⟨s, e, f⟩ =
      some ⟨(if s then (-1 : Int) else 1) * ((2 ^ (f64.p - 1) : Nat) + (f : Int)),
        (e : Int) - (f64.bias : Int) - ((f64.p : Int) - 1)⟩ := by
  have hsg : (⟨s, e, f⟩ : GBits f64).sign = s := rfl
  have hbe : (⟨s, e, f⟩ : GBits f64).bexp = e := rfl
  have hfr : (⟨s, e, f⟩ : GBits f64).frac = f := rfl
  unfold wertExakt
  rw [hsg, hbe, hfr, softKlasse_normal s e f he0 heM]

/-- The signed numerator is uniform over all finite classes: null, subnormal
    and normal all carry `softNum`. -/
theorem softNum_model (s : Bool) (e f : Nat) (heM : e ≠ 2047) :
    (wertExakt f64 ⟨s, e, f⟩).map Exakt.zaehler = some (softNum s e f) := by
  have hp : f64.p = 53 := rfl
  by_cases he0 : e = 0
  · subst he0
    by_cases hf0 : f = 0
    · subst hf0
      rw [softWertExakt_null s]
      show some (0 : Int) = some (softNum s 0 0)
      simp [softNum]
    · rw [softWertExakt_subnormal s f hf0]
      show some ((if s then (-1 : Int) else 1) * (f : Int)) = some (softNum s 0 f)
      simp [softNum]
  · rw [softWertExakt_normal s e f he0 heM]
    show some ((if s then (-1 : Int) else 1) * ((2 ^ (f64.p - 1) : Nat) + (f : Int))) =
      some (softNum s e f)
    simp [softNum, he0, hp]

/-- The true exponent is uniform over all finite classes: null sits at zero,
    subnormals at the floor, normals at biased minus 1075. -/
theorem softExp_model (s : Bool) (e f : Nat) (heM : e ≠ 2047) :
    (wertExakt f64 ⟨s, e, f⟩).map Exakt.zweierExp = some (softExp e f) := by
  have hp : f64.p = 53 := rfl
  have hbias : f64.bias = 1023 := rfl
  have hemin : f64.emin = 1 - 1023 := rfl
  by_cases he0 : e = 0
  · subst he0
    by_cases hf0 : f = 0
    · subst hf0
      rw [softWertExakt_null s]
      show some (0 : Int) = some (softExp 0 0)
      simp [softExp]
    · rw [softWertExakt_subnormal s f hf0]
      show some (f64.emin - ((f64.p : Int) - 1)) = some (softExp 0 f)
      simp [softExp, hf0, hemin, hp]
  · rw [softWertExakt_normal s e f he0 heM]
    show some (((e : Int)) - (f64.bias : Int) - ((f64.p : Int) - 1)) = some (softExp e f)
    rw [hbias, hp]
    unfold softExp
    rw [if_neg he0]
    congr 1
    omega

/-- The side decision replays the exponent order, nothing more. -/
theorem softShiftA_model (u v : Exakt) :
    softShiftA u.zweierExp v.zweierExp = decide (u.zweierExp ≤ v.zweierExp) := rfl

/-- Directional exact alignment: when `u` sits at or below `v`, the sum keeps
    `u`'s numerator and scales `v`'s by the gap. Replays `floatAdd_align`. -/
theorem softAlignAdd_exact (u v : Exakt) (h : u.zweierExp ≤ v.zweierExp) :
    exaktAdd u v =
      ⟨u.zaehler + v.zaehler * (2 ^ softGap u.zweierExp v.zweierExp : Nat),
        u.zweierExp⟩ := by
  rw [floatAdd_align]
  unfold softGap
  simp only [if_pos h]

/-- A decoded word's numerator is its aligned numerator, on every finite
    input (the dispatcher has already removed NaN and infinity). -/
theorem softAlign_decode (a : UInt64) (heM : softBexp a ≠ 2047) :
    (wertExakt f64 (u64ToG a)).map Exakt.zaehler =
      some (softNum (softSign a) (softBexp a) (softFrac a)) := by
  rw [softUnpack_model a]
  exact softNum_model (softSign a) (softBexp a) (softFrac a) heM

/-- A decoded word's exponent is its alignment exponent, on every finite
    input. -/
theorem softAlignExp_decode (a : UInt64) (heM : softBexp a ≠ 2047) :
    (wertExakt f64 (u64ToG a)).map Exakt.zweierExp =
      some (softExp (softBexp a) (softFrac a)) := by
  rw [softUnpack_model a]
  exact softExp_model (softSign a) (softBexp a) (softFrac a) heM

/-- Quotient plus remainder is the unshifted significand: nothing is lost
    before the sticky bit records it. -/
theorem softJam_exact (s gap : Nat) :
    s % 2 ^ gap + softJamQuot s gap * 2 ^ gap = s := by
  have h := Nat.mod_add_div s (2 ^ gap)
  rw [Nat.mul_comm (2 ^ gap)] at h
  unfold softJamQuot
  omega

/-- Directional gap word `eb - ea` (opcode 4): the caller orders the operands,
    so the subtraction never wraps. -/
def alignGapL (d : Nat) (ea eb : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  wordL 4 d (eb d) (ea (d + 1))

/-- Directional jam: the smaller significand shifted right by the gap with
    sticky bit, reusing `floatShiftJamL` (opcodes 12/11/14/4/9/5). -/
def alignShiftL (d : Nat) (s g : Nat → Option (List II × Nat)) :
    Option (List II × Nat) :=
  floatShiftJamL d s g

/-- Compositional IR simulation for the directional gap. -/
theorem alignGapL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {ea eb : Nat → Option (List II × Nat)} {eav ebv : Runner.W}
    (hea : WordCode (L := L) ρ W ea eav) (heb : WordCode (L := L) ρ W eb ebv) :
    WordCode (L := L) ρ W (fun d => alignGapL d ea eb) (ebv - eav) := by
  have result : WordCode (L := L) ρ W _ _ := WordCode.bin heb hea
    (g := fun x y => some (x - y)) rfl rfl (by decide : 4 < 256)
  intro fp K d c top h hK m pc hp
  exact result (fp := fp) (K := K) (d := d) (c := c) (top := top) h hK m pc hp

/-- Compositional IR simulation for the directional jam. -/
theorem alignShiftL_ok {Γ : Ctx} {ρ : Env D Γ} {W : Runner.Mem → Prop}
    {s g : Nat → Option (List II × Nat)} {sv gv : Runner.W}
    (hs : WordCode (L := L) ρ W s sv) (hg : WordCode (L := L) ρ W g gv) :
    WordCode (L := L) ρ W (fun d => alignShiftL d s g) (floatShiftJamWord sv gv) :=
  floatShiftJamL_ok hs hg

/-- Joint fixtures: hidden-one insertion, signed numerators, true exponents,
    gap direction and jam quotient with stickiness. -/
theorem align_zeuge :
    softSig 0 0 = 0 ∧
    softSig 1023 0 = 4503599627370496 ∧
    softNum false 1023 0 = 4503599627370496 ∧
    softNum true 0 7 = -7 ∧
    softExp 0 0 = 0 ∧ softExp 0 7 = -1074 ∧ softExp 1023 0 = -52 ∧
    softGap (-52 : Int) (-53 : Int) = 1 ∧
    softShiftA (-53 : Int) (-52 : Int) = true ∧
    softJamQuot 13 1 = 6 ∧ softJamSticky 13 1 = true ∧
    softJamQuot 12 1 = 6 ∧ softJamSticky 12 1 = false := by
  decide +kernel

/-- The directional gap on closed inputs computes and emits. -/
theorem alignGapL_ok_zeuge {Γ : Ctx} (ρ : Env D Γ) (W : Runner.Mem → Prop) :
    WordCode (L := L) ρ W (fun d => alignGapL d
      (fun j => some ([ci 1 j 1022 0], j + 1))
      (fun j => some ([ci 1 j 1023 0], j + 1))) 1 ∧
    (alignGapL 8 (fun j => some ([ci 1 j 1022 0], j + 1))
      (fun j => some ([ci 1 j 1023 0], j + 1))).isSome = true := by
  constructor
  · intro fp K d c top h hK m pc hp
    have result : WordCode (L := L) ρ W _ _ := alignGapL_ok
      (WordCode.const 1022 (by decide)) (WordCode.const 1023 (by decide))
    have hx : BitVec.ofInt 64 1023 - BitVec.ofInt 64 1022 = 1 := by decide
    rw [hx] at result
    exact result h hK m pc hp
  · decide +kernel

#print axioms softKlasse_null
#print axioms softKlasse_subnormal
#print axioms softKlasse_normal
#print axioms softWertExakt_null
#print axioms softWertExakt_subnormal
#print axioms softWertExakt_normal
#print axioms softNum_model
#print axioms softExp_model
#print axioms softShiftA_model
#print axioms softAlignAdd_exact
#print axioms softAlign_decode
#print axioms softAlignExp_decode
#print axioms softJam_exact
#print axioms alignGapL_ok
#print axioms alignShiftL_ok
#print axioms align_zeuge
#print axioms alignGapL_ok_zeuge

end Gabbro.Stage0.Senke
