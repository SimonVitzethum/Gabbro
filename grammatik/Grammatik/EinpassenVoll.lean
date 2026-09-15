/-
  File:      Grammatik/EinpassenVoll.lean
  Subject:   EVERY VALUE IS AN ANSWER -- the decoding `einpassen` (Semantik.lean) accepts, for
             every type, exactly the values of that type (floats: the well-formed ones), so
             the answer class of an axiom or a register is empty only when its declared type
             is (round-5 finding G1, 2026-09-15).

  THE FINDING. Until 2026-09-15 `einpassen` answered `none` for EVERY raw word of a `tagged`
  sum (`.sum`), a float (`.fl`) and a function pointer (`.fnptr`). Every call of an axiom with
  such a result ended in `hardware (annahme a)`, every read of such a register in
  `hardware (register r)`, for EVERY oracle -- a stop the MODEL decided, filed as hardware.
  `KoerperGutS` does not constrain hardware outcomes, so probe A (`ensures false`) behind one
  such call met (b) and was certified. `AxVertragO` was vacuous for such axioms.

  THE DECODINGS (Semantik.lean, `einpassen`):
  * `.sum cs`  -- `summePasst`: the raw word packs the emitter's C value
                  `struct { marke; union last; }` mixed-radix, `roh = marke + |cs| * last`
                  (Euclidean `%`, `/`); a bare case carries `0`, a payload case a number in
                  its range. Inverse: `summeRoh`, `summePasst_voll`.
  * `.fl lo hi`-- `gleitWortPasst`: the word is the IEEE-754 binary64 bit pattern
                  (`0 <= roh < 2^64`, `Gleitkomma.ausBits`), held against the range like a
                  computed float (`gleitPasst`). Inverse on well-formed values: `zuBits`,
                  `gleitWortPasst_voll`; every decoded value is well-formed
                  (`gleitWortPasst_wf`).
  * `.fnptr m` -- `zeigerPasst`: the word is a code address, the loaded image
                  `Orakel.zeiger` names the function there, and its signature number is held
                  against `m`. Every function of signature `m` is the answer of some image
                  (`zeigerPasst_voll`).
  * `.never` and every other EMPTY type have no value, hence no answer: `AntwortLeer`.

  WHAT IS PROVED HERE.
  * `einpassen_voll` -- every value of every type (floats: well-formed) is the decoding of
                        some raw word under some image;
  * `einpassen_wertOk` -- every decoded value is such a value;
  * `antwortLeer_iff` -- the answer class of `τ` is empty EXACTLY when `τ` has no such value:
                        the model decides no stop beyond the declared type;
  * `antwortLeer_never`, `antwortLeer_grund0`, `antwortLeer_int_leer` -- the named empties;
    `antwortLeer_keinErg` -- an axiom without a result always answers.
-/
import Grammatik.Semantik

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Sums -/

/-- The payload of a case as a raw number (a bare case: `0`). -/
def nutzRoh : (c : Option (Int × Int)) → Nutzlast c → Int
  | Option.none, _ => 0
  | Option.some (_, _), z => z.n

theorem nutzPasst_nutzRoh : ∀ (c : Option (Int × Int)) (x : Nutzlast c),
    nutzPasst c (nutzRoh c x) = some x
  | Option.none, x => by
      show (if (0 : Int) = 0 then some () else Option.none) = some x
      rw [if_pos rfl]
      rfl
  | Option.some (lo, hi), z => by
      show (if h : lo ≤ (z : Zahl lo hi).n ∧ (z : Zahl lo hi).n ≤ hi then
        some ⟨(z : Zahl lo hi).n, h.1, h.2⟩ else Option.none) = some z
      rw [dif_pos ⟨(z : Zahl lo hi).lo_le, (z : Zahl lo hi).le_hi⟩]
      rfl

/-- **The raw word of a `tagged` value**: `marke + |cases| * last`. -/
def summeRoh (cs : List (Option (Int × Int))) (v : Σ i : Fin cs.length, Nutzlast (cs.get i)) :
    Int :=
  (v.1.val : Int) + fallZahl cs * nutzRoh (cs.get v.1) v.2

/-- `summePasst` through its two digits. -/
theorem summePasst_eq (cs : List (Option (Int × Int))) (n : Int) (i : Fin cs.length) (p : Int)
    (hi : n % fallZahl cs = (i.val : Int)) (hp : n / fallZahl cs = p) :
    summePasst cs n = (nutzPasst (cs.get i) p).map fun x => ⟨i, x⟩ := by
  have hk : 0 < cs.length := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
  unfold summePasst
  rw [dif_pos hk]
  dsimp only
  rw [hp]
  generalize hI : (⟨(n % fallZahl cs).toNat, fall_marke_lt cs n hk⟩ : Fin cs.length) = I
  have e : I = i := by
    rw [← hI]
    apply Fin.ext
    show (n % fallZahl cs).toNat = i.val
    rw [hi, Int.toNat_natCast]
  subst e
  rfl

/-- **Every `tagged` value is the decoding of its raw word.** -/
theorem summePasst_voll (cs : List (Option (Int × Int)))
    (v : Σ i : Fin cs.length, Nutzlast (cs.get i)) : summePasst cs (summeRoh cs v) = some v := by
  have hk : (0 : Int) < fallZahl cs := by
    have := v.1.2
    unfold fallZahl
    omega
  have hi0 : (0 : Int) ≤ (v.1.val : Int) := Int.natCast_nonneg _
  have hi1 : (v.1.val : Int) < fallZahl cs := by
    have := v.1.2
    unfold fallZahl
    omega
  have hmod : summeRoh cs v % fallZahl cs = (v.1.val : Int) := by
    unfold summeRoh
    rw [Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt hi0 hi1
  have hdiv : summeRoh cs v / fallZahl cs = nutzRoh (cs.get v.1) v.2 := by
    unfold summeRoh
    rw [Int.add_mul_ediv_left _ _ (Int.ne_of_gt hk), Int.ediv_eq_zero_of_lt hi0 hi1, Int.zero_add]
  rw [summePasst_eq cs _ v.1 _ hmod hdiv, nutzPasst_nutzRoh]
  rfl

/-! ## 2. Floats -/

/-- Every bit pattern reads back as a well-formed triple (exponent field exactly full). -/
theorem ausBits_wf (F : Gleitkomma.Format) (hF : F.dicht) (m : Nat) :
    Gleitkomma.wf F (Gleitkomma.ausBits F m) := by
  refine ⟨?_, ?_⟩
  · show (m / 2 ^ F.fracBits) % 2 ^ F.ebits ≤ F.bexpMax
    have := Nat.mod_lt (m / 2 ^ F.fracBits) (Nat.two_pow_pos F.ebits)
    unfold Gleitkomma.Format.dicht at hF
    omega
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem f64_wortGrenze :
    2 ^ (Gleitkomma.f64.ebits + Gleitkomma.f64.fracBits + 1) = 18446744073709551616 := by
  decide

/-- **Every well-formed float in range is the decoding of its bit pattern.** -/
theorem gleitWortPasst_voll (lo hi : Int × Int) (v : Gleit lo hi)
    (hw : Gleitkomma.wf Gleitkomma.f64 v.x) :
    gleitWortPasst lo hi (Gleitkomma.zuBits Gleitkomma.f64 v.x : Int) = some v := by
  have hlt := Gleitkomma.zuBits_lt Gleitkomma.f64 Gleitkomma.f64_dicht v.x hw
  rw [f64_wortGrenze] at hlt
  unfold gleitWortPasst
  rw [if_pos ⟨Int.natCast_nonneg _, by unfold gleitWortGrenze; omega⟩, Int.toNat_natCast,
    Gleitkomma.ausBits_zuBits Gleitkomma.f64 Gleitkomma.f64_dicht v.x hw]
  unfold gleitPasst
  rw [dif_pos ⟨v.endlich, v.lo_le, v.le_hi⟩]

/-- Every decoded float is well-formed. -/
theorem gleitWortPasst_wf {lo hi : Int × Int} {n : Int} {v : Gleit lo hi}
    (h : gleitWortPasst lo hi n = some v) : Gleitkomma.wf Gleitkomma.f64 v.x := by
  unfold gleitWortPasst at h
  split at h
  · unfold gleitPasst at h
    split at h
    · cases h
      exact ausBits_wf Gleitkomma.f64 Gleitkomma.f64_dicht _
    · cases h
  · cases h

/-! ## 3. Function pointers -/

/-- **Every function of signature `m` is the answer of an image that places it at `0`.** -/
theorem zeigerPasst_voll (m : Nat) (v : {f : D.Fn // D.sig f = m}) :
    zeigerPasst (fun _ => some v.1) m 0 = some v := by
  show (if h : D.sig v.1 = m then some ⟨v.1, h⟩ else Option.none) = some v
  rw [dif_pos v.2]

/-! ## 4. Every type -/

/-- The values an answer can have: every value, and for a float a well-formed one (every
    value the kernel IEEE model computes is well-formed, `GleitkommaBits.lean`). -/
def WertOk : (τ : Ty) → Wert D τ → Prop
  | .fl _ _, v => Gleitkomma.wf Gleitkomma.f64 (v : Gleit _ _).x
  | _, _ => True

/-- **Every value is an answer** (G1 repair): for every type and every value of it
    (floats: well-formed), some image and some raw word decode to it. The model's decoding
    refuses no value the type admits. -/
theorem einpassen_voll : ∀ (τ : Ty) (v : Wert D τ), WertOk τ v →
    ∃ (z : Int → Option D.Fn) (n : Int), einpassen z τ n = some v
  | .int lo hi, v, _ => ⟨fun _ => Option.none, (v : Zahl lo hi).n, by
      simp only [einpassen]
      rw [dif_pos ⟨(v : Zahl lo hi).lo_le, (v : Zahl lo hi).le_hi⟩]
      rfl⟩
  | .bool, b, _ => by
      cases b
      · exact ⟨fun _ => Option.none, 0, rfl⟩
      · exact ⟨fun _ => Option.none, 1, rfl⟩
  | .opt m, o, _ => by
      cases o with
      | none =>
          refine ⟨fun _ => Option.none, -1, ?_⟩
          simp only [einpassen]
          rw [dif_neg (by omega), if_pos (by omega)]
      | some k =>
          refine ⟨fun _ => Option.none, k.n, ?_⟩
          simp only [einpassen]
          rw [dif_pos ⟨k.lo_le, k.le_hi⟩]
  | .sum cs, v, _ => ⟨fun _ => Option.none, summeRoh cs v, summePasst_voll cs v⟩
  | .grund m, r, _ => ⟨fun _ => Option.none, ((r : Fin m).val : Int), by
      simp only [einpassen]
      rw [dif_pos ⟨Int.natCast_nonneg _, by have := (r : Fin m).2; omega⟩]
      exact congrArg some (Fin.ext (Int.toNat_natCast _))⟩
  | .never, v, _ => (v : Empty).elim
  | .fl lo hi, v, hw => ⟨fun _ => Option.none, _, gleitWortPasst_voll lo hi v hw⟩
  | .fnptr m, v, _ => ⟨fun _ => some (v : {f : D.Fn // D.sig f = m}).1, 0, zeigerPasst_voll m v⟩
  | .ptr _ _, _, _ => ⟨fun _ => Option.none, 0, rfl⟩

/-- Every decoded value is a value an answer can have. -/
theorem einpassen_wertOk : ∀ (z : Int → Option D.Fn) (τ : Ty) (n : Int) (v : Wert D τ),
    einpassen z τ n = some v → WertOk τ v
  | _, .fl _ _, _, _, h => gleitWortPasst_wf h
  | _, .int _ _, _, _, _ => trivial
  | _, .bool, _, _, _ => trivial
  | _, .opt _, _, _, _ => trivial
  | _, .sum _, _, _, _ => trivial
  | _, .grund _, _, _, _ => trivial
  | _, .never, _, _, _ => trivial
  | _, .fnptr _, _, _, _ => trivial
  | _, .ptr _ _, _, _, _ => trivial

/-- **The answer class is empty EXACTLY when the type is** (G1 repair): no raw word decodes
    under any image iff the declared type has no value an answer can have. The model decides
    no stop the declared type does not. -/
theorem antwortLeer_iff (τ : Ty) : AntwortLeer D (some τ) ↔ ∀ v : Wert D τ, ¬ WertOk τ v := by
  constructor
  · intro hL v hv
    obtain ⟨z, n, h⟩ := einpassen_voll τ v hv
    have h' : einpassenErg z (some τ) n = some v := h
    rw [hL z n] at h'
    cases h'
  · intro h z n
    show einpassen z τ n = Option.none
    cases he : einpassen z τ n with
    | none => rfl
    | some v => exact absurd (einpassen_wertOk z τ n v he) (h v)

/-- `never` has no value: an axiom returning `never` never returns. -/
theorem antwortLeer_never : AntwortLeer D (some .never) := fun _ _ => rfl

/-- A reason channel without reasons has no value. -/
theorem antwortLeer_grund0 : AntwortLeer D (some (.grund 0)) :=
  (antwortLeer_iff _).mpr fun v _ => (v : Fin 0).elim0

/-- An empty range has no value. -/
theorem antwortLeer_int_leer {lo hi : Int} (h : hi < lo) : AntwortLeer D (some (.int lo hi)) :=
  (antwortLeer_iff _).mpr fun v _ => by
    have h1 := (v : Zahl lo hi).lo_le
    have h2 := (v : Zahl lo hi).le_hi
    omega

/-- An axiom without a result always answers (its answer class is `{()}`). -/
theorem antwortLeer_keinErg : ¬ AntwortLeer D Option.none := fun h =>
  nomatch h (fun _ => Option.none) 0

/-- The G1 types have answers: an `ok | err` sum, a float range containing a well-formed
    float, a function-pointer type some function has. -/
theorem nicht_leer_von (τ : Ty) (v : Wert D τ) (hv : WertOk τ v) : ¬ AntwortLeer D (some τ) :=
  fun h => (antwortLeer_iff τ).mp h v hv

#print axioms Gabbro.Grammatik.summePasst_voll
#print axioms Gabbro.Grammatik.gleitWortPasst_voll
#print axioms Gabbro.Grammatik.einpassen_voll
#print axioms Gabbro.Grammatik.antwortLeer_iff

end Gabbro.Grammatik
