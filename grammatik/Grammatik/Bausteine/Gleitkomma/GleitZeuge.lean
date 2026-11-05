/- Native CPU float program witnesses: checked ranges, comparison, conversion,
   register words and actual block outcomes through the canonical semantics. -/
module
public import Grammatik.Kern.Semantik.Semantik
@[expose] public section


namespace Gabbro.Grammatik


/-! ## 1. The declaration: one float global `G : f64 in 0 .. 1` -/

/-- One function, no parameters, no result, writes `G`. -/
def gzSig : Signatur Empty Unit Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun t => nomatch t
  gschreibt := fun _ => true
  konsumiert := []
  produziert := []

/-- The float range `0 .. 1` (as rationals `0/1 .. 1/1`). -/
abbrev gzLo : Int × Int := (0, 1)
abbrev gzHi : Int × Int := (1, 1)

def gzD : Deklaration where
  Tab := Empty
  decTab := inferInstance
  count := fun t => t.elim
  Feld := fun t => t.elim
  decFeld := fun t => t.elim
  typ := fun t => t.elim
  erlaubt := fun t => t.elim
  tabNr := fun _ => none
  Glob := Unit
  decGlob := inferInstance
  gtyp := fun _ => .fl gzLo gzHi
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun t => t.elim
  ggeteilt := fun _ => false
  Lock := Empty
  decLock := inferInstance
  rang := fun L => L.elim
  maskiert := fun L => L.elim
  Marke := Empty
  decMarke := inferInstance
  stufen := fun m => m.elim
  braucht := fun t => t.elim
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => gzSig
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun i => nomatch i
  invs := []
  Ax := Empty
  aparams := fun a => nomatch a
  aerg := fun a => nomatch a
  aschreibt := fun a => nomatch a
  agschreibt := fun a => nomatch a
  Reg := Empty
  rtyp := fun r => nomatch r
  rklasse := fun r => nomatch r
  spiegel := fun r => nomatch r
  rzusage := fun r => nomatch r
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t => t.elim
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun _ h => by simp only [Bool.false_eq_true] at h

abbrev gzV : Vertrag gzD := vertragVon gzD ()

def gzO : Orakel gzD where
  wirkt := fun a => nomatch a
  regLies := fun r => nomatch r
  regSchreib := fun r _ => nomatch r
  sichtbar := fun _ _ => true

/-- The calls of the block (there are none): any meaning will do. -/
def gzR : ∀ f : gzD.Fn, World gzD → Env gzD (gzD.params f) → RufAusgang f :=
  fun _ σ _ => .ok σ ()

/-- Only primitive classifier and bound-comparison replies for one actual value. -/
structure GzRangeAnswers (lo hi : Int × Int) (x : Float) (finite lower upper : Bool) : Prop where
  finite_reply : x.hwIsFinite = finite
  lower_reply : Float.hwLe (bruch lo) x = lower
  upper_reply : Float.hwLe x (bruch hi) = upper

/-- Retain precisely the value and range evidence returned by the hardware. -/
def GzRangeAnswers.value {lo hi : Int × Int} {x : Float}
    (answers : GzRangeAnswers lo hi x true true true) : Gleit lo hi :=
  ⟨x, answers.finite_reply, answers.lower_reply, answers.upper_reply⟩

theorem GzRangeAnswers.value_x {lo hi : Int × Int} {x : Float}
    (answers : GzRangeAnswers lo hi x true true true) : answers.value.x = x := rfl

theorem GzRangeAnswers.fits {lo hi : Int × Int} {x : Float}
    (answers : GzRangeAnswers lo hi x true true true) :
    gleitPasst lo hi x = some answers.value := by
  unfold gleitPasst
  rw [dif_pos ⟨answers.finite_reply, answers.lower_reply, answers.upper_reply⟩]
  rfl

theorem GzRangeAnswers.above {lo hi : Int × Int} {x : Float}
    (answers : GzRangeAnswers lo hi x true true false) : gleitPasst lo hi x = none := by
  simp [gleitPasst, gleitEndlich, gleitLe, answers.finite_reply,
    answers.lower_reply, answers.upper_reply]

private theorem gz_nonfinite (lo hi : Int × Int) (x : Float)
    (finite : x.hwIsFinite = false) : gleitPasst lo hi x = none := by
  simp [gleitPasst, gleitEndlich, finite]

/-- `+0` in range: the initial value of `G`, with explicit native replies. -/
def gzNull (initial : GzRangeAnswers gzLo gzHi (Float.hwOfBits 0) true true true) :
    Gleit gzLo gzHi := initial.value

/-- The initial world: `G = +0`, empty trace. -/
def gzWelt (initial : GzRangeAnswers gzLo gzHi (Float.hwOfBits 0) true true true) : World gzD where
  slots := fun t => t.elim
  globs := fun _ => gzNull initial
  spur := []

theorem gzDarf : gdarf gzD () [] := fun _ h => nomatch h

/-- Bits of the stored `G` after an `ok` outcome; `none` for any other outcome. -/
def gzGespeichert {Γ : Ctx} : Ausgang gzV false Γ → Option Nat
  | .ok σ _ => some ((σ.globs ()).x.hwToBits.toNat)
  | _ => none

/-- Detect the unchanged out-of-range logic outcome after native arithmetic. -/
def gzIeee {Γ : Ctx} : Ausgang gzV false Γ → Bool
  | .logik .bereich => true
  | _ => false

/-! ## 2. `0.1 + 0.2`, range-checked and stored -/

/-- `let a = 0.1 rounded; let b = 0.2 rounded; let c = a + b in lo..hi; G := c;`
    -- the range `lo .. hi` of `c` is the parameter. -/
def gzSumme (lo hi : Int × Int) (hG : gzD.gtyp () = .fl lo hi) :
    Block gzD gzV false [] [] [] :=
  .floatLit (1, 10) gzLo gzHi
    (.floatLit (2, 10) gzLo gzHi
      (.float .add (.var (.there .here)) (.var .here) lo hi
        (.cons (.assignGlob () (hG ▸ .var .here) rfl gzDarf) .nil)))

/-- The unchanged source run stores the supplied native addition word after all three range gates. -/
theorem lauf01_gespeichert
    (initial : GzRangeAnswers gzLo gzHi (Float.hwOfBits 0) true true true)
    (first : GzRangeAnswers gzLo gzHi (bruch (1, 10)) true true true)
    (second : GzRangeAnswers gzLo gzHi (bruch (2, 10)) true true true)
    (sum : GzRangeAnswers gzLo gzHi (Float.hwAdd (bruch (1, 10)) (bruch (2, 10))) true true true)
    (word : (Float.hwAdd (bruch (1, 10)) (bruch (2, 10))).hwToBits = 0x3FD3333333333334) :
    gzGespeichert (execBlock gzO 0 gzR (gzSumme gzLo gzHi rfl) (gzWelt initial) .nil)
      = some 0x3FD3333333333334 := by
  have a := first.fits
  have b := second.fits
  have c := sum.fits
  simp only [gzSumme, execBlock, execStmt, eval, Expr.orte, World.lese, World.merke,
    a, b, gleitRechne]
  erw [c]
  change some sum.value.x.hwToBits.toNat = some 0x3FD3333333333334
  rw [sum.value_x, word]
  rfl

/-- The block of `lauf01_ueber03`: the sum declared in `0 .. 3/10`, bound and
    dropped (the global keeps `0 .. 1`; the step's range is the one checked). -/
def gzSummeEng : Block gzD gzV false [] [] [] :=
  .floatLit (1, 10) gzLo gzHi
    (.floatLit (2, 10) gzLo gzHi
      (.float .add (.var (.there .here)) (.var .here) (0, 1) (3, 10) .nil))

/-- The last-ulp upper comparison rejects the same `0 .. 3/10` source range. -/
theorem lauf01_ueber03
    (initial : GzRangeAnswers gzLo gzHi (Float.hwOfBits 0) true true true)
    (first : GzRangeAnswers gzLo gzHi (bruch (1, 10)) true true true)
    (second : GzRangeAnswers gzLo gzHi (bruch (2, 10)) true true true)
    (sum : GzRangeAnswers (0, 1) (3, 10)
      (Float.hwAdd (bruch (1, 10)) (bruch (2, 10))) true true false) :
    gzIeee (execBlock gzO 0 gzR gzSummeEng (gzWelt initial) .nil) = true := by
  have a := first.fits
  have b := second.fits
  have c := sum.above
  simp only [gzSummeEng, execBlock, eval, Expr.orte, World.lese, World.merke,
    a, b, gleitRechne]
  erw [c]
  rfl

/-- Native comparison replies retain both strict directions and the upper-bound comparison. -/
theorem lauf01_vergleich
    (forward : Float.hwLt (Float.hwAdd (bruch (1, 10)) (bruch (2, 10))) (bruch (3, 10)) = false)
    (reverse : Float.hwLt (bruch (3, 10)) (Float.hwAdd (bruch (1, 10)) (bruch (2, 10))) = true)
    (upper : Float.hwLe (Float.hwAdd (bruch (1, 10)) (bruch (2, 10))) (bruch (1, 1)) = true) :
    gleitLt (gleitRechne .add (bruch (1, 10)) (bruch (2, 10))) (bruch (3, 10)) = false
    ∧ gleitLt (bruch (3, 10)) (gleitRechne .add (bruch (1, 10)) (bruch (2, 10))) = true
    ∧ gleitLe (gleitRechne .add (bruch (1, 10)) (bruch (2, 10))) (bruch (1, 1)) = true :=
  ⟨forward, reverse, upper⟩

/-- The same native reply is consumed by the actual language expression and ordered environment. -/
theorem lauf01_vergleichExpr
    (initial : GzRangeAnswers gzLo gzHi (Float.hwOfBits 0) true true true)
    (limit : GzRangeAnswers gzLo gzHi (bruch (3, 10)) true true true)
    (sum : GzRangeAnswers gzLo gzHi (Float.hwAdd (bruch (1, 10)) (bruch (2, 10))) true true true)
    (less : Float.hwLt (Float.hwAdd (bruch (1, 10)) (bruch (2, 10))) (bruch (3, 10)) = false) :
    wahr? (eval (gzWelt initial)
      (Expr.fllt (Γ := [.fl gzLo gzHi, .fl gzLo gzHi]) (Λ := []) (D := gzD)
        (.var (.there .here)) (.var .here))
      (gzWelt initial) (.cons limit.value (.cons sum.value .nil))) = false :=
  less

/-! ## 3. Integer conversion and a non-finite result -/

/-- The two actual native conversion replies retain the tie result and its exact word. -/
theorem laufVon_rundet
    (rounded : Float.hwOfInt (2 ^ 53 + 1) = Float.hwOfInt (2 ^ 53))
    (word : (Float.hwOfInt (2 ^ 53 + 1)).hwToBits = 0x4340000000000000) :
    gleitAusInt (2 ^ 53 + 1) = gleitAusInt (2 ^ 53)
      ∧ (gleitAusInt (2 ^ 53 + 1)).hwToBits.toNat = 0x4340000000000000 :=
  ⟨rounded, congrArg UInt64.toNat word⟩

theorem roh_trunc
    (positive : (bruch (5, 2)).hwToInt64 = Int64.ofInt 2)
    (negative : (bruch (-5, 2)).hwToInt64 = Int64.ofInt (-2))
    (integer : (bruch (7, 1)).hwToInt64 = Int64.ofInt 7)
    (fraction : (bruch (1, 10)).hwToInt64 = Int64.ofInt 0) :
    gleitRoh (bruch (5, 2)) = 2 ∧ gleitRoh (bruch (-5, 2)) = -2
      ∧ gleitRoh (bruch (7, 1)) = 7 ∧ gleitRoh (bruch (1, 10)) = 0 := by
  exact ⟨congrArg Int64.toInt positive, congrArg Int64.toInt negative,
    congrArg Int64.toInt integer, congrArg Int64.toInt fraction⟩

/-- `let e = 1 as f64; let z = 0 as f64; let q = e / z in 0 .. 1` -- the
    integer conversions are range-checked, the quotient is `+inf`, not finite,
    and the step takes `logik bereich`. -/
def gzDurchNull : Block gzD gzV false [] [] [] :=
  .floatOf (.lit 1) gzLo gzHi
    (.floatOf (.lit 0) gzLo gzHi
      (.float .div (.var (.there .here)) (.var .here) gzLo gzHi .nil))

theorem laufDurchNull
    (initial : GzRangeAnswers gzLo gzHi (Float.hwOfBits 0) true true true)
    (one : GzRangeAnswers gzLo gzHi (Float.hwOfInt 1) true true true)
    (zero : GzRangeAnswers gzLo gzHi (Float.hwOfInt 0) true true true)
    (quotient : (Float.hwDiv (Float.hwOfInt 1) (Float.hwOfInt 0)).hwIsFinite = false) :
    gzIeee (execBlock gzO 0 gzR gzDurchNull (gzWelt initial) .nil) = true := by
  have a := one.fits
  have b := zero.fits
  have c := gz_nonfinite gzLo gzHi _ quotient
  simp only [gzDurchNull, execBlock, eval, Expr.orte, World.lese, World.merke,
    a, b, gleitAusInt, gleitRechne]
  erw [c]
  rfl

/-- A native nonfinite reply rejects infinity at every range, through the canonical guard. -/
theorem gleitPasst_unendlich (lo hi : Int × Int) (infinite : Float.inf.hwIsFinite = false) :
    gleitPasst lo hi Float.inf = Option.none :=
  gz_nonfinite lo hi Float.inf infinite

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.lauf01_gespeichert
#print axioms Gabbro.Grammatik.lauf01_ueber03
#print axioms Gabbro.Grammatik.laufDurchNull
#print axioms Gabbro.Grammatik.gleitPasst_unendlich
