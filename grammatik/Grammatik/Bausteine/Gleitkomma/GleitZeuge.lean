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

/-- `+0` in range: the initial value of `G`. -/
def gzNull : Gleit gzLo gzHi := ⟨Float.ofBits 0, by decide, by decide, by decide⟩

/-- The initial world: `G = +0`, empty trace. -/
def gzWelt : World gzD where
  slots := fun t => t.elim
  globs := fun _ => gzNull
  spur := []

theorem gzDarf : gdarf gzD () [] := fun _ h => nomatch h

/-- Bits of the stored `G` after an `ok` outcome; `none` for any other outcome. -/
def gzGespeichert {Γ : Ctx} : Ausgang gzV false Γ → Option Nat
  | .ok σ _ => some ((σ.globs ()).x.toBits.toNat)
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

/-- **`0.1 + 0.2` runs, passes its range `0 .. 1`, and stores exactly
    `0x3FD3333333333334`** -- the IEEE double 0.30000000000000004, pinned by
    `decide` on the model's own semantics. -/
theorem lauf01_gespeichert :
    gzGespeichert (execBlock gzO 0 gzR (gzSumme gzLo gzHi rfl) gzWelt .nil)
      = some 0x3FD3333333333334 := by decide

/-- The block of `lauf01_ueber03`: the sum declared in `0 .. 3/10`, bound and
    dropped (the global keeps `0 .. 1`; the step's range is the one checked). -/
def gzSummeEng : Block gzD gzV false [] [] [] :=
  .floatLit (1, 10) gzLo gzHi
    (.floatLit (2, 10) gzLo gzHi
      (.float .add (.var (.there .here)) (.var .here) (0, 1) (3, 10) .nil))

/-- **The range check bites on the last ulp**: `0.1 + 0.2` declared in
    `0 .. 3/10` leaves its range (`0x3FD3333333333334 > 0x3FD3333333333333 =
    (double)0.3`), and the step's outcome is `logik bereich`. -/
theorem lauf01_ueber03 :
    gzIeee (execBlock gzO 0 gzR gzSummeEng gzWelt .nil) = true := by decide

/-- The model's comparisons on the sum: `0.1 + 0.2 < 0.3` is false and
    `0.3 < 0.1 + 0.2` true; `0.1 + 0.2 <= 1` holds. -/
theorem lauf01_vergleich :
    gleitLt (gleitRechne .add (bruch (1, 10)) (bruch (2, 10))) (bruch (3, 10)) = false
    ∧ gleitLt (bruch (3, 10)) (gleitRechne .add (bruch (1, 10)) (bruch (2, 10))) = true
    ∧ gleitLe (gleitRechne .add (bruch (1, 10)) (bruch (2, 10))) (bruch (1, 1)) = true := by
  decide

/-- The same comparison as an expression of the language, evaluated: the
    condition `a + b < 0.3` over the bound values reads `false`. -/
theorem lauf01_vergleichExpr :
    wahr? (eval gzWelt
      (Expr.fllt (Γ := [.fl gzLo gzHi, .fl gzLo gzHi]) (Λ := []) (D := gzD)
        (.var (.there .here)) (.var .here))
      gzWelt
      (.cons ⟨bruch (3, 10), by decide, by decide, by decide⟩
        (.cons ⟨gleitRechne .add (bruch (1, 10)) (bruch (2, 10)), by decide, by decide,
          by decide⟩ .nil))) = false := by decide

/-! ## 3. Integer conversion and a non-finite result -/

/-- `let x = (2^53 + 1) as f64; G := x` needs a wide range; here the value
    is pinned directly: `gleitAusInt (2^53 + 1)` is `2^53` (a tie, the even
    significand wins). -/
theorem laufVon_rundet : gleitAusInt (2 ^ 53 + 1) = gleitAusInt (2 ^ 53)
    ∧ (gleitAusInt (2 ^ 53 + 1)).toBits.toNat = 0x4340000000000000 := by decide

theorem roh_trunc : gleitRoh (bruch (5, 2)) = 2 ∧ gleitRoh (bruch (-5, 2)) = -2
    ∧ gleitRoh (bruch (7, 1)) = 7 ∧ gleitRoh (bruch (1, 10)) = 0 := by decide

/-- `let e = 1 as f64; let z = 0 as f64; let q = e / z in 0 .. 1` -- the
    integer conversions are range-checked, the quotient is `+inf`, not finite,
    and the step takes `logik bereich`. -/
def gzDurchNull : Block gzD gzV false [] [] [] :=
  .floatOf (.lit 1) gzLo gzHi
    (.floatOf (.lit 0) gzLo gzHi
      (.float .div (.var (.there .here)) (.var .here) gzLo gzHi .nil))

theorem laufDurchNull :
    gzIeee (execBlock gzO 0 gzR gzDurchNull gzWelt .nil) = true := by decide

/-- The inhabitation side of `gleitPasst`: a finite in-range value passes
    (so `lauf01_gespeichert` is not vacuous at the check), and `+inf` never
    does, whatever the range. -/
theorem gleitPasst_unendlich (lo hi : Int × Int) :
    gleitPasst lo hi Float.inf = Option.none := by
  unfold gleitPasst
  rw [dif_neg]
  intro h
  exact absurd h.1 (by decide)

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.lauf01_gespeichert
#print axioms Gabbro.Grammatik.lauf01_ueber03
#print axioms Gabbro.Grammatik.laufDurchNull
#print axioms Gabbro.Grammatik.gleitPasst_unendlich
