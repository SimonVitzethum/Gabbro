/-
  File:      Grammatik/GleitZeuge.lean
  Subject:   RUNS OF FLOAT PROGRAMS WITH PINNED VALUES -- witnesses that were
             impossible while the model computed with Lean's opaque `Float`.

  Since the switch of 2026-09-14 a `Val (.fl lo hi)` carries an IEEE-754
  binary64 value as DATA (`GFloat = Gleitkomma.GBits f64`), and every float
  step (`gleitRechne`, `gleitPasst`, `bruch`, `gleitAusInt`, `gleitLt/Le`)
  reduces in the kernel. The witnesses below run concrete blocks through
  the model's semantics (`execBlock`) and pin the stored value by `decide`:

  * `lauf01_gespeichert`: `let a = 0.1 rounded; let b = 0.2 rounded;
    let c = a + b; G := c;` with every value in `0 .. 1` stores exactly
    `0x3FD3333333333334` (0.30000000000000004) in the global `G`;
  * `lauf01_ueber03`: the same sum with the declared range `0 .. 3/10`
    is OUT of range (`0.30000000000000004 > 0.3`, both as doubles), and
    the step takes the `logik bereich` outcome -- the range check bites on
    the last ulp;
  * `lauf01_vergleich`: `0.1 + 0.2 < 0.3` is FALSE and `0.3 < 0.1 + 0.2`
    TRUE (the comparisons of the model, `Expr.fllt`);
  * `laufVon_rundet`: `(double)(2^53 + 1)` rounds to `2^53` (ties to
    even) -- the conversion `gleitVon` computes;
  * `roh_trunc`: a float written to a register is truncated toward zero
    (`gleitRoh`, the meaning the `Float` model's `toInt64` had);
  * `laufDurchNull`: `1 / 0` is infinite, not finite, and falls into the
    range check's failure branch (`logik bereich`) -- floats stay FINITE.
-/
import Grammatik.Semantik

namespace Gabbro.Grammatik

open Gleitkomma

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
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
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
  ggeteilt_bewacht := fun _ h => by simp at h

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
def gzNull : Gleit gzLo gzHi := ⟨⟨false, 0, 0⟩, by decide, by decide, by decide⟩

/-- The initial world: `G = +0`, empty trace. -/
def gzWelt : World gzD where
  slots := fun t => t.elim
  globs := fun _ => gzNull
  spur := []

theorem gzDarf : gdarf gzD () [] := fun _ h => nomatch h

/-- Bits of the stored `G` after an `ok` outcome; `none` for any other outcome. -/
def gzGespeichert {Γ : Ctx} : Ausgang gzV false Γ → Option Nat
  | .ok σ _ => some (zuBits f64 (σ.globs ()).x)
  | _ => none

/-- `true` exactly for the out-of-range outcome, `logik bereich` (it was `hardware ieee`
    until 2026-09-15, verdict F1: the kernel IEEE model decides it, no oracle). -/
def gzIeee {Γ : Ctx} : Ausgang gzV false Γ → Bool
  | .logik .bereich => true
  | _ => false

/-! ## 2. `0.1 + 0.2`, range-checked and stored -/

/-- `let a = 0.1 rounded; let b = 0.2 rounded; let c = a + b in lo..hi; G := c;`
    -- the range `lo .. hi` of `c` is the parameter. -/
def gzSumme (lo hi : Int × Int) (hG : gzD.gtyp () = .fl lo hi) :
    Block gzD gzV false [] [] [] :=
  .gleitLit (1, 10) gzLo gzHi
    (.gleitLit (2, 10) gzLo gzHi
      (.gleit .add (.var (.dort .hier)) (.var .hier) lo hi
        (.cons (.assignGlob () (hG ▸ .var .hier) rfl gzDarf) .nil)))

/-- **`0.1 + 0.2` runs, passes its range `0 .. 1`, and stores exactly
    `0x3FD3333333333334`** -- the IEEE double 0.30000000000000004, pinned by
    `decide` on the model's own semantics. -/
theorem lauf01_gespeichert :
    gzGespeichert (execBlock gzO 0 gzR (gzSumme gzLo gzHi rfl) gzWelt .nil)
      = some 0x3FD3333333333334 := by decide

/-- The block of `lauf01_ueber03`: the sum declared in `0 .. 3/10`, bound and
    dropped (the global keeps `0 .. 1`; the step's range is the one checked). -/
def gzSummeEng : Block gzD gzV false [] [] [] :=
  .gleitLit (1, 10) gzLo gzHi
    (.gleitLit (2, 10) gzLo gzHi
      (.gleit .add (.var (.dort .hier)) (.var .hier) (0, 1) (3, 10) .nil))

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
        (.var (.dort .hier)) (.var .hier))
      gzWelt
      (.cons ⟨bruch (3, 10), by decide, by decide, by decide⟩
        (.cons ⟨gleitRechne .add (bruch (1, 10)) (bruch (2, 10)), by decide, by decide,
          by decide⟩ .nil))) = false := by decide

/-! ## 3. Integer conversion and a non-finite result -/

/-- `let x = (2^53 + 1) as f64; G := x` needs a wide range; here the value
    is pinned directly: `gleitAusInt (2^53 + 1)` is `2^53` (a tie, the even
    significand wins). -/
theorem laufVon_rundet : gleitAusInt (2 ^ 53 + 1) = gleitAusInt (2 ^ 53)
    ∧ zuBits f64 (gleitAusInt (2 ^ 53 + 1)) = 0x4340000000000000 := by decide

theorem roh_trunc : gleitRoh (bruch (5, 2)) = 2 ∧ gleitRoh (bruch (-5, 2)) = -2
    ∧ gleitRoh (bruch (7, 1)) = 7 ∧ gleitRoh (bruch (1, 10)) = 0 := by decide

/-- `let e = 1 as f64; let z = 0 as f64; let q = e / z in 0 .. 1` -- the
    integer conversions are range-checked, the quotient is `+inf`, not finite,
    and the step takes `logik bereich`. -/
def gzDurchNull : Block gzD gzV false [] [] [] :=
  .gleitVon (.lit 1) gzLo gzHi
    (.gleitVon (.lit 0) gzLo gzHi
      (.gleit .div (.var (.dort .hier)) (.var .hier) gzLo gzHi .nil))

theorem laufDurchNull :
    gzIeee (execBlock gzO 0 gzR gzDurchNull gzWelt .nil) = true := by decide

/-- The inhabitation side of `gleitPasst`: a finite in-range value passes
    (so `lauf01_gespeichert` is not vacuous at the check), and `+inf` never
    does, whatever the range. -/
theorem gleitPasst_unendlich (lo hi : Int × Int) :
    gleitPasst lo hi ⟨false, f64.bexpMax, 0⟩ = Option.none := by
  unfold gleitPasst
  rw [dif_neg]
  intro h
  exact absurd h.1 (by decide)

end Gabbro.Grammatik

#print axioms Gabbro.Grammatik.lauf01_gespeichert
#print axioms Gabbro.Grammatik.lauf01_ueber03
#print axioms Gabbro.Grammatik.laufDurchNull
#print axioms Gabbro.Grammatik.gleitPasst_unendlich
