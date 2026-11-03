/-
  File:      stage0/Stage0/Senke/Ausdruck/Gleichungen.lean
  Subject:   Constructor equations for `lowE`, checked by definitional equality. Explicit equations avoid
             realizing the large recursive equation theorem when the expression fragment grows. To extend
             the lowering, update the equation of that constructor and use `lowE_eqs` in proofs.
-/
module
public import Stage0.Senke.Ausdruck
@[expose] public section

variable {currentOld : Bool}


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (L : Lay D) (d : Nat) {reserved : Nat}

@[lowE_eqs] theorem lowE_lit (n : Int) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.lit n) d =
    (if lit32 n then some ([ci 1 d n 0], d + 1) else
      some (constWords (encodeWords L (.int n n) ⟨n, by omega, by omega⟩) d)) := by rfl

/-- Every literal is accepted, whatever its range: small immediates directly, all others by the
    shared complete word materializer. -/
theorem lowE_literal (n : Int) :
    ∃ c top, lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit n) d = some (c, top) := by
  rw [lowE_lit]
  split <;> exact ⟨_, _, rfl⟩

/-- Every representable signed64 literal is accepted, for any environment and layout. -/
theorem lowE_signed64 (n : Int) (_ : inW n n = true) :
    ∃ c top, lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit n) d = some (c, top) :=
  lowE_literal L d n

/-- Every unsigned64 literal uses the shared materializer. -/
theorem lowE_unsigned64 (n : Int) (_ : inU n n = true) :
    ∃ c top, lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit n) d = some (c, top) :=
  lowE_literal L d n

theorem lowE_unsigned64_zeuge :
    (∃ c top, lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ)
      (.lit 18446744073709551615) d = some (c, top)) ∧
    (∃ c top, lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ)
      (.lit 9223372036854775808) d = some (c, top)) :=
  ⟨lowE_unsigned64 L d _ (by decide), lowE_unsigned64 L d _ (by decide)⟩

/-- Joint boundary witnesses use the same compiler equation as the generic soundness theorem. -/
theorem lowE_signed64_zeuge :
    (∃ c top, lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit (-9223372036854775808)) d = some (c, top)) ∧
    (∃ c top, lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit 9223372036854775807) d = some (c, top)) ∧
    (∃ c top, lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit (-4294967297)) d = some (c, top)) :=
  ⟨lowE_signed64 L d _ (by decide), lowE_signed64 L d _ (by decide), lowE_signed64 L d _ (by decide)⟩

/-- The immediate guard is crossed at the signed32 boundary, and literals beyond the 64-bit scalar
    ranges are no longer refused: they materialize as multiword values. -/
theorem lowE_literal_boundaries_zeuge :
    lit32 (-9223372036854775808) = false ∧ lit32 9223372036854775807 = false ∧
    lit32 (-4294967297) = false ∧
    (∃ c top, lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit 18446744073709551616) d = some (c, top)) ∧
    (∃ c top, lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit (-9223372036854775809)) d = some (c, top)) :=
  ⟨by decide, by decide, by decide, lowE_literal L d _, lowE_literal L d _⟩

@[lowE_eqs] theorem lowE_tru :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.tru) d =
    (some ([ci 1 d 1 0], d + 1)) := by rfl

@[lowE_eqs] theorem lowE_fls :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.fls) d =
    (some ([ci 1 d 0 0], d + 1)) := by rfl

@[lowE_eqs] theorem lowE_var (x : Var Γ τ) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.var x) d =
    some (copyWords (valueWords τ) d (vslot x reserved), d + valueWords τ) := by rfl

@[lowE_eqs] theorem lowE_glob (g : D.Glob) (hL : gdarf D g Λ) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.glob g hL) d =
    globalValueC L g d := by rfl

@[lowE_eqs] theorem lowE_slot (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t))) (hL : darf D t Λ) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.slot t f i hL) d =
    (do let ci' ← lowE (currentOld := currentOld) L (reserved := reserved) i (d + valueWords (D.typ t f)); slotValueC L t f d ci') := rfl

@[lowE_eqs] theorem lowE_thru (p : Expr D Γ Λ (.ptr (.table n (true, rw) space))) (t : D.Tab) (ht : D.capTab space n = some t) (f : D.Feld t)
      (i : Expr D Γ Λ (.index (D.count t))) (hL : darf D t Λ) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.thru p t ht f i hL) d =
    (do let ci' ← lowE (currentOld := currentOld) L (reserved := reserved) i (d + valueWords (D.typ t f)); slotValueC L t f d ci') := rfl

@[lowE_eqs] theorem lowE_thruOwn (p : Expr D Γ Λ (.ptr ⟨space, ⟨true, rw, some o⟩, .table n⟩)) (t : D.Tab)
      (ht : D.capTab space n = some t) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t)))
      (m : D.Marke) (s : Nat) (ho : D.ownerNr o = some m) (he : m ∈ D.eigner t)
      (hg : Sum.inr (m, s) ∈ D.braucht t) (hL : darf D t Λ) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.thruOwn p t ht f i m s ho he hg hL) d =
    (do let ci' ← lowE (currentOld := currentOld) L (reserved := reserved) i (d + valueWords (D.typ t f)); slotValueC L t f d ci') := rfl

@[lowE_eqs] theorem lowE_ptrOf (t : D.Tab) (n : Nat) (ht : D.capTab space n = some t) (rw : Bool × Bool) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.ptrOf t n ht rw) d =
    (some ([ci 1 d 0 0], d + 1)) := by rfl

@[lowE_eqs] theorem lowE_fnref (f : D.Fn) (n : Nat) (h : D.passt f n = true) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.fnref f n h) d =
    (if lit32 (L.fa f) then some ([ci 1 d (L.fa f) 0], d + 1) else none) := by rfl

@[lowE_eqs] theorem lowE_oldG (g : D.Glob) (hL : gdarf D g Λ) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.oldG g hL) d =
    (if currentOld then globalValueC L g d else none) := by rfl

@[lowE_eqs] theorem lowE_oldS (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t))) (hL : darf D t Λ) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.oldS t f i hL) d =
    (if currentOld then do
      let index ← lowE (currentOld := currentOld) L (reserved := reserved) i (d + valueWords (D.typ t f))
      slotValueC L t f d index
    else none) := by rfl

@[lowE_eqs] theorem lowE_widen (h1 : lo' ≤ lo) (h2 : hi ≤ hi') (e : Expr D Γ Λ (.int lo hi)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.widen h1 h2 e) d =
    resizeIntegerL lo hi lo' hi' d (lowE (currentOld := currentOld) L (reserved := reserved) e d) := by rfl

@[lowE_eqs] theorem lowE_add (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.add a b) d =
    (if valueWords (.int (l1 + l2) (h1 + h2)) = 1 then
      do let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a d; let cb ← lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1); pure (bin2 3 d ca cb)
    else wideAddL l1 h1 l2 h2 (l1 + l2) (h1 + h2) d (lowE (currentOld := currentOld) L (reserved := reserved) a) (lowE (currentOld := currentOld) L (reserved := reserved) b)) := by rfl

@[lowE_eqs] theorem lowE_sub (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.sub a b) d =
    (if valueWords (.int (l1 - h2) (h1 - l2)) = 1 then
      do let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a d; let cb ← lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1); pure (bin2 4 d ca cb)
    else wideSubL l1 h1 l2 h2 (l1 - h2) (h1 - l2) d (lowE (currentOld := currentOld) L (reserved := reserved) a) (lowE (currentOld := currentOld) L (reserved := reserved) b)) := by rfl

@[lowE_eqs] theorem lowE_neg (a : Expr D Γ Λ (.int lo hi)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.neg a) d =
    (if valueWords (.int (-hi) (-lo)) = 1 then
      do let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a (d + 1); pure (bin2 4 d ([ci 1 d 0 0], d + 1) ca)
    else wideNegL lo hi (-hi) (-lo) d (lowE (currentOld := currentOld) L (reserved := reserved) a)) := by rfl

@[lowE_eqs] theorem lowE_mul (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.mul a b) d =
    (if valueWords (.int (imin (imin (l1*l2) (l1*h2)) (imin (h1*l2) (h1*h2)))
      (imax (imax (l1*l2) (l1*h2)) (imax (h1*l2) (h1*h2)))) = 1 then
      do let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a d; let cb ← lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1); pure (bin2 5 d ca cb)
    else wideMulL l1 h1 l2 h2 (imin (imin (l1*l2) (l1*h2)) (imin (h1*l2) (h1*h2)))
      (imax (imax (l1*l2) (l1*h2)) (imax (h1*l2) (h1*h2))) d (lowE (currentOld := currentOld) L (reserved := reserved) a) (lowE (currentOld := currentOld) L (reserved := reserved) b)) := by rfl

@[lowE_eqs] theorem lowE_div (h0 : 0 ≤ l1) (h1' : 1 ≤ l2) (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.div h0 h1' a b) d =
    (if inUE a && inUE b then do let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a d; let cb ← lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1); pure (bin2 25 d ca cb)
    else wideDivL l1 h1 l2 h2 0 h1 d (lowE (currentOld := currentOld) L (reserved := reserved) a) (lowE (currentOld := currentOld) L (reserved := reserved) b)) := by rfl

@[lowE_eqs] theorem lowE_rem (h0 : 0 ≤ l1) (h1' : 1 ≤ l2) (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.rem h0 h1' a b) d =
    (if inUE a && inUE b then do let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a d; let cb ← lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1); pure (bin2 26 d ca cb)
    else wideRemL l1 h1 l2 h2 0 (h2 - 1) d (lowE (currentOld := currentOld) L (reserved := reserved) a) (lowE (currentOld := currentOld) L (reserved := reserved) b)) := by rfl

@[lowE_eqs] theorem lowE_sdiv (hb : 1 ≤ l2 ∨ h2 ≤ -1) (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.sdiv hb a b) d =
    (if inWE a && inWE b && nichtMin a then do
      let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a d; let cb ← lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1); pure (bin2 6 d ca cb)
    else wideSdivL l1 h1 l2 h2 (-(betragMax l1 h1)) (betragMax l1 h1) d
      (lowE (currentOld := currentOld) L (reserved := reserved) a) (lowE (currentOld := currentOld) L (reserved := reserved) b)) := by rfl

@[lowE_eqs] theorem lowE_srem (hb : 1 ≤ l2 ∨ h2 ≤ -1) (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.srem hb a b) d =
    (if inWE a && inWE b && nichtMin a then do
      let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a d; let cb ← lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1); pure (bin2 7 d ca cb)
    else wideSremL l1 h1 l2 h2 (-(betragMax l2 h2 - 1)) (betragMax l2 h2 - 1) d
      (lowE (currentOld := currentOld) L (reserved := reserved) a) (lowE (currentOld := currentOld) L (reserved := reserved) b)) := by rfl

@[lowE_eqs] theorem lowE_getBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (n : Nat)
      (i : Expr D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo) (hhi : hi + n ≤ D.count t) (hL : darf D t Λ) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.getBytes t f hf n i hlo hhi hL) d =
    (if n ≤ 8 then readBytesL L t f (lowE (currentOld := currentOld) L (reserved := reserved) i) 0 n d else
      readBytesWideL L t f (lowE (currentOld := currentOld) L (reserved := reserved) i) n d) := by rfl

@[lowE_eqs] theorem lowE_band (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.band h0 h0' a b) d =
    (if inUE a && inUE b then do let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a d; let cb ← lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1); pure (bin2 8 d ca cb)
    else wideBitL 8 l1 h1 l2 h2 0 h1 d (lowE (currentOld := currentOld) L (reserved := reserved) a) (lowE (currentOld := currentOld) L (reserved := reserved) b)) := by rfl

@[lowE_eqs] theorem lowE_bor (w : Nat) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w) (hw2 : h2 < 2 ^ w)
      (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.bor w h0 h0' hw1 hw2 a b) d =
    (if inUE a && inUE b then resizeIntegerL 0 (2 ^ 64 - 1) 0 (2 ^ w - 1) d
      (do let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a d; let cb ← lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1); pure (bin2 9 d ca cb))
    else wideBitL 9 l1 h1 l2 h2 0 (2 ^ w - 1) d (lowE (currentOld := currentOld) L (reserved := reserved) a) (lowE (currentOld := currentOld) L (reserved := reserved) b)) := by rfl

@[lowE_eqs] theorem lowE_bxor (w : Nat) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w) (hw2 : h2 < 2 ^ w)
      (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.bxor w h0 h0' hw1 hw2 a b) d =
    (if inUE a && inUE b then resizeIntegerL 0 (2 ^ 64 - 1) 0 (2 ^ w - 1) d
      (do let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a d; let cb ← lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1); pure (bin2 10 d ca cb))
    else wideBitL 10 l1 h1 l2 h2 0 (2 ^ w - 1) d (lowE (currentOld := currentOld) L (reserved := reserved) a) (lowE (currentOld := currentOld) L (reserved := reserved) b)) := by rfl

@[lowE_eqs] theorem lowE_shl (w : Nat) (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.shl w hw1 hw2 h0 h0' a b) d =
    (if decide (valueWords (.int 0 (h1 * 2 ^ h2.toNat)) = 1) && inWE b && lt64 b then
      do let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a d; let cb ← lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1); pure (bin2 11 d ca cb)
    else wideShlL l1 h1 l2 h2 0 (h1 * 2 ^ h2.toNat) d (lowE (currentOld := currentOld) L (reserved := reserved) a) (lowE (currentOld := currentOld) L (reserved := reserved) b)) := by rfl

@[lowE_eqs] theorem lowE_shr (w : Nat) (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.shr w hw1 hw2 h0 h0' a b) d =
    (if inUE a && inUE b && lt64 b then do
      let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a d; let cb ← lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1); pure (bin2 12 d ca cb)
    else wideShrL l1 h1 l2 h2 0 h1 d (lowE (currentOld := currentOld) L (reserved := reserved) a) (lowE (currentOld := currentOld) L (reserved := reserved) b)) := by rfl

@[lowE_eqs] theorem lowE_lt (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Expr.lt a b) d =
    (if scalarFits l1 h1 && scalarFits l2 h2 then
      scalarCompareL false d l1 h1 l2 h2 (lowE (currentOld := currentOld) L (reserved := reserved) a d) (lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1))
    else wideLtL l1 h1 l2 h2 d (lowE (currentOld := currentOld) L (reserved := reserved) a) (lowE (currentOld := currentOld) L (reserved := reserved) b)) := by rfl

@[lowE_eqs] theorem lowE_le (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Expr.le a b) d =
    (if scalarFits l1 h1 && scalarFits l2 h2 then do
      let c ← scalarCompareL false d l2 h2 l1 h1
        (lowE (currentOld := currentOld) L (reserved := reserved) b d) (lowE (currentOld := currentOld) L (reserved := reserved) a (d + 1))
      pure (bin2 10 d c ([ci 1 (d + 1) 1 0], d + 2))
    else wideLeL l1 h1 l2 h2 d (lowE (currentOld := currentOld) L (reserved := reserved) a) (lowE (currentOld := currentOld) L (reserved := reserved) b)) := by rfl

@[lowE_eqs] theorem lowE_eq (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Expr.eq a b) d =
    (if scalarFits l1 h1 && scalarFits l2 h2 then
      scalarCompareL true d l1 h1 l2 h2 (lowE (currentOld := currentOld) L (reserved := reserved) a d) (lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1))
    else wideEqL l1 h1 l2 h2 d (lowE (currentOld := currentOld) L (reserved := reserved) a) (lowE (currentOld := currentOld) L (reserved := reserved) b)) := by rfl

@[lowE_eqs] theorem lowE_fllt (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.fllt a b) d =
    floatExprL false d (lowE (currentOld := currentOld) L (reserved := reserved) a) (lowE (currentOld := currentOld) L (reserved := reserved) b) := by rfl

@[lowE_eqs] theorem lowE_flle (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2)) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.flle a b) d =
    floatExprL true d (lowE (currentOld := currentOld) L (reserved := reserved) b) (lowE (currentOld := currentOld) L (reserved := reserved) a) := by rfl

@[lowE_eqs] theorem lowE_and (a b : Expr D Γ Λ .bool) :
    lowE (currentOld := currentOld) L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.and a b) d =
    (do let ca ← lowE (currentOld := currentOld) L (reserved := reserved) a d; let cb ← lowE (currentOld := currentOld) L (reserved := reserved) b (d + 1); pure (bin2 8 d ca cb)) := rfl


end Gabbro.Stage0.Senke
