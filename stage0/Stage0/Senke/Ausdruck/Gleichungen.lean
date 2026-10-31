/-
  File:      stage0/Stage0/Senke/Ausdruck/Gleichungen.lean
  Subject:   Constructor equations for `lowE`, checked by definitional equality. Explicit equations avoid
             realizing the large recursive equation theorem when the expression fragment grows. To extend
             the lowering, update the equation of that constructor and use `lowE_eqs` in proofs.
-/
import Stage0.Senke.Ausdruck

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (L : Lay D) (d : Nat) {reserved : Nat}

@[lowE_eqs] theorem lowE_lit (n : Int) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.lit n) d =
    (if lit32 n then some ([ci 1 d n 0], d + 1)
     else if scalarFits n n then some (konstWL 4 (BitVec.ofInt 64 n).toNat d) else none) := rfl

/-- Every representable signed64 literal is accepted, for any environment and layout. -/
theorem lowE_signed64 (n : Int) (hn : inW n n = true) :
    ∃ c top, lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit n) d = some (c, top) := by
  rw [lowE_lit]
  split
  · exact ⟨_, _, rfl⟩
  · simp only [scalarFits, hn, Bool.true_or, ↓reduceIte]
    exact ⟨_, _, rfl⟩

/-- Every unsigned64 literal uses the actual scalar materializer. -/
theorem lowE_unsigned64 (n : Int) (hn : inU n n = true) :
    ∃ c top, lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit n) d = some (c, top) := by
  rw [lowE_lit]
  split
  · exact ⟨_, _, rfl⟩
  · simp only [scalarFits, hn, Bool.or_true, ↓reduceIte]
    exact ⟨_, _, rfl⟩

theorem lowE_unsigned64_zeuge :
    (∃ c top, lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ)
      (.lit 18446744073709551615) d = some (c, top)) ∧
    (∃ c top, lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ)
      (.lit 9223372036854775808) d = some (c, top)) :=
  ⟨lowE_unsigned64 L d _ (by decide), lowE_unsigned64 L d _ (by decide)⟩

/-- Joint boundary witnesses use the same compiler equation as the generic soundness theorem. -/
theorem lowE_signed64_zeuge :
    (∃ c top, lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit (-9223372036854775808)) d = some (c, top)) ∧
    (∃ c top, lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit 9223372036854775807) d = some (c, top)) ∧
    (∃ c top, lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit (-4294967297)) d = some (c, top)) :=
  ⟨lowE_signed64 L d _ (by decide), lowE_signed64 L d _ (by decide), lowE_signed64 L d _ (by decide)⟩

/-- The new source fixtures cross the former immediate guard; truly wider literals still refuse. -/
theorem lowE_signed64_boundaries_zeuge :
    lit32 (-9223372036854775808) = false ∧ lit32 9223372036854775807 = false ∧
    lit32 (-4294967297) = false ∧
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit 18446744073709551616) d = none ∧
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (.lit (-9223372036854775809)) d = none := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  constructor <;> rw [lowE_lit] <;> rfl

@[lowE_eqs] theorem lowE_tru :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.tru) d =
    (some ([ci 1 d 1 0], d + 1)) := rfl

@[lowE_eqs] theorem lowE_fls :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.fls) d =
    (some ([ci 1 d 0 0], d + 1)) := rfl

@[lowE_eqs] theorem lowE_var (x : Var Γ τ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.var x) d =
    (if aggregateFits τ then some ([ci 2 d (vslot x reserved) 0], d + 1) else none) := rfl

@[lowE_eqs] theorem lowE_glob (g : D.Glob) (hL : gdarf D g Λ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.glob g hL) d =
    (if lit32 (L.ga g) && aggregateFits (D.gtyp g) then some ([ci 1 d (L.ga g) 0, ci 15 d d 0], d + 1) else none) := rfl

@[lowE_eqs] theorem lowE_slot (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t))) (hL : darf D t Λ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.slot t f i hL) d =
    (do let ci' ← lowE L (reserved := reserved) i d; slotC L t f d ci') := rfl

@[lowE_eqs] theorem lowE_thru (p : Expr D Γ Λ (.ptr n rw)) (t : D.Tab) (ht : D.tabNr n = some t) (f : D.Feld t)
      (i : Expr D Γ Λ (.index (D.count t))) (hL : darf D t Λ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.thru p t ht f i hL) d =
    (do let ci' ← lowE L (reserved := reserved) i d; slotC L t f d ci') := rfl

@[lowE_eqs] theorem lowE_ptrOf (t : D.Tab) (n : Nat) (ht : D.tabNr n = some t) (rw : Bool) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.ptrOf t n ht rw) d =
    (some ([ci 1 d 0 0], d + 1)) := rfl

@[lowE_eqs] theorem lowE_fnref (f : D.Fn) (n : Nat) (h : D.passt f n = true) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.fnref f n h) d =
    (if lit32 (L.fa f) then some ([ci 1 d (L.fa f) 0], d + 1) else none) := rfl

@[lowE_eqs] theorem lowE_oldG (g : D.Glob) (hL : gdarf D g Λ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.oldG g hL) d =
    (none) := rfl

@[lowE_eqs] theorem lowE_oldS (t : D.Tab) (f : D.Feld t) (i : Expr D Γ Λ (.index (D.count t))) (hL : darf D t Λ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.oldS t f i hL) d =
    (none) := rfl

@[lowE_eqs] theorem lowE_widen (h1 : lo' ≤ lo) (h2 : hi ≤ hi') (e : Expr D Γ Λ (.int lo hi)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.widen h1 h2 e) d =
    (lowE L (reserved := reserved) e d) := rfl

@[lowE_eqs] theorem lowE_add (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.add a b) d =
    (do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 3 d ca cb)) := rfl

@[lowE_eqs] theorem lowE_sub (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.sub a b) d =
    (do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 4 d ca cb)) := rfl

@[lowE_eqs] theorem lowE_neg (a : Expr D Γ Λ (.int lo hi)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.neg a) d =
    (do let ca ← lowE L (reserved := reserved) a (d + 1); pure (bin2 4 d ([ci 1 d 0 0], d + 1) ca)) := rfl

@[lowE_eqs] theorem lowE_mul (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.mul a b) d =
    (do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 5 d ca cb)) := rfl

@[lowE_eqs] theorem lowE_div (h0 : 0 ≤ l1) (h1' : 1 ≤ l2) (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.div h0 h1' a b) d =
    (if inWE a && inWE b then do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 6 d ca cb) else none) := rfl

@[lowE_eqs] theorem lowE_rem (h0 : 0 ≤ l1) (h1' : 1 ≤ l2) (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.rem h0 h1' a b) d =
    (if inWE a && inWE b then do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 7 d ca cb) else none) := rfl

@[lowE_eqs] theorem lowE_sdiv (hb : 1 ≤ l2 ∨ h2 ≤ -1) (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.sdiv hb a b) d =
    (if inWE a && inWE b && nichtMin a then do
      let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 6 d ca cb)
    else none) := rfl

@[lowE_eqs] theorem lowE_srem (hb : 1 ≤ l2 ∨ h2 ≤ -1) (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.srem hb a b) d =
    (if inWE a && inWE b && nichtMin a then do
      let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 7 d ca cb)
    else none) := rfl

@[lowE_eqs] theorem lowE_getBytes (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (n : Nat)
      (i : Expr D Γ Λ (.int lo hi)) (hlo : 0 ≤ lo) (hhi : hi + n ≤ D.count t) (hL : darf D t Λ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.getBytes t f hf n i hlo hhi hL) d =
    (if n ≤ 8 then readBytesL L t f (lowE L (reserved := reserved) i) 0 n d else none) := rfl

@[lowE_eqs] theorem lowE_band (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.band h0 h0' a b) d =
    (if inUE a && inUE b then do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 8 d ca cb) else none) := rfl

@[lowE_eqs] theorem lowE_bor (w : Nat) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w) (hw2 : h2 < 2 ^ w)
      (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.bor w h0 h0' hw1 hw2 a b) d =
    (if inUE a && inUE b then do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 9 d ca cb) else none) := rfl

@[lowE_eqs] theorem lowE_bxor (w : Nat) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (hw1 : h1 < 2 ^ w) (hw2 : h2 < 2 ^ w)
      (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.bxor w h0 h0' hw1 hw2 a b) d =
    (if inUE a && inUE b then do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 10 d ca cb) else none) := rfl

@[lowE_eqs] theorem lowE_shl (w : Nat) (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.shl w hw1 hw2 h0 h0' a b) d =
    (if inWE b && lt64 b then do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 11 d ca cb) else none) := rfl

@[lowE_eqs] theorem lowE_shr (w : Nat) (hw1 : h1 < 2 ^ w) (hw2 : h2 < (w : Int)) (h0 : 0 ≤ l1) (h0' : 0 ≤ l2) (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.shr w hw1 hw2 h0 h0' a b) d =
    (if inUE a && inUE b && lt64 b then do
      let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 12 d ca cb)
    else none) := rfl

@[lowE_eqs] theorem lowE_lt (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.lt a b) d =
    (if inW l1 h1 && inW l2 h2 then do
      let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 13 d ca cb)
    else none) := rfl

@[lowE_eqs] theorem lowE_le (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.le a b) d =
    (if inW l1 h1 && inW l2 h2 then do
      let cb ← lowE L (reserved := reserved) b d; let ca ← lowE L (reserved := reserved) a (d + 1)
      pure (bin2 10 d (bin2 13 d cb ca) ([ci 1 (d + 1) 1 0], d + 2))
    else none) := rfl

@[lowE_eqs] theorem lowE_eq (a : Expr D Γ Λ (.int l1 h1)) (b : Expr D Γ Λ (.int l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.eq a b) d =
    (if inW l1 h1 && inW l2 h2 then do
      let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 14 d ca cb)
    else none) := rfl

@[lowE_eqs] theorem lowE_fllt (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.fllt a b) d =
    floatExprL false d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b) := rfl

@[lowE_eqs] theorem lowE_flle (a : Expr D Γ Λ (.fl l1 h1)) (b : Expr D Γ Λ (.fl l2 h2)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.flle a b) d =
    floatExprL true d (lowE L (reserved := reserved) b) (lowE L (reserved := reserved) a) := rfl

@[lowE_eqs] theorem lowE_and (a b : Expr D Γ Λ .bool) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.and a b) d =
    (do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 8 d ca cb)) := rfl

@[lowE_eqs] theorem lowE_or (a b : Expr D Γ Λ .bool) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.or a b) d =
    (do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 9 d ca cb)) := rfl

@[lowE_eqs] theorem lowE_not (a : Expr D Γ Λ .bool) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.not a) d =
    (do let ca ← lowE L (reserved := reserved) a d; pure (bin2 10 d ca ([ci 1 (d + 1) 1 0], d + 2))) := rfl

@[lowE_eqs] theorem lowE_none (n : Int) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.none n) d =
    (some ([ci 1 d (-1) 0], d + 1)) := rfl

@[lowE_eqs] theorem lowE_some (e : Expr D Γ Λ (.index n)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.some e) d =
    (lowE L (reserved := reserved) e d) := rfl

@[lowE_eqs] theorem lowE_istSome (e : Expr D Γ Λ (.opt n)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.istSome e) d =
    (if decide (n ≤ 2 ^ 63) then do
      let ce ← lowE L (reserved := reserved) e d
      pure (bin2 10 d (bin2 14 d ce ([ci 1 (d + 1) (-1) 0], d + 2)) ([ci 1 (d + 1) 1 0], d + 2))
    else none) := rfl

@[lowE_eqs] theorem lowE_case (cs : List (Option (Int × Int))) (i : Fin cs.length)
      (nutz : NutzlastExpr D Γ Λ (cs.get i)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.case cs i nutz) d =
    (if sumFits cs then lowN L (reserved := reserved) i.val nutz d else none) := rfl

@[lowE_eqs] theorem lowN_empty (tag : Nat) :
    lowN L (reserved := reserved) (Γ := Γ) (Λ := Λ) tag .empty d = some ([ci 1 d tag 0], d + 1) := rfl

@[lowE_eqs] theorem lowN_num (tag : Nat) (e : Expr D Γ Λ (.int lo hi)) :
    lowN L (reserved := reserved) tag (.num e) d = (if lit32 lo then do
      let ce ← lowE L (reserved := reserved) e d
      pure (packSum d lo tag ce)
    else none) := rfl

@[lowE_eqs] theorem lowE_why (n : Nat) (r : Fin n) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.why n r) d =
    (if decide (n < 2 ^ 31) then some ([ci 1 d (r.val : Int) 0], d + 1) else none) := rfl

@[lowE_eqs] theorem lowE_forallSlots (t : D.Tab) (body : Expr D (.index (D.count t) :: Γ) Λ .bool) (hL : darf D t Λ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.forallSlots t body hL) d =
    quantL true (frei Γ reserved) d (D.count t) (lowE L (reserved := reserved) body (d + 3)) := rfl

@[lowE_eqs] theorem lowE_existsSlots (t : D.Tab) (body : Expr D (.index (D.count t) :: Γ) Λ .bool) (hL : darf D t Λ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.existsSlots t body hL) d =
    quantL false (frei Γ reserved) d (D.count t) (lowE L (reserved := reserved) body (d + 3)) := rfl

@[lowE_eqs] theorem lowE_reaches (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .opt (D.count t))
      (a b : Expr D Γ Λ (.index (D.count t))) (hL : darf D t Λ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.reaches t f hf a b hL) d =
    reachesL L t f d (lowE L (reserved := reserved) a d) (lowE L (reserved := reserved) b (d + 1)) := rfl

@[lowE_eqs] theorem lowE_refEq (a b : Expr D Γ Λ (.ref n)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.refEq a b) d =
    wordL 14 d (lowE L (reserved := reserved) a d) (lowE L (reserved := reserved) b (d + 1)) := rfl

@[lowE_eqs] theorem lowE_slotRef (r : Expr D Γ Λ (.ref n)) (t : D.Tab) (ht : D.tabNr n = some t) (ho : D.offen t = true)
      (f : D.Feld t) (hL : darf D t Λ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.slotRef r t ht ho f hL) d =
    (do let cr ← lowE L (reserved := reserved) r d; slotC L t f d cr) := rfl

@[lowE_eqs] theorem lowE_arrNil :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.arrNil (τ := τ)) d =
    some ([ci 1 d 0 0], d + 1) := rfl

@[lowE_eqs] theorem lowE_arrCons (a : Expr D Γ Λ τ) (rest : Expr D Γ Λ (.arr τ n)) :
    lowE L (reserved := reserved) (.arrCons a rest) d = (if n = 0 then lowE L (reserved := reserved) a d else none) := rfl

@[lowE_eqs] theorem lowE_arrGet (a : Expr D Γ Λ (.arr τ n)) (i : Expr D Γ Λ (.index n)) :
    lowE L (reserved := reserved) (.arrGet a i) d = (if n = 1 then lowE L (reserved := reserved) a d else none) := rfl

@[lowE_eqs] theorem lowE_arrSet (a : Expr D Γ Λ (.arr τ n)) (i : Expr D Γ Λ (.index n)) (v : Expr D Γ Λ τ) :
    lowE L (reserved := reserved) (.arrSet a i v) d = (if n = 1 then lowE L (reserved := reserved) v d else none) := rfl

@[lowE_eqs] theorem lowE_strLit (bs : List (Zahl 0 255)) (h : bs.length ≤ n) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.strLit bs h) d =
    (if n ≤ 1 then some ([ci 1 d (strN bs) 0], d + 1) else none) := rfl

@[lowE_eqs] theorem lowE_strLen (s : Expr D Γ Λ (.str n)) :
    lowE L (reserved := reserved) (.strLen s) d = (if n ≤ 1 then wordK 12 d (lowE L (reserved := reserved) s d) 8 else none) := rfl

@[lowE_eqs] theorem lowE_strCat (s : Expr D Γ Λ (.str n)) (t : Expr D Γ Λ (.str m)) :
    lowE L (reserved := reserved) (.strCat s t) d =
    (if n + m ≤ 1 then (if n = 0 then lowE L (reserved := reserved) t d else lowE L (reserved := reserved) s d) else none) := rfl

@[lowE_eqs] theorem lowE_strGet (s : Expr D Γ Λ (.str n)) (i : Expr D Γ Λ (.int lo hi)) :
    lowE L (reserved := reserved) (.strGet s i) d =
    (if n ≤ 1 ∧ inW lo hi = true then strGetL d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) i d) else none) := rfl

@[lowE_eqs] theorem lowE_strEq (s : Expr D Γ Λ (.str n)) (t : Expr D Γ Λ (.str m)) :
    lowE L (reserved := reserved) (.strEq s t) d =
    (if n ≤ 1 ∧ m ≤ 1 then wordL 14 d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) t (d + 1)) else none) := rfl

@[lowE_eqs] theorem lowE_strLt (s : Expr D Γ Λ (.str n)) (t : Expr D Γ Λ (.str m)) :
    lowE L (reserved := reserved) (.strLt s t) d =
    (if n ≤ 1 ∧ m ≤ 1 then wordL 13 d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) t (d + 1)) else none) := rfl

@[lowE_eqs] theorem lowE_strWeit (m : Nat) (s : Expr D Γ Λ (.str n)) :
    lowE L (reserved := reserved) (.strWeit m s) d =
    (if n ≤ 1 ∧ m ≤ 1 then (if m = 0 then some ([ci 1 d 0 0], d + 1) else lowE L (reserved := reserved) s d) else none) := rfl

@[lowE_eqs] theorem lowE_wenn (c : Expr D Γ Λ .bool) (a b : Expr D Γ Λ τ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.wenn c a b) d =
    wennL d (lowE L (reserved := reserved) c d) (lowE L (reserved := reserved) a d) (lowE L (reserved := reserved) b d) := rfl

@[lowE_eqs] theorem lowE_eng (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int) (sonst : Expr D Γ Λ (.int lo' hi')) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.eng e lo' hi' sonst) d =
    engL d lo hi lo' hi' (lowE L (reserved := reserved) e d) (lowE L (reserved := reserved) sonst d) := rfl

end Gabbro.Stage0.Senke
