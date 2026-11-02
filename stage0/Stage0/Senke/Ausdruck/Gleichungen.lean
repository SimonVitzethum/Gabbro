/-
  File:      stage0/Stage0/Senke/Ausdruck/Gleichungen.lean
  Subject:   Constructor equations for `lowE`, checked by definitional equality. Explicit equations avoid
             realizing the large recursive equation theorem when the expression fragment grows. To extend
             the lowering, update the equation of that constructor and use `lowE_eqs` in proofs.
-/
module
public import Stage0.Senke.Ausdruck.Gleichungena
public import Stage0.Senke.Ausdruck
@[expose] public section


namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (L : Lay D) (d : Nat) {reserved : Nat}

@[lowE_eqs] theorem lowE_prod (name : Nat) {fs : List Ty} (args : Args D Γ Λ fs) :
    lowE L (reserved := reserved) (.prod name args) d =
      prodL d (prodArgsL (lowE L (reserved := reserved)) args d) :=
  congrArg (prodL d) (lowA_eq_prodArgsL args d)

@[lowE_eqs] theorem lowE_or (a b : Expr D Γ Λ .bool) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.or a b) d =
    (do let ca ← lowE L (reserved := reserved) a d; let cb ← lowE L (reserved := reserved) b (d + 1); pure (bin2 9 d ca cb)) := rfl

@[lowE_eqs] theorem lowE_not (a : Expr D Γ Λ .bool) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.not a) d =
    (do let ca ← lowE L (reserved := reserved) a d; pure (bin2 10 d ca ([ci 1 (d + 1) 1 0], d + 2))) := rfl

@[lowE_eqs] theorem lowE_none (n : Int) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.none n) d =
    some (constWords (encodeWords L (.opt n) none) d) := by rfl

@[lowE_eqs] theorem lowE_some (e : Expr D Γ Λ (.index n)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.some e) d =
    (if n ≤ 2 ^ 63 then lowE L (reserved := reserved) e d else do
      let child ← lowE L (reserved := reserved) e (d + 1)
      pure ([ci 1 d 1 0] ++ child.1, max child.2 (d + valueWords (.opt n)))) := by rfl

@[lowE_eqs] theorem lowE_istSome (e : Expr D Γ Λ (.opt n)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.istSome e) d =
    (if decide (n ≤ 2 ^ 63) then do
      let ce ← lowE L (reserved := reserved) e d
      pure (bin2 10 d (bin2 14 d ce ([ci 1 (d + 1) (-1) 0], d + 2)) ([ci 1 (d + 1) 1 0], d + 2))
    else none) := by rfl

@[lowE_eqs] theorem lowE_case (cs : List (Option Ty)) (i : Fin cs.length)
      (nutz : NutzlastExpr D Γ Λ (cs.get i)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.case cs i nutz) d =
    (if sumFits cs then lowN L (reserved := reserved) i.val nutz d else none) := by rfl

@[lowE_eqs] theorem lowN_empty (tag : Nat) :
    lowN L (reserved := reserved) (Γ := Γ) (Λ := Λ) tag .empty d = some ([ci 1 d tag 0], d + 1) := by rfl

@[lowE_eqs] theorem lowN_val (tag : Nat) {lo hi : Int} (e : Expr D Γ Λ (.int lo hi)) :
    lowN L (reserved := reserved) (Γ := Γ) (Λ := Λ) tag (.val e) d = (do
      let ce ← lowE L (reserved := reserved) e d
      pure (packSum d lo tag ce)) := by rfl

@[lowE_eqs] theorem lowE_why (n : Nat) (r : Fin n) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.why n r) d =
    some (constWords (encodeWords L (.why n) r) d) := by rfl

@[lowE_eqs] theorem lowE_forallSlots (t : D.Tab) (body : Expr D (.index (D.count t) :: Γ) Λ .bool) (hL : darf D t Λ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.forallSlots t body hL) d =
    quantL true (frei Γ reserved) d (D.count t) (lowE L (reserved := reserved) body (d + 3)) := by rfl

@[lowE_eqs] theorem lowE_existsSlots (t : D.Tab) (body : Expr D (.index (D.count t) :: Γ) Λ .bool) (hL : darf D t Λ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.existsSlots t body hL) d =
    quantL false (frei Γ reserved) d (D.count t) (lowE L (reserved := reserved) body (d + 3)) := by rfl

@[lowE_eqs] theorem lowE_reaches (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .opt (D.count t))
      (a b : Expr D Γ Λ (.index (D.count t))) (hL : darf D t Λ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.reaches t f hf a b hL) d =
    reachesL L t f d (lowE L (reserved := reserved) a d) (lowE L (reserved := reserved) b (d + 1)) := by rfl

@[lowE_eqs] theorem lowE_refEq (a b : Expr D Γ Λ (.ref n)) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.refEq a b) d =
    wordL 14 d (lowE L (reserved := reserved) a d) (lowE L (reserved := reserved) b (d + 1)) := by rfl

@[lowE_eqs] theorem lowE_slotRef (r : Expr D Γ Λ (.ref n)) (t : D.Tab) (ht : D.capTab space n = some t) (ho : D.offen t = true)
      (f : D.Feld t) (hL : darf D t Λ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.slotRef r t ht ho f hL) d =
    (do let cr ← lowE L (reserved := reserved) r (d + valueWords (D.typ t f)); slotValueC L t f d cr) := rfl

@[lowE_eqs] theorem lowE_arrNil :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.arrNil (τ := τ)) d =
    some ([ci 1 d 0 0], d + 1) := by rfl

@[lowE_eqs] theorem lowE_arrCons (a : Expr D Γ Λ τ) (rest : Expr D Γ Λ (.arr τ n)) :
    lowE L (reserved := reserved) (.arrCons a rest) d =
      (if n = 0 then lowE L (reserved := reserved) a d else do
        let head ← lowE L (reserved := reserved) a d
        let tail ← lowE L (reserved := reserved) rest (d + valueWords τ)
        pure (head.1 ++ tail.1, max (max head.2 tail.2) (d + valueWords (.arr τ (n + 1))))) := by rfl

@[lowE_eqs] theorem lowE_arrGet (a : Expr D Γ Λ (.arr τ n)) (i : Expr D Γ Λ (.index n)) :
    lowE L (reserved := reserved) (.arrGet a i) d = (if n = 1 then lowE L (reserved := reserved) a d else
      arrGetL τ n d (lowE L (reserved := reserved) a d)
        (lowE L (reserved := reserved) i (d + valueWords (.arr τ n)))) := by rfl

@[lowE_eqs] theorem lowE_arrSet (a : Expr D Γ Λ (.arr τ n)) (i : Expr D Γ Λ (.index n)) (v : Expr D Γ Λ τ) :
    lowE L (reserved := reserved) (.arrSet a i v) d = (if n = 1 then lowE L (reserved := reserved) v d else
      arrSetL τ n d (lowE L (reserved := reserved) a d)
        (lowE L (reserved := reserved) v (d + valueWords (.arr τ n)))
        (lowE L (reserved := reserved) i (d + valueWords (.arr τ n) + valueWords τ))) := by rfl

@[lowE_eqs] theorem lowE_strLit (bs : List (Zahl 0 255)) (h : bs.length ≤ n) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.strLit bs h) d =
    some (constWords (encodeWords L (.str n) ⟨bs, h⟩) d) := by rfl

@[lowE_eqs] theorem lowE_strLen (s : Expr D Γ Λ (.str n)) :
    lowE L (reserved := reserved) (.strLen s) d =
      (if n ≤ 1 then wordK 12 d (lowE L (reserved := reserved) s d) 8 else
        (lowE L (reserved := reserved) s d).map fun p => (p.1, max p.2 (d + valueWords (.str n)))) := by rfl

@[lowE_eqs] theorem lowE_strCat (s : Expr D Γ Λ (.str n)) (t : Expr D Γ Λ (.str m)) :
    lowE L (reserved := reserved) (.strCat s t) d =
    (if n + m ≤ 1 then (if n = 0 then lowE L (reserved := reserved) t d else lowE L (reserved := reserved) s d) else none) := by rfl

@[lowE_eqs] theorem lowE_strGet (s : Expr D Γ Λ (.str n)) (i : Expr D Γ Λ (.int lo hi)) :
    lowE L (reserved := reserved) (.strGet s i) d =
    (if n ≤ 1 ∧ inW lo hi = true then strGetL d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) i d)
    else if scalarFits lo hi = true then
      strGetWideL n d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) i (d + n + 2))
    else none) := by rfl

@[lowE_eqs] theorem lowE_strEq (s : Expr D Γ Λ (.str n)) (t : Expr D Γ Λ (.str m)) :
    lowE L (reserved := reserved) (.strEq s t) d =
    (if n ≤ 1 ∧ m ≤ 1 then wordL 14 d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) t (d + 1))
    else if n ≤ 1 ∨ m ≤ 1 then
      strEqMixedL n m d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) t (d + valueWords (.str n)))
    else strEqLongL n m d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) t (d + (n + 1)))) := by rfl

@[lowE_eqs] theorem lowE_strLt (s : Expr D Γ Λ (.str n)) (t : Expr D Γ Λ (.str m)) :
    lowE L (reserved := reserved) (.strLt s t) d =
    (if n ≤ 1 ∧ m ≤ 1 then wordL 13 d (lowE L (reserved := reserved) s d) (lowE L (reserved := reserved) t (d + 1)) else none) := by rfl

@[lowE_eqs] theorem lowE_strWeit (m : Nat) (s : Expr D Γ Λ (.str n)) :
    lowE L (reserved := reserved) (.strWeit m s) d =
    (if n ≤ 1 ∧ m ≤ 1 then (if m = 0 then some ([ci 1 d 0 0], d + 1) else lowE L (reserved := reserved) s d)
    else if 2 ≤ n ∧ n ≤ m then
      (lowE L (reserved := reserved) s d).map fun a =>
        (a.1 ++ (constWords (List.replicate (m - n) 0) (d + n + 1)).1,
          max a.2 (max (constWords (List.replicate (m - n) 0) (d + n + 1)).2 (d + m + 1)))
    else if n ≤ 1 then
      strExpandL n m d (lowE L (reserved := reserved) s d) (constWords (List.replicate (m - 1) 0) (d + 2))
    else strTakeL n m d (lowE L (reserved := reserved) s d)) := by rfl

@[lowE_eqs] theorem lowE_wenn (c : Expr D Γ Λ .bool) (a b : Expr D Γ Λ τ) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.wenn c a b) d =
    wennL d (lowE L (reserved := reserved) c d) (lowE L (reserved := reserved) a d) (lowE L (reserved := reserved) b d) := by rfl

@[lowE_eqs] theorem lowE_eng (e : Expr D Γ Λ (.int lo hi)) (lo' hi' : Int) (sonst : Expr D Γ Λ (.int lo' hi')) :
    lowE L (reserved := reserved) (Γ := Γ) (Λ := Λ) (Expr.eng e lo' hi' sonst) d =
    (if scalarFits lo hi && scalarFits lo' hi' then
      engL d lo hi lo' hi' (lowE L (reserved := reserved) e d) (lowE L (reserved := reserved) sonst d)
    else wideEngL lo hi lo' hi' d (lowE L (reserved := reserved) e) (lowE L (reserved := reserved) sonst)) := by rfl

@[lowE_eqs] theorem lowE_count (n : Nat) (body : Expr D (.index (n : Int) :: Γ) Λ .bool) :
    lowE L (reserved := reserved) (.count n body) d =
      countL (frei Γ reserved) d n (lowE L (reserved := reserved) body (d + 3)) := rfl

@[lowE_eqs] theorem lowE_intBuiltin1 (op : IntBuiltin [τ1] τ) (a : Expr D Γ Λ τ1) :
    lowE L (reserved := reserved) (.intBuiltin1 op a) d =
      BitBuiltin.unary op (lowE L (reserved := reserved) a) d := rfl

@[lowE_eqs] theorem lowE_intBuiltin2 (op : IntBuiltin [τ1, τ2] τ)
    (a : Expr D Γ Λ τ1) (b : Expr D Γ Λ τ2) :
    lowE L (reserved := reserved) (.intBuiltin2 op a b) d =
      intBuiltin2L op d (lowE L (reserved := reserved) a) (lowE L (reserved := reserved) b) := rfl

end Gabbro.Stage0.Senke
