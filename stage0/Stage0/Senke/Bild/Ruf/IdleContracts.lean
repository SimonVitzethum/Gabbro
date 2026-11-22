module

public import Stage0.Senke.Bild.Ruf.IdleExpression
public import Stage0.Senke.Bild.Ruf.IdleCounters
import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheStatisch.T1.Teil1Basis

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik Runner.IR

variable {D : Deklaration}

private theorem lowE_holdings (L : Lay D) {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty}
    (holds : Λ = Λ') (expr : Expr D Γ Λ τ) (dest : Nat) :
    lowE L (expr.umΛ holds) dest = lowE L expr dest := by
  cases holds
  rfl

/-- The requires guard checks exactly the production source predicate. -/
theorem lowRequires_withIdle (L : Lay D) (P : Programm D) (f : D.Fn) (dest : Nat) :
    lowE L.withIdle (P.mitRuhe.requires (some f)) dest = lowE L (P.requires f) dest :=
  (lowE_holdings _ _ _ _).trans (lowE_withIdle L 0 true (P.requires f) dest)

private theorem words_ruE (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (expr : Expr D Γ Λ τ) :
    EntrySnapshots.words (oldCells (ruE expr)) = EntrySnapshots.words (oldCells expr) := by
  rw [oldCells_ruE]
  exact (EntrySnapshots.withIdle L (oldCells expr) FB).1

private theorem lowEnsAt_withIdle (L : Lay D) (original shifted : FrameLayout)
    (reserve : shifted.ensReserved = original.ensReserved) :
    ∀ {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (expr : Expr D Γ Λ τ) (start dest : Nat),
      lowEnsAt L.withIdle shifted start (ruE expr) dest = lowEnsAt L original start expr dest
  | _, _, _, .oldG .., _, _ => by
    simp only [ruE, lowEnsAt, Deklaration.mitRuhe, tyR, valueWords_mapNumbers]
  | _, _, _, .oldS table field index _, start, dest => by
    have selected := entryIndex_ruE index
    have words := words_ruE L index
    have body := lowEnsAt_withIdle L original shifted reserve index start (dest + valueWords (D.typ table field))
    have width : valueWords (D.mitRuhe.typ table field) = valueWords (D.typ table field) :=
      valueWords_mapNumbers _ _ _
    let access (i : Option Int) (words : Nat) (code : Option (List II × Nat)) :=
      match i with
      | some _ => some (copyWords (valueWords (D.typ table field)) dest start, dest + valueWords (D.typ table field))
      | none => if EntrySnapshots.columnFits table field then
          entryColumnL (D.typ table field) (start + words) dest code else none
    calc
      _ = access (entryIndex (ruE index)) (EntrySnapshots.words (oldCells (ruE index)))
          (lowEnsAt L.withIdle shifted start (ruE index) (dest + valueWords (D.typ table field))) := by
        simp only [ruE, lowEnsAt, access, idleColumnFits (D := D), entryColumnL, width]
        with_unfolding_all rfl
      _ = access (entryIndex index) (EntrySnapshots.words (oldCells index))
          (lowEnsAt L original start index (dest + valueWords (D.typ table field))) :=
        congrFun (kongr₂ access selected words) _ |>.trans (congrArg (access _ _) body)
      _ = _ := rfl
  | _, _, _, .widen (lo := lo) (hi := hi) (lo' := lo') (hi' := hi') _ _ e, start, dest =>
    congrArg (resizeIntegerL lo hi lo' hi' dest) (lowEnsAt_withIdle L original shifted reserve e start dest)
  | _, _, _, .not e, start, dest =>
    congrArg (fun source : Option (List II × Nat) => do
      let code ← source
      pure (bin2 10 dest code ([ci 1 (dest + 1) 1 0], dest + 2)))
      (lowEnsAt_withIdle L original shifted reserve e start dest)
  | _, _, _, .neg (lo := lo) (hi := hi) e, start, dest =>
    congrArg (wideNegL lo hi (-hi) (-lo) dest) (funext (lowEnsAt_withIdle L original shifted reserve e start))
  | _, _, _, .add a b, start, _ | _, _, _, .sub a b, start, _ | _, _, _, .mul a b, start, _
  | _, _, _, .eq a b, start, _ | _, _, _, .lt a b, start, _ | _, _, _, .le a b, start, _ => by
    have left := funext (lowEnsAt_withIdle L original shifted reserve a start)
    have right : lowEnsAt L.withIdle shifted (start + EntrySnapshots.words (oldCells (ruE a))) (ruE b) =
        lowEnsAt L original (start + EntrySnapshots.words (oldCells a)) b :=
      (congrArg (fun n => lowEnsAt L.withIdle shifted (start + n) (ruE b)) (words_ruE L a)).trans
        (funext (lowEnsAt_withIdle L original shifted reserve b (start + EntrySnapshots.words (oldCells a))))
    simp only [ruE, lowEnsAt]
    congr 1 <;> with_unfolding_all first | exact left | exact right
  | _, _, _, node@(.and a b), start, dest | _, _, _, node@(.or a b), start, dest => by
    have left := lowEnsAt_withIdle L original shifted reserve a start dest
    have right :=
      (congrArg (fun n => lowEnsAt L.withIdle shifted (start + n) (ruE b) (dest + 1)) (words_ruE L a)).trans
        (lowEnsAt_withIdle L original shifted reserve b (start + EntrySnapshots.words (oldCells a)) (dest + 1))
    first
    | exact kongr₂ (fun x y : Option (List II × Nat) => do
        let ca ← x
        let cb ← y
        pure (bin2 8 dest ca cb)) left right
    | exact kongr₂ (fun x y : Option (List II × Nat) => do
        let ca ← x
        let cb ← y
        pure (bin2 9 dest ca cb)) left right
  | _, _, _, .intBuiltin1 op e, start, _ => by
    have mapped := funext (lowEnsAt_withIdle L original shifted reserve e start)
    simp only [ruE, lowEnsAt, unary_withIdle, mapped]
  | _, _, _, .intBuiltin2 op a b, start, _ => by
    have left := funext (lowEnsAt_withIdle L original shifted reserve a start)
    have right : lowEnsAt L.withIdle shifted (start + EntrySnapshots.words (oldCells (ruE a))) (ruE b) =
        lowEnsAt L original (start + EntrySnapshots.words (oldCells a)) b :=
      (congrArg (fun n => lowEnsAt L.withIdle shifted (start + n) (ruE b)) (words_ruE L a)).trans
        (funext (lowEnsAt_withIdle L original shifted reserve b (start + EntrySnapshots.words (oldCells a))))
    simp only [ruE, lowEnsAt, binary_withIdle, left, right]
  | _, _, _, node@(.lit ..), _, dest | _, _, _, node@(.tru ..), _, dest | _, _, _, node@(.fls ..), _, dest
  | _, _, _, node@(.var ..), _, dest | _, _, _, node@(.glob ..), _, dest | _, _, _, node@(.slot ..), _, dest
  | _, _, _, node@(.thru ..), _, dest | _, _, _, node@(.thruOwn ..), _, dest | _, _, _, node@(.ptrOf ..), _, dest
  | _, _, _, node@(.fnref ..), _, dest | _, _, _, node@(.refEq ..), _, dest | _, _, _, node@(.slotRef ..), _, dest
  | _, _, _, node@(.div ..), _, dest | _, _, _, node@(.rem ..), _, dest | _, _, _, node@(.sdiv ..), _, dest
  | _, _, _, node@(.srem ..), _, dest | _, _, _, node@(.getBytes ..), _, dest | _, _, _, node@(.band ..), _, dest
  | _, _, _, node@(.bor ..), _, dest | _, _, _, node@(.bxor ..), _, dest | _, _, _, node@(.shl ..), _, dest
  | _, _, _, node@(.shr ..), _, dest | _, _, _, node@(.fllt ..), _, dest | _, _, _, node@(.flle ..), _, dest
  | _, _, _, node@(.none ..), _, dest | _, _, _, node@(.some ..), _, dest | _, _, _, node@(.istSome ..), _, dest
  | _, _, _, node@(.case ..), _, dest | _, _, _, node@(.why ..), _, dest | _, _, _, node@(.forallSlots ..), _, dest
  | _, _, _, node@(.existsSlots ..), _, dest | _, _, _, node@(.reaches ..), _, dest | _, _, _, node@(.arrNil ..), _, dest
  | _, _, _, node@(.arrCons ..), _, dest | _, _, _, node@(.arrGet ..), _, dest | _, _, _, node@(.arrSet ..), _, dest
  | _, _, _, node@(.strLit ..), _, dest | _, _, _, node@(.strLen ..), _, dest | _, _, _, node@(.strCat ..), _, dest
  | _, _, _, node@(.strGet ..), _, dest | _, _, _, node@(.strEq ..), _, dest | _, _, _, node@(.strLt ..), _, dest
  | _, _, _, node@(.strWeit ..), _, dest | _, _, _, node@(.wenn ..), _, dest | _, _, _, node@(.eng ..), _, dest
  | _, _, _, node@(.count ..), _, dest | _, _, _, node@(.prod ..), _, dest | _, _, _, node@(.prodGet ..), _, dest
  | _, _, _, node@(.prodSet ..), _, dest => by
    simp only [ruE, lowEnsAt]
    rw [← reserve]
    with_unfolding_all exact (lowE_withIdle L shifted.ensReserved false node dest)
termination_by structural _ _ _ expr _ _ => expr

private theorem lowEns_context (L : Lay D) (frame : FrameLayout) {Γ Γ' : Ctx}
    {Λ : List (Res D)} {τ : Ty} (equal : Γ = Γ') (e : Expr D Γ Λ τ) (dest : Nat) :
    lowEns L frame (e.umΓ equal) dest = lowEns L frame e dest := by
  cases equal
  rfl

private theorem lowEns_holdings (L : Lay D) (frame : FrameLayout) {Γ : Ctx}
    {Λ Λ' : List (Res D)} {τ : Ty} (equal : Λ = Λ') (e : Expr D Γ Λ τ) (dest : Nat) :
    lowEns L frame (e.umΛ equal) dest = lowEns L frame e dest := by
  cases equal
  rfl

private theorem lowInvs_withIdle (L : Lay D) (P : Programm D) (f : D.Fn) (dest : Nat)
    (invariants : List D.Inv) :
    lowInvs L.withIdle P.mitRuhe (some f) dest invariants = lowInvs L P f dest invariants := by
  induction invariants with
  | nil => rfl
  | cons invariant rest ih =>
    have owes : schuldet (D := D.mitRuhe) (some f) invariant = schuldet f invariant := rfl
    have check : lowE L.withIdle (P.mitRuhe.invariante invariant) dest = lowE L (P.invariante invariant) dest :=
      (lowE_holdings _ _ _ _).trans (lowE_withIdle L 0 true (P.invariante invariant) dest)
    simp only [lowInvs, owes, check, ih]

/-- The two model views share the exact ensures and owed-invariant epilogue. -/
theorem lowPost_withIdle (L : Lay D) (P : Programm D) (f : D.Fn) (dest : Nat) :
    lowPost L.withIdle (functionFrame P.mitRuhe (some f)) P.mitRuhe (some f) dest =
      lowPost L (functionFrame P f) P f dest := by
  let original := functionFrame P f
  let shifted := functionFrame P.mitRuhe (some f)
  have same : shifted.ensReserved = original.ensReserved := (functionFrame_offsets_withIdle P L f).2.2.1
  have ensures : lowEns L.withIdle shifted (P.mitRuhe.ensures (some f)) dest =
      lowEns L original (P.ensures f) dest := by
    calc
      _ = lowEns L.withIdle shifted (ruE (P.ensures f)) dest :=
        (lowEns_context _ _ _ _ _).trans (lowEns_holdings _ _ _ _ _)
      _ = _ := lowEnsAt_withIdle L original shifted same (P.ensures f) FB dest
  simp only [original, shifted] at ensures
  simp only [lowPost, ensures, lowInvs_withIdle]

end Gabbro.Stage0.Senke
