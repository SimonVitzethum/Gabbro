module

public import Stage0.Senke.Bild.Ruf.IdleExpression
public import Stage0.Senke.Bild.Ruf.IdleCounters

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
    have body := funext (lowEnsAt_withIdle L original shifted reserve index start)
    have width : valueWords (D.mitRuhe.typ table field) = valueWords (D.typ table field) :=
      valueWords_mapNumbers _ _ _
    simp only [ruE, lowEnsAt, idleColumnFits (D := D), entryColumnL, width]
    with_unfolding_all rw [selected, words, body]
  | _, _, _, .widen _ _ e, start, _ | _, _, _, .not e, start, _ | _, _, _, .neg e, start, _ => by
    have mapped := funext (lowEnsAt_withIdle L original shifted reserve e start)
    simp only [ruE, lowEnsAt, mapped]
  | _, _, _, .add a b, start, _ | _, _, _, .sub a b, start, _ | _, _, _, .mul a b, start, _
  | _, _, _, .eq a b, start, _ | _, _, _, .lt a b, start, _ | _, _, _, .le a b, start, _
  | _, _, _, .and a b, start, _ | _, _, _, .or a b, start, _ => by
    have left := funext (lowEnsAt_withIdle L original shifted reserve a start)
    have right := funext (lowEnsAt_withIdle L original shifted reserve b
      (start + EntrySnapshots.words (oldCells a)))
    simp only [ruE, lowEnsAt, words_ruE L, left, right]
  | _, _, _, .intBuiltin1 op e, start, _ => by
    have mapped := funext (lowEnsAt_withIdle L original shifted reserve e start)
    cases op <;> simp only [ruE, lowEnsAt, ibR, BitBuiltin.unary, mapped]
  | _, _, _, .intBuiltin2 op a b, start, _ => by
    have left := funext (lowEnsAt_withIdle L original shifted reserve a start)
    have right := funext (lowEnsAt_withIdle L original shifted reserve b
      (start + EntrySnapshots.words (oldCells a)))
    cases op <;> simp only [ruE, lowEnsAt, words_ruE L, ibR, intBuiltin2L, left, right]
  | _, _, _, .lit .., _, dest | _, _, _, .tru .., _, dest | _, _, _, .fls .., _, dest
  | _, _, _, .var .., _, dest | _, _, _, .glob .., _, dest | _, _, _, .slot .., _, dest
  | _, _, _, .thru .., _, dest | _, _, _, .thruOwn .., _, dest | _, _, _, .ptrOf .., _, dest
  | _, _, _, .fnref .., _, dest | _, _, _, .refEq .., _, dest | _, _, _, .slotRef .., _, dest
  | _, _, _, .div .., _, dest | _, _, _, .rem .., _, dest | _, _, _, .sdiv .., _, dest
  | _, _, _, .srem .., _, dest | _, _, _, .getBytes .., _, dest | _, _, _, .band .., _, dest
  | _, _, _, .bor .., _, dest | _, _, _, .bxor .., _, dest | _, _, _, .shl .., _, dest
  | _, _, _, .shr .., _, dest | _, _, _, .fllt .., _, dest | _, _, _, .flle .., _, dest
  | _, _, _, .none .., _, dest | _, _, _, .some .., _, dest | _, _, _, .istSome .., _, dest
  | _, _, _, .case .., _, dest | _, _, _, .why .., _, dest | _, _, _, .forallSlots .., _, dest
  | _, _, _, .existsSlots .., _, dest | _, _, _, .reaches .., _, dest | _, _, _, .arrNil .., _, dest
  | _, _, _, .arrCons .., _, dest | _, _, _, .arrGet .., _, dest | _, _, _, .arrSet .., _, dest
  | _, _, _, .strLit .., _, dest | _, _, _, .strLen .., _, dest | _, _, _, .strCat .., _, dest
  | _, _, _, .strGet .., _, dest | _, _, _, .strEq .., _, dest | _, _, _, .strLt .., _, dest
  | _, _, _, .strWeit .., _, dest | _, _, _, .wenn .., _, dest | _, _, _, .eng .., _, dest
  | _, _, _, .count .., _, dest | _, _, _, .prod .., _, dest | _, _, _, .prodGet .., _, dest
  | _, _, _, .prodSet .., _, dest => by
    rw [← reserve]
    exact lowE_withIdle L shifted.ensReserved false _ dest
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
  simp only [lowPost, ensures, lowInvs_withIdle]

end Gabbro.Stage0.Senke
