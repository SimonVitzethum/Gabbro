module

public import Grammatik.Korpus.Zeugnis.Zeugnis
public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Korpus.Zeugnis.ZeugnisIdent.Teil1

@[expose] public section

namespace Gabbro.Grammatik

theorem print_elab_all {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} :
    ∀ (e : Expr D Γ Λ τ),
    match printInt e with
    | some c => elabInt c = some ⟨τ, e⟩
    | none => True
  | .lit n => rfl
  | .var x => by simp only [printInt, elabInt, varOfAll_varIdx x]
  | .glob g hL => by simp only [printInt, elabInt, hL, ↓reduceDIte]
  | .slot t f i hL => by
    have ihi := print_elab_all i
    cases hi : printInt i with
    | none => simp only [printInt, hi, Option.map_none]
    | some ci =>
      have ihi' : elabInt ci = some ⟨_, i⟩ := by rw [hi] at ihi; exact ihi
      simp only [printInt, hi, Option.map_some, elabInt, ihi', hL, and_self, ↓reduceDIte, eq_mp_eq_cast, cast_eq]
  | .widen h1 h2 e => by
    have ihe := print_elab_all e
    cases he : printInt e with
    | none => simp only [printInt, he, Option.map_none]
    | some ce =>
      have ihe' : elabInt ce = some ⟨_, e⟩ := by rw [he] at ihe; exact ihe
      simp only [printInt, he, Option.map_some, elabInt, ihe', h1, h2, and_self, ↓reduceDIte]
  | .add a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp only [printInt, ha, Option.bind_none]
    | some ca =>
      cases hb : printInt b with
      | none => simp only [printInt, ha, hb, Option.bind_none, Option.bind_fun_none]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp only [printInt, ha, hb, Option.bind_some, elabInt, iha', ihb']
  | .sub a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp only [printInt, ha, Option.bind_none]
    | some ca =>
      cases hb : printInt b with
      | none => simp only [printInt, ha, hb, Option.bind_none, Option.bind_fun_none]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp only [printInt, ha, hb, Option.bind_some, elabInt, iha', ihb']
  | .neg a => by
    have iha := print_elab_all a
    cases ha : printInt a with
    | none => simp only [printInt, ha, Option.map_none]
    | some ca =>
      have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
      simp only [printInt, ha, Option.map_some, elabInt, iha']
  | .mul a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp only [printInt, ha, Option.bind_none]
    | some ca =>
      cases hb : printInt b with
      | none => simp only [printInt, ha, hb, Option.bind_none, Option.bind_fun_none]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp only [printInt, ha, hb, Option.bind_some, elabInt, iha', ihb']
  | .div h0 h1' a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp only [printInt, ha, Option.bind_none]
    | some ca =>
      cases hb : printInt b with
      | none => simp only [printInt, ha, hb, Option.bind_none, Option.bind_fun_none]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp only [printInt, ha, hb, Option.bind_some, elabInt, iha', ihb', h0, h1', and_self, ↓reduceDIte]
  | .rem h0 h1' a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp only [printInt, ha, Option.bind_none]
    | some ca =>
      cases hb : printInt b with
      | none => simp only [printInt, ha, hb, Option.bind_none, Option.bind_fun_none]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp only [printInt, ha, hb, Option.bind_some, elabInt, iha', ihb', h0, h1', and_self, ↓reduceDIte]
  | .sdiv hb a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp only [printInt, ha, Option.bind_none]
    | some ca =>
      cases hb2 : printInt b with
      | none => simp only [printInt, ha, hb2, Option.bind_none, Option.bind_fun_none]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb2] at ihb; exact ihb
        simp only [printInt, ha, hb2, Option.bind_some, elabInt, iha', ihb', Int.reduceNeg, hb, ↓reduceDIte]
  | .srem hb a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp only [printInt, ha, Option.bind_none]
    | some ca =>
      cases hb2 : printInt b with
      | none => simp only [printInt, ha, hb2, Option.bind_none, Option.bind_fun_none]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb2] at ihb; exact ihb
        simp only [printInt, ha, hb2, Option.bind_some, elabInt, iha', ihb', Int.reduceNeg, hb, ↓reduceDIte]
  | .band h0 h0' a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp only [printInt, ha, Option.bind_none]
    | some ca =>
      cases hb : printInt b with
      | none => simp only [printInt, ha, hb, Option.bind_none, Option.bind_fun_none]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp only [printInt, ha, hb, Option.bind_some, elabInt, iha', ihb', h0, h0', and_self, ↓reduceDIte]
  | .bor w h0 h0' hw1 hw2 a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp only [printInt, ha, Option.bind_none]
    | some ca =>
      cases hb : printInt b with
      | none => simp only [printInt, ha, hb, Option.bind_none, Option.bind_fun_none]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp only [printInt, ha, hb, Option.bind_some, elabInt, iha', ihb', h0, h0', hw1, hw2, and_self, ↓reduceDIte]
  | .bxor w h0 h0' hw1 hw2 a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp only [printInt, ha, Option.bind_none]
    | some ca =>
      cases hb : printInt b with
      | none => simp only [printInt, ha, hb, Option.bind_none, Option.bind_fun_none]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp only [printInt, ha, hb, Option.bind_some, elabInt, iha', ihb', h0, h0', hw1, hw2, and_self, ↓reduceDIte]
  | .shl w hw1 hw2 h0 h0' a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp only [printInt, ha, Option.bind_none]
    | some ca =>
      cases hb : printInt b with
      | none => simp only [printInt, ha, hb, Option.bind_none, Option.bind_fun_none]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp only [printInt, ha, hb, Option.bind_some, elabInt, iha', ihb', h0, h0', hw1, hw2, and_self, ↓reduceDIte]
  | .shr w hw1 hw2 h0 h0' a b => by
    have iha := print_elab_all a
    have ihb := print_elab_all b
    cases ha : printInt a with
    | none => simp only [printInt, ha, Option.bind_none]
    | some ca =>
      cases hb : printInt b with
      | none => simp only [printInt, ha, hb, Option.bind_none, Option.bind_fun_none]
      | some cb =>
        have iha' : elabInt ca = some ⟨_, a⟩ := by rw [ha] at iha; exact iha
        have ihb' : elabInt cb = some ⟨_, b⟩ := by rw [hb] at ihb; exact ihb
        simp only [printInt, ha, hb, Option.bind_some, elabInt, iha', ihb', h0, h0', hw1, hw2, and_self, ↓reduceDIte]
  | .tru => by simp only [printInt]
  | .fls => by simp only [printInt]
  | .thru _ _ _ _ _ _ => by simp only [printInt]
  | .ptrOf _ _ _ _ => by simp only [printInt]
  | .refEq _ _ => by simp only [printInt]
  | .slotRef _ _ _ _ _ _ => by simp only [printInt]
  | .fnref _ _ _ => by simp only [printInt]
  | .oldG _ _ => by simp only [printInt]
  | .oldS _ _ _ _ => by simp only [printInt]
  | .getBytes _ _ _ _ _ _ _ _ => by simp only [printInt]
  | .lt _ _ => by simp only [printInt]
  | .le _ _ => by simp only [printInt]
  | .eq _ _ => by simp only [printInt]
  | .fllt _ _ => by simp only [printInt]
  | .flle _ _ => by simp only [printInt]
  | .and _ _ => by simp only [printInt]
  | .or _ _ => by simp only [printInt]
  | .not _ => by simp only [printInt]
  | .none _ => by simp only [printInt]
  | .some _ => by simp only [printInt]
  | .istSome _ => by simp only [printInt]
  | .case _ _ _ => by simp only [printInt]
  | .why _ _ => by simp only [printInt]
  | .forallSlots _ _ _ => by simp only [printInt]
  | .existsSlots _ _ _ => by simp only [printInt]
  | .reaches _ _ _ _ _ _ => by simp only [printInt]
  | .arrNil => by simp only [printInt]
  | .arrCons _ _ => by simp only [printInt]
  | .arrGet _ _ => by simp only [printInt]
  | .arrSet _ _ _ => by simp only [printInt]
  | .strLit _ _ => by simp only [printInt]
  | .strLen _ => by simp only [printInt]
  | .strCat _ _ => by simp only [printInt]
  | .strGet _ _ => by simp only [printInt]
  | .strEq _ _ => by simp only [printInt]
  | .strLt _ _ => by simp only [printInt]
  | .strWeit _ _ => by simp only [printInt]
  | .wenn _ _ _ => by simp only [printInt]
  | .eng _ _ _ _ => by simp only [printInt]

/-- Term identity at int type: the task's proposed shape
    (`print_elab (e : CheckedExpr) : elab (print e) = some e`).
    `printInt` is partial -- the shapes with no `CertExpr` print answer
    `none` -- so the statement round-trips exactly where print is defined
    (the some-branch) and states `True` elsewhere. This is an elaboration
    detail of the fixed target, not a weakening: for every printable
    constructor it says `elab (print e) = some e`. -/
theorem print_elab {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {lo hi : Int}
    (e : Expr D Γ Λ (.int lo hi)) :
    match printInt e with
    | some c => elabInt c = some ⟨.int lo hi, e⟩
    | none => True :=
  print_elab_all e

/-- Converse: elaboration implies certificate validity -- an elaborated
    print is exactly what the range table recomputes. Combined with the
    existing `zeugnis_sound`, `elabInt c = some e` yields both the
    `GueltigAbleitung` (here) and the judgment (there). Proved by
    induction over the certificate; every premise is used (sub-equations
    feed the IHs, side hypotheses discharge the table guards). -/
end Gabbro.Grammatik
