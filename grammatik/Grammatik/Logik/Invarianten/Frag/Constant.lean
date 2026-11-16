module

public import Grammatik.Logik.Invarianten.Frag.Bounded

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag

variable {D : Deklaration}

theorem constantBinaryCongr (operation : α → β → γ) {a a' : α} {b b' : β}
    (left : a = a') (right : b = b') : operation a b = operation a' b' := by
  cases left
  cases right
  rfl

mutual

/-- Exact constant folding in the current environment. A successful result is
    independent of every memory world, not a sample of an expression's range.
    Products and arrays are folded componentwise using their model operations. -/
def constantValue (expression : Expr D Γ Λ τ) (locals : Env D Γ) :
    Option { value : Wert D τ // ∀ world, eval world expression world locals = value } :=
  match expression with
  | .lit n => some ⟨⟨n, Int.le_refl _, Int.le_refl _⟩, fun _ => rfl⟩
  | .tru => some ⟨true, fun _ => rfl⟩
  | .fls => some ⟨false, fun _ => rfl⟩
  | .var name => some ⟨locals.get name, fun _ => rfl⟩
  | .ptrOf .. => some ⟨(), fun _ => rfl⟩
  | .fnref f _ conforms => some ⟨⟨f, conforms⟩, fun _ => rfl⟩
  | .widen lower upper body => do
      let value ← constantValue body locals
      return ⟨Zahl.weiter lower upper value.val, fun world => congrArg _ (value.property world)⟩
  | .add left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.add a.val b.val, fun world => constantBinaryCongr Zahl.add (a.property world) (b.property world)⟩
  | .sub left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.sub a.val b.val, fun world => constantBinaryCongr Zahl.sub (a.property world) (b.property world)⟩
  | .mul left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.mul a.val b.val, fun world => constantBinaryCongr Zahl.mul (a.property world) (b.property world)⟩
  | .neg body => do
      let value ← constantValue body locals
      return ⟨Zahl.neg value.val, fun world => congrArg _ (value.property world)⟩
  | .div nonzero positive left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.div nonzero positive a.val b.val, fun world => constantBinaryCongr (Zahl.div nonzero positive) (a.property world) (b.property world)⟩
  | .rem nonzero positive left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.rem nonzero positive a.val b.val, fun world => constantBinaryCongr (Zahl.rem nonzero positive) (a.property world) (b.property world)⟩
  | .sdiv nonzero left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.sdiv nonzero a.val b.val, fun world => constantBinaryCongr (Zahl.sdiv nonzero) (a.property world) (b.property world)⟩
  | .srem nonzero left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.srem nonzero a.val b.val, fun world => constantBinaryCongr (Zahl.srem nonzero) (a.property world) (b.property world)⟩
  | .band lower lower' left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.band lower lower' a.val b.val, fun world => constantBinaryCongr (Zahl.band lower lower') (a.property world) (b.property world)⟩
  | .bor width lower lower' upper upper' left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.bor width lower lower' upper upper' a.val b.val, fun world => constantBinaryCongr (Zahl.bor width lower lower' upper upper') (a.property world) (b.property world)⟩
  | .bxor width lower lower' upper upper' left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.bxor width lower lower' upper upper' a.val b.val, fun world => constantBinaryCongr (Zahl.bxor width lower lower' upper upper') (a.property world) (b.property world)⟩
  | .shl width upper upper' lower lower' left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.shl width upper upper' lower lower' a.val b.val, fun world => constantBinaryCongr (Zahl.shl width upper upper' lower lower') (a.property world) (b.property world)⟩
  | .shr width upper upper' lower lower' left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.shr width upper upper' lower lower' a.val b.val, fun world => constantBinaryCongr (Zahl.shr width upper upper' lower lower') (a.property world) (b.property world)⟩
  | .lt left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨decide (a.val.n < b.val.n), fun world => constantBinaryCongr ((fun a b => decide (Zahl.n a < Zahl.n b))) (a.property world) (b.property world)⟩
  | .le left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨decide (a.val.n ≤ b.val.n), fun world => constantBinaryCongr ((fun a b => decide (Zahl.n a ≤ Zahl.n b))) (a.property world) (b.property world)⟩
  | .eq left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨decide (a.val.n = b.val.n), fun world => constantBinaryCongr ((fun a b => decide (Zahl.n a = Zahl.n b))) (a.property world) (b.property world)⟩
  | .and left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨wahr? a.val && wahr? b.val, fun world => constantBinaryCongr ((fun a b => wahr? a && wahr? b)) (a.property world) (b.property world)⟩
  | .or left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨wahr? a.val || wahr? b.val, fun world => constantBinaryCongr ((fun a b => wahr? a || wahr? b)) (a.property world) (b.property world)⟩
  | .not body => do
      let value ← constantValue body locals
      return ⟨!wahr? value.val, fun world => congrArg _ (value.property world)⟩
  | .none _ => some ⟨none, fun _ => rfl⟩
  | .some body => do
      let value ← constantValue body locals
      return ⟨some value.val, fun world => congrArg _ (value.property world)⟩
  | .istSome body => do
      let value ← constantValue body locals
      return ⟨value.val.isSome, fun world => congrArg _ (value.property world)⟩
  | .case cases index payload => do
      let value ← constantPayload payload locals
      return ⟨⟨index, Fall.ofNutzlast _ _ _ _ value.val⟩, fun world => by
        change (⟨index, Fall.ofNutzlast _ _ _ _ (evalNutz world payload world locals)⟩ :
          Wert D (.sum cases)) = _
        rw [value.property world]⟩
  | .why _ reason => some ⟨reason, fun _ => rfl⟩
  | .arrNil => some ⟨fun index => index.elim0, fun _ => rfl⟩
  | .arrCons head tail => do
      let a ← constantValue head locals
      let b ← constantValue tail locals
      return ⟨arrConsW a.val b.val, fun world => constantBinaryCongr arrConsW (a.property world) (b.property world)⟩
  | .arrGet array index => do
      let a ← constantValue array locals
      let i ← constantValue index locals
      return ⟨a.val i.val.fin, fun world => by simp only [eval, a.property world, i.property world] <;> rfl⟩
  | .arrSet array index value => do
      let a ← constantValue array locals
      let i ← constantValue index locals
      let v ← constantValue value locals
      return ⟨arrSetW a.val i.val.fin v.val, fun world => by
        simp only [eval, a.property world, i.property world, v.property world] <;> rfl⟩
  | .strLit bytes bounded => some ⟨⟨bytes, bounded⟩, fun _ => rfl⟩
  | .strLen body => do
      let value ← constantValue body locals
      return ⟨strLenW value.val, fun world => congrArg _ (value.property world)⟩
  | .strCat left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨strCatW a.val b.val, fun world => constantBinaryCongr strCatW (a.property world) (b.property world)⟩
  | .strGet string index => do
      let s ← constantValue string locals
      let i ← constantValue index locals
      return ⟨strGetW s.val i.val.n, fun world => by simp only [eval, s.property world, i.property world] <;> rfl⟩
  | .strEq left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨strEqW a.val b.val, fun world => constantBinaryCongr strEqW (a.property world) (b.property world)⟩
  | .strLt left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨strLtW a.val b.val, fun world => constantBinaryCongr strLtW (a.property world) (b.property world)⟩
  | .strWeit capacity body => do
      let value ← constantValue body locals
      return ⟨strWeitW capacity value.val, fun world => congrArg _ (value.property world)⟩
  | .wenn test positive negative => do
      let guard ← constantValue test locals
      if chosen : wahr? guard.val = true then
        let value ← constantValue positive locals
        return ⟨value.val, fun world => by simp only [eval, guard.property world, chosen, ↓reduceIte, value.property world] <;> rfl⟩
      else
        let value ← constantValue negative locals
        return ⟨value.val, fun world => by simp only [eval, guard.property world, chosen, ↓reduceIte, value.property world] <;> rfl⟩
  | .eng body lower upper fallback => do
      let value ← constantValue body locals
      if fits : lower ≤ value.val.n ∧ value.val.n ≤ upper then
        return ⟨⟨value.val.n, fits.1, fits.2⟩, fun world => by
          have actual : lower ≤ (eval world body world locals).n ∧
              (eval world body world locals).n ≤ upper := by
            rw [value.property world]
            exact fits
          have evaluated : eval world (.eng body lower upper fallback) world locals =
              (⟨(eval world body world locals).n, actual.1, actual.2⟩ : Zahl lower upper) :=
            dif_pos actual
          have same : (eval world body world locals).n = value.val.n :=
            congrArg Zahl.n (value.property world)
          exact evaluated.trans (zahl_ext same)⟩
      else
        let alternative ← constantValue fallback locals
        return ⟨alternative.val, fun world => by
          have actual : ¬ (lower ≤ (eval world body world locals).n ∧
              (eval world body world locals).n ≤ upper) := by
            rw [value.property world]
            exact fits
          have evaluated : eval world (.eng body lower upper fallback) world locals =
              eval world fallback world locals := dif_neg actual
          exact evaluated.trans (alternative.property world)⟩
  | .intBuiltin1 operation body => do
      let value ← constantValue body locals
      return ⟨evalIntBuiltin1 operation value.val, fun world => congrArg _ (value.property world)⟩
  | .intBuiltin2 operation left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨evalIntBuiltin2 operation a.val b.val, fun world => constantBinaryCongr (evalIntBuiltin2 operation) (a.property world) (b.property world)⟩
  | .prod _ fields => do
      let values ← constantFields fields locals
      return ⟨values.val, fun world => by simp only [eval, values.property world] <;> rfl⟩
  | .prodGet body field => do
      let value ← constantValue body locals
      return ⟨prodGetW field value.val, fun world => congrArg _ (value.property world)⟩
  | .prodSet body field replacement => do
      let value ← constantValue body locals
      let next ← constantValue replacement locals
      return ⟨prodSetW field value.val next.val, fun world => by
        simp only [eval, value.property world, next.property world] <;> rfl⟩
  | _ => none

def constantFields (fields : Args D Γ Λ types) (locals : Env D Γ) :
    Option { values : ProdVal D.Fn D.passt types //
      ∀ world, evalProd world fields world locals = values } :=
  match fields with
  | .nil => some ⟨(), fun _ => rfl⟩
  | .cons head tail => do
      let a ← constantValue head locals
      let b ← constantFields tail locals
      return ⟨(a.val, b.val), fun world => by simp only [evalProd, a.property world, b.property world] <;> rfl⟩

def constantPayload (payload : NutzlastExpr D Γ Λ type) (locals : Env D Γ) :
    Option { value : Nutzlast D.Fn D.passt type //
      ∀ world, evalNutz world payload world locals = value } :=
  match payload with
  | .empty => some ⟨(), fun _ => rfl⟩
  | .val expression => do
      let value ← constantValue expression locals
      return ⟨value.val, fun world => by simp only [evalNutz, value.property world] <;> rfl⟩

end

end Gabbro.Grammatik.Invarianten.Frag
