module

public import Grammatik.Logik.Invarianten.Frag.Translation

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag

variable {D : Deklaration}

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
      return ⟨Zahl.weiter lower upper value.val, fun world => by
        simp only [eval, value.property world] <;> rfl⟩
  | .add left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.add a.val b.val, fun world => by simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .sub left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.sub a.val b.val, fun world => by simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .mul left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.mul a.val b.val, fun world => by simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .neg body => do
      let value ← constantValue body locals
      return ⟨Zahl.neg value.val, fun world => by simp only [eval, value.property world] <;> rfl⟩
  | .div nonzero positive left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.div nonzero positive a.val b.val, fun world => by
        simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .rem nonzero positive left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.rem nonzero positive a.val b.val, fun world => by
        simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .sdiv nonzero left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.sdiv nonzero a.val b.val, fun world => by
        simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .srem nonzero left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.srem nonzero a.val b.val, fun world => by
        simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .band lower lower' left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.band lower lower' a.val b.val, fun world => by
        simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .bor width lower lower' upper upper' left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.bor width lower lower' upper upper' a.val b.val, fun world => by
        simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .bxor width lower lower' upper upper' left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.bxor width lower lower' upper upper' a.val b.val, fun world => by
        simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .shl width upper upper' lower lower' left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.shl width upper upper' lower lower' a.val b.val, fun world => by
        simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .shr width upper upper' lower lower' left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨Zahl.shr width upper upper' lower lower' a.val b.val, fun world => by
        simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .lt left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨decide (a.val.n < b.val.n), fun world => by
        simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .le left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨decide (a.val.n ≤ b.val.n), fun world => by
        simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .eq left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨decide (a.val.n = b.val.n), fun world => by
        simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .and left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨wahr? a.val && wahr? b.val, fun world => by
        simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .or left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨wahr? a.val || wahr? b.val, fun world => by
        simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .not body => do
      let value ← constantValue body locals
      return ⟨!wahr? value.val, fun world => by simp only [eval, value.property world] <;> rfl⟩
  | .none _ => some ⟨none, fun _ => rfl⟩
  | .some body => do
      let value ← constantValue body locals
      return ⟨some value.val, fun world => by simp only [eval, value.property world] <;> rfl⟩
  | .istSome body => do
      let value ← constantValue body locals
      return ⟨value.val.isSome, fun world => by simp only [eval, value.property world] <;> rfl⟩
  | .case cases index payload => do
      let value ← constantPayload payload locals
      return ⟨⟨index, Fall.ofNutzlast _ _ _ _ value.val⟩, fun world => by
        simp only [eval, value.property world] <;> rfl⟩
  | .why _ reason => some ⟨reason, fun _ => rfl⟩
  | .arrNil => some ⟨fun index => index.elim0, fun _ => rfl⟩
  | .arrCons head tail => do
      let a ← constantValue head locals
      let b ← constantValue tail locals
      return ⟨arrConsW a.val b.val, fun world => by simp only [eval, a.property world, b.property world] <;> rfl⟩
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
      return ⟨strLenW value.val, fun world => by simp only [eval, value.property world] <;> rfl⟩
  | .strCat left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨strCatW a.val b.val, fun world => by simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .strGet string index => do
      let s ← constantValue string locals
      let i ← constantValue index locals
      return ⟨strGetW s.val i.val.n, fun world => by simp only [eval, s.property world, i.property world] <;> rfl⟩
  | .strEq left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨strEqW a.val b.val, fun world => by simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .strLt left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨strLtW a.val b.val, fun world => by simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .strWeit capacity body => do
      let value ← constantValue body locals
      return ⟨strWeitW capacity value.val, fun world => by simp only [eval, value.property world] <;> rfl⟩
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
          simp only [eval, value.property world, fits, ↓reduceDIte] <;> rfl⟩
      else
        let alternative ← constantValue fallback locals
        return ⟨alternative.val, fun world => by
          simp only [eval, value.property world, fits, ↓reduceDIte, alternative.property world] <;> rfl⟩
  | .intBuiltin1 operation body => do
      let value ← constantValue body locals
      return ⟨evalIntBuiltin1 operation value.val, fun world => by simp only [eval, value.property world] <;> rfl⟩
  | .intBuiltin2 operation left right => do
      let a ← constantValue left locals
      let b ← constantValue right locals
      return ⟨evalIntBuiltin2 operation a.val b.val, fun world => by
        simp only [eval, a.property world, b.property world] <;> rfl⟩
  | .prod _ fields => do
      let values ← constantFields fields locals
      return ⟨values.val, fun world => by simp only [eval, values.property world] <;> rfl⟩
  | .prodGet body field => do
      let value ← constantValue body locals
      return ⟨prodGetW field value.val, fun world => by simp only [eval, value.property world] <;> rfl⟩
  | .prodSet body field replacement => do
      let value ← constantValue body locals
      let next ← constantValue replacement locals
      return ⟨prodSetW field value.val next.val, fun world => by
        simp only [eval, value.property world, next.property world] <;> rfl⟩
  | _ => none
termination_by sizeOf expression

def constantFields (fields : Args D Γ Λ types) (locals : Env D Γ) :
    Option { values : ProdVal D.Fn D.passt types //
      ∀ world, evalProd world fields world locals = values } :=
  match fields with
  | .nil => some ⟨(), fun _ => rfl⟩
  | .cons head tail => do
      let a ← constantValue head locals
      let b ← constantFields tail locals
      return ⟨(a.val, b.val), fun world => by simp only [evalProd, a.property world, b.property world] <;> rfl⟩
termination_by sizeOf fields

def constantPayload (payload : NutzlastExpr D Γ Λ type) (locals : Env D Γ) :
    Option { value : Nutzlast D.Fn D.passt type //
      ∀ world, evalNutz world payload world locals = value } :=
  match payload with
  | .empty => some ⟨(), fun _ => rfl⟩
  | .val expression => do
      let value ← constantValue expression locals
      return ⟨value.val, fun world => by simp only [evalNutz, value.property world] <;> rfl⟩
termination_by sizeOf payload

end

end Gabbro.Grammatik.Invarianten.Frag
