module

public import Grammatik.Logik.Invarianten.Frag.Bounded

@[expose] public section

namespace Gabbro.Grammatik.Invarianten.Frag

variable {D : Deklaration}

/-- Share exact constant propagation and its semantic proof across operations. -/
def foldUnary (operation : α → β) {source : κ → α}
    (argument : Option { value : α // ∀ context, source context = value }) :
    Option { value : β // ∀ context, operation (source context) = value } := do
  let value ← argument
  return ⟨operation value.val, fun context => congrArg operation (value.property context)⟩

def foldBinary (operation : α → β → γ) {left : κ → α} {right : κ → β}
    (a : Option { value : α // ∀ context, left context = value })
    (b : Option { value : β // ∀ context, right context = value }) :
    Option { value : γ // ∀ context, operation (left context) (right context) = value } := do
  let a ← a
  let b ← b
  return ⟨operation a.val b.val, fun context => by
    rw [a.property context, b.property context]⟩

def foldTernary (operation : α → β → γ → δ)
    {first : κ → α} {second : κ → β} {third : κ → γ}
    (a : Option { value : α // ∀ context, first context = value })
    (b : Option { value : β // ∀ context, second context = value })
    (c : Option { value : γ // ∀ context, third context = value }) :
    Option { value : δ // ∀ context,
      operation (first context) (second context) (third context) = value } := do
  let a ← a
  let b ← b
  let c ← c
  return ⟨operation a.val b.val c.val, fun context => by
    rw [a.property context, b.property context, c.property context]⟩

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
  | .widen lower upper body =>
      foldUnary (fun argument => Zahl.weiter lower upper argument) (constantValue body locals)
  | .add left right =>
      foldBinary Zahl.add (constantValue left locals) (constantValue right locals)
  | .sub left right =>
      foldBinary Zahl.sub (constantValue left locals) (constantValue right locals)
  | .mul left right =>
      foldBinary Zahl.mul (constantValue left locals) (constantValue right locals)
  | .neg body =>
      foldUnary (fun argument => Zahl.neg argument) (constantValue body locals)
  | .div nonzero positive left right =>
      foldBinary (Zahl.div nonzero positive) (constantValue left locals) (constantValue right locals)
  | .rem nonzero positive left right =>
      foldBinary (Zahl.rem nonzero positive) (constantValue left locals) (constantValue right locals)
  | .sdiv nonzero left right =>
      foldBinary (Zahl.sdiv nonzero) (constantValue left locals) (constantValue right locals)
  | .srem nonzero left right =>
      foldBinary (Zahl.srem nonzero) (constantValue left locals) (constantValue right locals)
  | .band lower lower' left right =>
      foldBinary (Zahl.band lower lower') (constantValue left locals) (constantValue right locals)
  | .bor width lower lower' upper upper' left right =>
      foldBinary (Zahl.bor width lower lower' upper upper') (constantValue left locals) (constantValue right locals)
  | .bxor width lower lower' upper upper' left right =>
      foldBinary (Zahl.bxor width lower lower' upper upper') (constantValue left locals) (constantValue right locals)
  | .shl width upper upper' lower lower' left right =>
      foldBinary (Zahl.shl width upper upper' lower lower') (constantValue left locals) (constantValue right locals)
  | .shr width upper upper' lower lower' left right =>
      foldBinary (Zahl.shr width upper upper' lower lower') (constantValue left locals) (constantValue right locals)
  | .lt left right =>
      foldBinary ((fun a b => decide (Zahl.n a < Zahl.n b))) (constantValue left locals) (constantValue right locals)
  | .le left right =>
      foldBinary ((fun a b => decide (Zahl.n a ≤ Zahl.n b))) (constantValue left locals) (constantValue right locals)
  | .eq left right =>
      foldBinary ((fun a b => decide (Zahl.n a = Zahl.n b))) (constantValue left locals) (constantValue right locals)
  | .and left right =>
      foldBinary ((fun a b => wahr? a && wahr? b)) (constantValue left locals) (constantValue right locals)
  | .or left right =>
      foldBinary ((fun a b => wahr? a || wahr? b)) (constantValue left locals) (constantValue right locals)
  | .not body =>
      foldUnary (fun argument => !wahr? argument) (constantValue body locals)
  | .none _ => some ⟨none, fun _ => rfl⟩
  | .some body =>
      foldUnary (fun argument => some argument) (constantValue body locals)
  | .istSome body =>
      foldUnary Option.isSome (constantValue body locals)
  | .case cases index payload =>
      foldUnary (fun value => (⟨index, Fall.ofNutzlast _ _ _ _ value⟩ : Wert D (.sum cases)))
        (constantPayload payload locals)
  | .why _ reason => some ⟨reason, fun _ => rfl⟩
  | .arrNil => some ⟨fun index => index.elim0, fun _ => rfl⟩
  | .arrCons head tail =>
      foldBinary arrConsW (constantValue head locals) (constantValue tail locals)
  | .arrGet array index =>
      foldBinary (fun a i => a (Zahl.fin i)) (constantValue array locals) (constantValue index locals)
  | .arrSet array index value =>
      foldTernary (fun a i v => arrSetW a (Zahl.fin i) v)
        (constantValue array locals) (constantValue index locals) (constantValue value locals)
  | .strLit bytes bounded => some ⟨⟨bytes, bounded⟩, fun _ => rfl⟩
  | .strLen body =>
      foldUnary (fun argument => strLenW argument) (constantValue body locals)
  | .strCat left right =>
      foldBinary strCatW (constantValue left locals) (constantValue right locals)
  | .strGet string index =>
      foldBinary (fun s i => strGetW s (Zahl.n i))
        (constantValue string locals) (constantValue index locals)
  | .strEq left right =>
      foldBinary strEqW (constantValue left locals) (constantValue right locals)
  | .strLt left right =>
      foldBinary strLtW (constantValue left locals) (constantValue right locals)
  | .strWeit capacity body =>
      foldUnary (fun argument => strWeitW capacity argument) (constantValue body locals)
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
  | .intBuiltin1 operation body =>
      foldUnary (fun argument => evalIntBuiltin1 operation argument) (constantValue body locals)
  | .intBuiltin2 operation left right =>
      foldBinary (evalIntBuiltin2 operation) (constantValue left locals) (constantValue right locals)
  | .prod _ fields => constantFields fields locals
  | .prodGet body field =>
      foldUnary (fun argument => prodGetW field argument) (constantValue body locals)
  | .prodSet body field replacement =>
      foldBinary (prodSetW field) (constantValue body locals) (constantValue replacement locals)
  | _ => none


def constantFields (fields : Args D Γ Λ types) (locals : Env D Γ) :
    Option { values : ProdVal D.Fn D.passt types //
      ∀ world, evalProd world fields world locals = values } :=
  match fields with
  | .nil => some ⟨(), fun _ => rfl⟩
  | .cons head tail =>
      foldBinary Prod.mk (constantValue head locals) (constantFields tail locals)

def constantPayload (payload : NutzlastExpr D Γ Λ type) (locals : Env D Γ) :
    Option { value : Nutzlast D.Fn D.passt type //
      ∀ world, evalNutz world payload world locals = value } :=
  match payload with
  | .empty => some ⟨(), fun _ => rfl⟩
  | .val expression => constantValue expression locals

end

end Gabbro.Grammatik.Invarianten.Frag
