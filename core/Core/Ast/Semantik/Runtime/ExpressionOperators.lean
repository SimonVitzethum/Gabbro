module

public import Core.Ast.Semantik.Runtime.ExpressionValues

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

namespace ExpressionOperators

theorem literal (value : Nat) : Ausdruckswert env slot (.lit value) :=
  BewachterAusdruck.wert ((Expr.lit value).wert env) (fun _ _ _ _ _ _ _ _ => rfl)

theorem negativeLiteral (value : Nat) : Ausdruckswert env slot (.negativeLit value) :=
  BewachterAusdruck.wert ((Expr.negativeLit value).wert env) (fun _ _ _ _ _ _ _ _ => rfl)

theorem trueLiteral : Ausdruckswert env slot .trueLit :=
  BewachterAusdruck.wert ((Expr.trueLit (scope := scope)).wert env) (fun _ _ _ _ _ _ _ _ => rfl)

theorem falseLiteral : Ausdruckswert env slot .falseLit :=
  BewachterAusdruck.wert ((Expr.falseLit (scope := scope)).wert env) (fun _ _ _ _ _ _ _ _ => rfl)

theorem variableRead (ref : Local scope type) (visible : ref.visible) (ordinary : ordinaryLocal ref.binding.name) :
    Ausdruckswert env slot (.variable ref visible ordinary) := by
  refine BewachterAusdruck.wert (env ref) ?_
  intro pre post frame position active typed checked entry
  simp only [Expr.wert, Befehl.auswerten, typed ref, Option.join, Option.bind_some, id_eq]

theorem neg (operand : Ausdruckswert env slot tree) : Ausdruckswert env slot (.neg tree) := by
  refine BewachterAusdruck.einOperand operand ((Expr.neg tree).wert env) ?_
  intro pre post frame position active typed checked entry
  simp only [TemporaryValue] at entry
  simp only [Expr.wert, Befehl.auswerten, Rahmen.zahl, entry, Option.bind_some, alsGanzzahl, Option.map_some, Ganzzahl.pack]

theorem not (operand : Ausdruckswert env slot tree) : Ausdruckswert env slot (.not tree) := by
  refine BewachterAusdruck.einOperand operand ((Expr.not tree).wert env) ?_
  intro pre post frame position active typed checked entry
  simp only [TemporaryValue] at entry
  simp only [Expr.wert, Befehl.auswerten, entry, Option.bind_some, alsBoolean, Option.map_some]

theorem arithmetic (op : Arith) (left : Ausdruckswert env slot a) (right : Ausdruckswert env (slot + 1) b) :
    Ausdruckswert env slot (.binary op a b) := by
  refine BewachterAusdruck.zweiOperandenWert left right ((Expr.binary op a b).wert env) ?_
  intro pre post frame position active typed checked entry
  rcases entry with ⟨first, second⟩
  simp only [TemporaryValue] at first second
  simp only [Expr.wert, Befehl.auswerten, Rahmen.zahl, first, second, Option.bind_some, alsGanzzahl,
    bind, Option.bind, pure, Ganzzahl.pack]

theorem divide (left : Ausdruckswert env slot a) (right : Ausdruckswert env (slot + 1) (b : Expr scope (.int lo hi)))
    (nonzero : Divisor lo hi) : Ausdruckswert env slot (.div a b nonzero) := by
  refine BewachterAusdruck.zweiOperandenWert left right ((Expr.div a b nonzero).wert env) ?_
  intro pre post frame position active typed checked entry
  rcases entry with ⟨first, second⟩
  simp only [TemporaryValue] at first second
  simp only [Expr.wert, Befehl.auswerten, Rahmen.zahl, first, second, Option.bind_some, alsGanzzahl,
    bind, Option.bind, pure, dif_pos nonzero]

theorem compare (op : Compare) (left : Ausdruckswert env slot a) (right : Ausdruckswert env (slot + 1) b) :
    Ausdruckswert env slot (.compare op a b) := by
  refine BewachterAusdruck.zweiOperandenWert left right ((Expr.compare op a b).wert env) ?_
  intro pre post frame position active typed checked entry
  rcases entry with ⟨first, second⟩
  simp only [TemporaryValue] at first second
  simp only [Expr.wert, Befehl.auswerten, Rahmen.zahl, first, second, Option.bind_some, alsGanzzahl,
    bind, Option.bind, pure]

theorem textLiteral (decoded : List Char) : Ausdruckswert env slot (.textLiteral decoded) :=
  BewachterAusdruck.wert ((Expr.textLiteral decoded).wert env) (fun _ _ _ _ _ _ _ _ => rfl)

private theorem text_readback (text : TextValue capacity) :
    wertAls (.text capacity) ⟨.text capacity, text⟩ = some text := by
  cases text with
  | mk bytes bound =>
    simp only [wertAls, dif_pos bound]
    rfl

theorem textConcat (left : Ausdruckswert env slot a) (right : Ausdruckswert env (slot + 1) b) :
    Ausdruckswert env slot (.textConcat a b) := by
  refine BewachterAusdruck.zweiOperandenWert left right ((Expr.textConcat a b).wert env) ?_
  intro pre post frame position active typed checked entry
  rcases entry with ⟨first, second⟩
  simp only [TemporaryValue] at first second
  simp only [Expr.wert, Befehl.auswerten, first, second, Option.bind_some, text_readback, bind, Option.bind, pure]

theorem textLength (operand : Ausdruckswert env slot tree) : Ausdruckswert env slot (.textLength tree) := by
  refine BewachterAusdruck.einOperand operand ((Expr.textLength tree).wert env) ?_
  intro pre post frame position active typed checked entry
  simp only [TemporaryValue] at entry
  simp only [Expr.wert, Befehl.auswerten, entry, Option.bind_some, text_readback, Option.map_some]

theorem textIndex (left : Ausdruckswert env slot (base : Expr scope (.text capacity))) (right : Ausdruckswert env (slot + 1) offset) :
    Ausdruckswert env slot (.textIndex base offset) := by
  refine BewachterAusdruck.zweiOperandenWert left right ((Expr.textIndex base offset).wert env) ?_
  intro pre post frame position active typed checked entry
  rcases entry with ⟨first, second⟩
  simp only [TemporaryValue] at first second
  let text := base.wert env
  let index := (offset.wert env).wert
  have guard : (Befehl.textIndex slot capacity).guard frame =
      some ⟨.index, (if index < 0 then text.bytes.size else index.toNat, text.bytes.size)⟩ := by
    simp only [Befehl.guard, Rahmen.zahl, first, second, Option.bind_some, text_readback, alsGanzzahl,
      bind, Option.bind, pure, index, text]
  have allowed := guardOfInstruction position active checked guard
  change (if index < 0 then text.bytes.size else index.toNat) < text.bytes.size at allowed
  have nonnegative : ¬ index < 0 := by
    intro negative
    simp only [if_pos negative, Nat.lt_irrefl] at allowed
  have fits : index.toNat < text.bytes.size := by simpa only [if_neg nonnegative] using allowed
  have read : text.bytes[index.toNat]? = some (text.bytes[index.toNat]'fits) := getElem?_pos _ _ fits
  simp only [Expr.wert, Befehl.auswerten, Id.run, Rahmen.zahl, first, second, Option.bind_some, text_readback, alsGanzzahl,
    Expr.wert, ← index, ← text, if_neg nonnegative, read, Option.getD_some]

theorem optionIsSome (ref : Local scope (indexOptionType count)) (visible : ref.visible)
    (ordinary : ordinaryLocal ref.binding.name) : Ausdruckswert env slot (.optionIsSome ref visible ordinary) := by
  refine BewachterAusdruck.einOperand (variableRead (env := env) (slot := slot) ref visible ordinary)
    ((Expr.optionIsSome ref visible ordinary).wert env) ?_
  intro pre post frame position active typed checked entry
  simp only [TemporaryValue, Expr.wert] at entry
  simp only [Expr.wert, Befehl.auswerten, entry, Option.bind_some, indexOptionType, wertAls, dif_pos rfl,
    bind, Option.bind, pure]

end ExpressionOperators

end Gabbro.Core.Ast.Semantik
