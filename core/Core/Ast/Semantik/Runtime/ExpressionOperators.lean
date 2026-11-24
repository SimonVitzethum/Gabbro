module

public import Core.Ast.Semantik.Runtime.ExpressionValues

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

namespace ExpressionOperators

theorem literal (value : Nat) : Ausdruckswert env slot (.lit value) :=
  BewachterAusdruck.wert (Zahl.literal (value : Int)) (fun _ _ _ _ _ _ _ _ => rfl)

theorem negativeLiteral (value : Nat) : Ausdruckswert env slot (.negativeLit value) :=
  BewachterAusdruck.wert (Zahl.literal (-(value : Int))) (fun _ _ _ _ _ _ _ _ => rfl)

theorem trueLiteral : Ausdruckswert env slot .trueLit :=
  BewachterAusdruck.wert true (fun _ _ _ _ _ _ _ _ => rfl)

theorem falseLiteral : Ausdruckswert env slot .falseLit :=
  BewachterAusdruck.wert false (fun _ _ _ _ _ _ _ _ => rfl)

theorem variableRead (ref : Local scope type) (visible : ref.visible) (ordinary : ordinaryLocal ref.binding.name) :
    Ausdruckswert env slot (.variable ref visible ordinary) := by
  refine BewachterAusdruck.wert (env ref) ?_
  intro pre post frame position active typed checked entry
  simp only [Befehl.auswerten, typed ref, Option.join]

theorem neg (operand : Ausdruckswert env slot tree) : Ausdruckswert env slot (.neg tree) := by
  refine BewachterAusdruck.einOperand operand (tree.wert env).neg ?_
  intro pre post frame position active typed checked entry
  simp only [TemporaryValue] at entry
  simp only [Befehl.auswerten, Rahmen.zahl, entry, Option.bind_some, alsGanzzahl, Option.map_some, Ganzzahl.pack]

theorem not (operand : Ausdruckswert env slot tree) : Ausdruckswert env slot (.not tree) := by
  refine BewachterAusdruck.einOperand operand (!(tree.wert env)) ?_
  intro pre post frame position active typed checked entry
  simp only [TemporaryValue] at entry
  simp only [Befehl.auswerten, entry, Option.bind_some, alsBoolean, Option.map_some]

theorem arithmetic (op : Arith) (left : Ausdruckswert env slot a) (right : Ausdruckswert env (slot + 1) b) :
    Ausdruckswert env slot (.binary op a b) := by
  refine BewachterAusdruck.zweiOperandenWert left right (op.auswerten (a.wert env) (b.wert env)) ?_
  intro pre post frame position active typed checked entry
  rcases entry with ⟨first, second⟩
  simp only [TemporaryValue] at first second
  simp only [Befehl.auswerten, Rahmen.zahl, first, second, Option.bind_some, alsGanzzahl,
    bind, Option.bind, pure, Ganzzahl.pack]

theorem divide (left : Ausdruckswert env slot a) (right : Ausdruckswert env (slot + 1) b)
    (nonzero : Divisor lo hi) : Ausdruckswert env slot (.div a b nonzero) := by
  refine BewachterAusdruck.zweiOperandenWert left right ((a.wert env).div (b.wert env) nonzero) ?_
  intro pre post frame position active typed checked entry
  rcases entry with ⟨first, second⟩
  simp only [TemporaryValue] at first second
  simp only [Befehl.auswerten, Rahmen.zahl, first, second, Option.bind_some, alsGanzzahl,
    bind, Option.bind, pure, dif_pos nonzero]

theorem compare (op : Compare) (left : Ausdruckswert env slot a) (right : Ausdruckswert env (slot + 1) b) :
    Ausdruckswert env slot (.compare op a b) := by
  refine BewachterAusdruck.zweiOperandenWert left right (op.eval (a.wert env).wert (b.wert env).wert) ?_
  intro pre post frame position active typed checked entry
  rcases entry with ⟨first, second⟩
  simp only [TemporaryValue] at first second
  simp only [Befehl.auswerten, Rahmen.zahl, first, second, Option.bind_some, alsGanzzahl,
    bind, Option.bind, pure]

theorem textLiteral (decoded : List Char) : Ausdruckswert env slot (.textLiteral decoded) :=
  BewachterAusdruck.wert (TextValue.literal decoded) (fun _ _ _ _ _ _ _ _ => rfl)

private theorem text_readback (text : TextValue capacity) :
    wertAls (.text capacity) ⟨.text capacity, text⟩ = some text := by
  cases text with
  | mk bytes bound => simp only [wertAls, dif_pos bound]

theorem textConcat (left : Ausdruckswert env slot a) (right : Ausdruckswert env (slot + 1) b) :
    Ausdruckswert env slot (.textConcat a b) := by
  refine BewachterAusdruck.zweiOperandenWert left right ((a.wert env).concat (b.wert env)) ?_
  intro pre post frame position active typed checked entry
  rcases entry with ⟨first, second⟩
  simp only [TemporaryValue] at first second
  simp only [Befehl.auswerten, first, second, Option.bind_some, text_readback, bind, Option.bind, pure]

theorem textLength (operand : Ausdruckswert env slot tree) : Ausdruckswert env slot (.textLength tree) := by
  refine BewachterAusdruck.einOperand operand (tree.wert env).lengthValue ?_
  intro pre post frame position active typed checked entry
  simp only [TemporaryValue] at entry
  simp only [Befehl.auswerten, entry, Option.bind_some, text_readback, Option.map_some]

theorem textIndex (left : Ausdruckswert env slot base) (right : Ausdruckswert env (slot + 1) offset) :
    Ausdruckswert env slot (.textIndex base offset) := by
  refine BewachterAusdruck.zweiOperandenWert left right ((Expr.textIndex base offset).wert env) ?_
  intro pre post frame position active typed checked entry
  rcases entry with ⟨first, second⟩
  simp only [TemporaryValue] at first second
  let text := base.wert env
  let index := (offset.wert env).wert
  have guard : (Befehl.textIndex slot _).guard frame =
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
  simp only [Befehl.auswerten, Id.run, Rahmen.zahl, first, second, Option.bind_some, text_readback, alsGanzzahl,
    Expr.wert, ← index, ← text, if_neg nonnegative, read, Option.getD_some]

theorem optionIsSome (ref : Local scope (indexOptionType count)) (visible : ref.visible)
    (ordinary : ordinaryLocal ref.binding.name) : Ausdruckswert env slot (.optionIsSome ref visible ordinary) := by
  refine BewachterAusdruck.einOperand (variableRead (env := env) (slot := slot) ref visible ordinary)
    (indexOptionPresent (env ref)) ?_
  intro pre post frame position active typed checked entry
  simp only [TemporaryValue, Expr.wert] at entry
  simp only [Befehl.auswerten, entry, Option.bind_some, indexOptionType, wertAls, dif_pos rfl,
    bind, Option.bind, pure]

end ExpressionOperators

end Gabbro.Core.Ast.Semantik
