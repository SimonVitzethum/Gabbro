module

public import Core.Ast.Semantik.Runtime.ExpressionValues

@[expose] public section

namespace Gabbro.Core.Ast.Semantik

namespace ExpressionOperators

variable {scope : Scope} {env : Umgebung scope} {slot : Nat}

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
  rfl

theorem arithmetic (op : Arith) (left : Ausdruckswert env slot a) (right : Ausdruckswert env (slot + 1) b) :
    Ausdruckswert env slot (.binary op a b) := by
  refine BewachterAusdruck.zweiOperandenWert left right ((Expr.binary op a b).wert env) ?_
  intro pre post frame position active typed checked entry
  rcases entry with ⟨first, second⟩
  simp only [TemporaryValue] at first second
  simp only [Expr.wert, Befehl.auswerten, Rahmen.zahl, first, second, Option.bind_some, alsGanzzahl,
    bind, Option.bind, pure, Ganzzahl.pack]
  rfl

theorem divide (left : Ausdruckswert env slot a) (right : Ausdruckswert env (slot + 1) (b : Expr scope (.int lo hi)))
    (nonzero : Divisor lo hi) : Ausdruckswert env slot (.div a b nonzero) := by
  refine BewachterAusdruck.zweiOperandenWert left right ((Expr.div a b nonzero).wert env) ?_
  intro pre post frame position active typed checked entry
  rcases entry with ⟨first, second⟩
  simp only [TemporaryValue] at first second
  have admitted : 1 ≤ lo ∨ hi ≤ -1 := nonzero
  simp only [Expr.wert, Befehl.auswerten, Rahmen.zahl, first, second, Option.bind_some, alsGanzzahl,
    bind, Option.bind, pure, dif_pos admitted]

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
  simp only [Expr.wert, Befehl.auswerten, first, second, Option.bind_some, text_readback (a.wert env),
    text_readback (b.wert env), bind, Option.bind, pure]

theorem textLength (operand : Ausdruckswert env slot tree) : Ausdruckswert env slot (.textLength tree) := by
  refine BewachterAusdruck.einOperand operand ((Expr.textLength tree).wert env) ?_
  intro pre post frame position active typed checked entry
  simp only [TemporaryValue] at entry
  simp only [Expr.wert, Befehl.auswerten, entry, Option.bind_some, text_readback (tree.wert env), Option.map_some]
  rfl

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
    simp only [Befehl.guard, Rahmen.zahl, first, second, Option.bind_some, text_readback (base.wert env), alsGanzzahl,
      bind, Option.bind, pure, index, text]
  have allowed := guardOfInstruction position active checked guard
  change (if index < 0 then text.bytes.size else index.toNat) < text.bytes.size at allowed
  have nonnegative : ¬ index < 0 := by
    intro negative
    simp only [if_pos negative, Nat.lt_irrefl] at allowed
  have fits : index.toNat < text.bytes.size := by simpa only [if_neg nonnegative] using allowed
  have read : text.bytes[index.toNat]? = some (text.bytes[index.toNat]'fits) := getElem?_pos text.bytes index.toNat fits
  simp only [Expr.wert, Befehl.auswerten, Id.run, Rahmen.zahl, first, second, Option.bind_some, text_readback, alsGanzzahl,
    Expr.wert, ← index, ← text, if_neg nonnegative, read, Option.getD_some]

theorem optionIsSome (ref : Local scope (indexOptionType count)) (visible : ref.visible)
    (ordinary : ordinaryLocal ref.binding.name) : Ausdruckswert env slot (.optionIsSome ref visible ordinary) := by
  refine BewachterAusdruck.einOperand (variableRead (env := env) (slot := slot) ref visible ordinary)
    ((Expr.optionIsSome ref visible ordinary).wert env) ?_
  intro pre post frame position active typed checked entry
  simp only [TemporaryValue, Expr.wert] at entry
  simp only [Expr.wert, Befehl.auswerten, entry, Option.bind_some, indexOptionType, wertAls, dif_pos rfl,
    bind, Option.bind, pure, dif_pos trivial]

theorem substring
    (baseRead : Ausdruckswert env slot (base : Expr scope (.text capacity)))
    (firstRead : Ausdruckswert env (slot + 1) first)
    (lastRead : Ausdruckswert env (slot + 2) last) :
    Ausdruckswert env slot (.substring base first last) := by
  let left := (expr slot base).code ++ (expr (slot + 1) first).code
  let middle := (expr (slot + 2) last).code
  let observedBase := TemporaryValue slot (base.wert env)
  let observedFirst := TemporaryValue (slot + 1) (first.wert env)
  let observedLast := TemporaryValue (slot + 2) (last.wert env)
  have operands : BewachterAusdruck env slot (left ++ middle) (fun _ => True)
      (fun frame => observedBase frame ∧ observedFirst frame ∧ observedLast frame) := by
    refine .anhaengen (.zweiOperanden baseRead firstRead) (lastRead.eingang (fun _ _ => trivial)) (by omega) ?_
    intro middle out values final preserve
    exact ⟨(preserve slot (by omega)).trans values.1,
      (preserve (slot + 1) (by omega)).trans values.2, final⟩
  refine BewachterAusdruck.anhaengen operands
    (BewachterAusdruck.wert ((Expr.substring base first last).wert env) ?_) (Nat.le_refl _) (fun _ _ _ found _ => found)
  intro pre post frame position active typed checked entry
  rcases entry with ⟨baseValue, firstValue, lastValue⟩
  simp only [observedBase, observedFirst, observedLast, TemporaryValue] at baseValue firstValue lastValue
  let text := base.wert env
  let lower := (first.wert env).wert
  let upper := (last.wert env).wert
  have guard : (Befehl.substring slot capacity).guard frame =
      some ⟨.teilfolge, (lower, upper, text.bytes.size)⟩ := by
    simp only [Befehl.guard, Rahmen.zahl, baseValue, firstValue, lastValue, Option.bind_some,
      text_readback (base.wert env), alsGanzzahl, bind, Option.bind, pure, lower, upper, text]
  have allowed := guardOfInstruction position active checked guard
  change 0 ≤ lower ∧ lower ≤ upper ∧ upper ≤ (text.bytes.size : Int) at allowed
  dsimp only [lower, upper, text] at allowed
  simp only [Befehl.auswerten, Id.run, Rahmen.zahl, baseValue, firstValue, lastValue,
    Option.bind_some, text_readback (base.wert env), alsGanzzahl, Expr.wert, if_pos allowed]
  rfl

theorem logic (op : Logic) (leftRead : Ausdruckswert env slot left) (rightRead : Ausdruckswert env slot right) :
    Ausdruckswert env slot (.logic op left right) := by
  intro pre post frame position active typed checked _
  let lhs := (expr slot left).code
  let rhs := (expr slot right).code
  let branch := Befehl.springeWenn slot op.skips (rhs.length + 1)
  let full := pre ++ (lhs ++ [branch] ++ rhs) ++ post
  have checkedLeft : frame.WaechterHalten (pre ++ lhs ++ (branch :: rhs ++ post)) := by
    simpa only [expr, Fragment.anhaengen, Fragment.einzel, lhs, rhs, branch, List.append_assoc,
      List.singleton_append] using checked
  obtain ⟨middle, lhsTrace, value⟩ := leftRead pre (branch :: rhs ++ post)
    frame position active typed checkedLeft trivial
  have lhsFull : Ausdrucksabschnitt full (pre.length + lhs.length) slot frame middle := by
    simpa only [full, lhs, List.append_assoc, List.singleton_append] using lhsTrace
  have branchLookup : full[middle.pc]? = some branch := by
    have atBranch : middle.pc = (pre ++ lhs).length := by simpa only [List.length_append, lhs] using lhsTrace.position
    simpa only [full, List.append_assoc] using
      (codeLookup_instruction (pre := pre ++ lhs) (post := rhs ++ post) (instruction := branch) atBranch)
  let afterBranch := branch.auswerten middle
  have valueAtSlot : middle.temp slot = some ⟨.bool, left.wert env⟩ := value
  let bit : Bool := left.wert env
  have branchShape : afterBranch =
      { middle with pc := middle.pc + (if bit = op.skips then rhs.length + 1 else 1) } := by
    simp only [afterBranch, branch, Befehl.auswerten, valueAtSlot, Option.bind_some, alsBoolean]
    change { middle with pc := middle.pc + (if some bit = some op.skips then rhs.length + 1 else 1) } = _
    rw [Option.some.injEq]
  have midActive := lhsFull.aktiv active
  have branchStep : Rahmen.Schritt full middle afterBranch :=
    ⟨branch, midActive.1, midActive.2, branchLookup, rfl⟩
  have branchSame : afterBranch = { middle with pc := afterBranch.pc, temp := afterBranch.temp } := by
    rw [branchShape]
  have preserves : ∀ i, afterBranch.temp i = middle.temp i := fun i => congrArg (fun f : Rahmen => f.temp i) branchShape
  by_cases taken : bit = op.skips
  · have atEnd : afterBranch.pc = pre.length + (lhs ++ [branch] ++ rhs).length := by
      simp only [branchShape, if_pos taken, List.length_append, List.length_cons, List.length_nil, lhsFull.position]
      omega
    have branchTrace : Ausdrucksabschnitt full _ slot middle afterBranch :=
      ⟨.schritt .start branchStep, atEnd, branchSame, fun i _ => preserves i⟩
    have trace := lhsFull.trans branchTrace (Nat.le_refl _)
    refine ⟨afterBranch, ?_, ?_⟩
    · simpa only [full, lhs, rhs, branch, expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc] using trace
    · change TemporaryValue (type := .bool) slot (if bit = op.skips then bit else right.wert env) afterBranch
      rw [if_pos taken]
      exact (preserves slot).trans valueAtSlot
  · have afterPC : afterBranch.pc = (pre ++ lhs ++ [branch]).length := by
      simp only [branchShape, if_neg taken, List.length_append, List.length_cons, List.length_nil, lhsFull.position]
    have branchTrace : Ausdrucksabschnitt full _ slot middle afterBranch :=
      ⟨.schritt .start branchStep, afterPC, branchSame, fun i _ => preserves i⟩
    have prefixTrace : Ausdrucksabschnitt full _ slot frame afterBranch :=
      lhsFull.trans branchTrace (Nat.le_refl _)
    have checkedRight : afterBranch.WaechterHalten ((pre ++ lhs ++ [branch]) ++ rhs ++ post) := by
      have checkedFull : frame.WaechterHalten full := by
        simpa only [full, lhs, rhs, branch, expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc] using checked
      simpa only [full, List.append_assoc] using checkedFull.after prefixTrace.walk
    obtain ⟨out, rhsTrace, result⟩ := rightRead (pre ++ lhs ++ [branch]) post afterBranch afterPC
      (prefixTrace.aktiv active) (prefixTrace.traegt typed) checkedRight trivial
    have rhsFull : Ausdrucksabschnitt full (pre.length + (lhs ++ [branch] ++ rhs).length) slot afterBranch out := by
      simpa only [full, rhs, List.append_assoc, List.length_append, Nat.add_assoc] using rhsTrace
    refine ⟨out, ?_, ?_⟩
    · simpa only [full, lhs, rhs, branch, expr, Fragment.anhaengen, Fragment.einzel, List.append_assoc] using
        prefixTrace.trans rhsFull (Nat.le_refl _)
    · change TemporaryValue (type := .bool) slot (if bit = op.skips then bit else right.wert env) out
      rw [if_neg taken]
      exact result

end ExpressionOperators

end Gabbro.Core.Ast.Semantik
