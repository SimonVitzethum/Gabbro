module

public import Core.Ast.Aggregate.TupleBindings
public import Core.Ast.Semantik.Formbeweise

/-!
# Prover checklist

## TupleBind

- `Surface.TupleBindInversionAussage`
- `Surface.TupleBindSuffixAussage`
- `Surface.TupleBindDerivationAussage`
- `TupleBindParseAussage`
- `TupleBindElaboriertAussage`
- `TupleBindRealisiertAussage`
- `TupleBindAnnahmeAussage`
- `TupleBindIdealAussage`
- `TupleBindEinheitAussage`
- `TupleBindImplAussage`
- `TupleBindErhaltungAussage`
- `TupleBindRegelSicherAussage`
- `TupleBindErfuellbarAmAussage`
- `TupleBindLocalsAussage`
-/

namespace Gabbro.Core.Ast.Semantik

open Maschine Katalog Waechter

theorem tupleBind_am_ort (ctx : Scope × Option (Ty .value)) : (tupleBindForm ctx).RegelAmOrt := by
  intro args
  change (((expr 0 args.value).anhaengen (.einzel
    (.bindeTupel 0 args.types (args.pattern.names.map Option.isSome)))).code[
      (expr 0 args.value).code.length]? =
    some (.bindeTupel 0 args.types (args.pattern.names.map Option.isSome)))
  simp only [Fragment.anhaengen, Fragment.einzel, List.getElem?_append_right (Nat.le_refl _),
    Nat.sub_self, List.getElem?_cons_zero]

theorem tupleBind_elaboriert : TupleBindElaboriertAussage := by
  intro ctx platform args
  rfl

theorem tupleBind_realisiert : TupleBindRealisiertAussage := by
  intro ctx platform args s running active live atPc
  exact (tupleBindForm ctx).realisiert (tupleBind_am_ort ctx) platform args s
    running active live atPc

theorem tupleBind_annahme : TupleBindAnnahmeAussage := by
  intro ctx
  exact (tupleBindForm ctx).annahme

theorem tupleBind_ideal : TupleBindIdealAussage := by
  intro ctx
  refine ⟨tupleBind_am_ort ctx, ?_⟩
  intro args
  exact ⟨((tupleBindForm ctx).befehl args).bestimmt, fun _ _ _ _ _ => Iff.rfl⟩

theorem tupleBind_einheit : TupleBindEinheitAussage := by
  intro ctx platform args
  exact ⟨rfl, ((tupleBindForm ctx).befehl args).kommutation⟩

theorem tupleBind_impl : TupleBindImplAussage := by
  intro ctx args c s w plans u
  rfl

private theorem tupleBind_keineInvarianten (ctx : Scope × Option (Ty .value))
    (args : Surface.TupleBindArgs ctx.1) :
    ((tupleBindForm ctx).fragment args).klauseln.invariant = [] := by
  change (stmt (Stmt.tupleBind args.pattern args.annotation args.checked args.value)).klauseln.invariant = []
  exact stmt_keine_invarianten _

theorem tupleBind_erhaltung : TupleBindErhaltungAussage := by
  intro ctx
  exact (tupleBindForm ctx).erhaltung (tupleBind_keineInvarianten ctx)

theorem tupleBind_regelSicher : TupleBindRegelSicherAussage := by
  intro ctx platform args
  exact ((tupleBindForm ctx).befehl args).sicher ((tupleBindForm ctx).fragment args)
    platform (tupleBind_keineInvarianten ctx args)

private theorem tupleLocals_length : (types : List (Ty .value)) → (value : Wert (tupleType types)) →
    (names : List (Option Identifier)) → names.length = types.length →
    (tupleLocals types value (names.map Option.isSome)).length =
      ((names.zip types).filterMap fun (name, _) => name).length
  | [], _, [], _ => rfl
  | _ :: _, _, [], h => by cases h
  | [], _, _ :: _, h => by cases h
  | t :: ts, (head, tail), name :: names, h => by
      cases name with
      | none =>
          simpa [tupleLocals] using (tupleLocals_length ts tail names (by simpa using h))
      | some id =>
          simpa [tupleLocals] using (tupleLocals_length ts tail names (by simpa using h))

theorem tupleBind_locals : TupleBindLocalsAussage := by
  intro ctx args frame value temp
  have got : wertAls (tupleType args.types) ⟨tupleType args.types, value⟩ = some value := by
    change (if same : tupleType args.types = tupleType args.types then some (same ▸ value) else none) = some value
    rw [dif_pos rfl]
  simp only [tupleBindForm, Quellform.befehl, Befehl.auswerten]
  rw [temp]
  simp only [Option.bind_some]
  rw [got]
  simp only [Option.map_some, Option.getD_some]
  have hlen : (args.pattern.bindings args.types).length =
      ((args.pattern.names.zip args.types).filterMap fun (name, _) => name).length := by
    simp only [TuplePattern.bindings, List.length_reverse]
    let z := args.pattern.names.zip args.types
    change (z.filterMap (fun x => Option.map (fun id => (⟨id, x.2, false, false⟩ : Binding)) x.1)).length =
      (z.filterMap fun x => x.1).length
    induction z with
    | nil => rfl
    | cons x xs ih =>
        cases hx : x.1 with
        | none => simpa [hx] using ih
        | some id => simpa [hx] using congrArg Nat.succ ih
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_reverse]
    rw [hlen]
    rw [tupleLocals_length args.types value args.pattern.names args.checked.1]
  · trivial
  · trivial

end Gabbro.Core.Ast.Semantik
