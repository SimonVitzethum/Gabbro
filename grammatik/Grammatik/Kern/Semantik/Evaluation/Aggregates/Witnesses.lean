module

public import Grammatik.Kern.Semantik.Evaluation.Aggregates.Locals
public import Grammatik.Kern.Semantik.Semantik.PayloadProben

@[expose] public section

namespace Gabbro.Grammatik.AggregateValues

/-! Small kernel-computation witnesses. Reuse the existing declaration, world,
and oracle from the typed-payload fixture; no parser or external execution is
needed. The two equal bindings below are deliberately both observable. -/

abbrev D := TypedPayload.D
abbrev V := TypedPayload.V

def array : Wert D (.arr .bool 2) := fun j => if j.val = 0 then false else true

def record : Wert D (.prod 7 [.bool, .bool]) := (false, (true, ()))

def text : Wert D (.str 4) :=
  ⟨[⟨65, by decide, by decide⟩, ⟨66, by decide, by decide⟩], by decide⟩

def tagged : Wert D (.sum [some (.prod 7 [.bool, .bool]), none]) :=
  ⟨⟨0, by decide⟩, record⟩

/-- All array-update premises hold jointly, with a replacement that changes the
first element and a second element that remains observable. -/
theorem arrSetW_characterization_zeuge :
    arrSetW array ⟨0, by decide⟩ true ⟨0, by decide⟩ = true ∧
    (∀ j, j ≠ (⟨0, by decide⟩ : Fin 2) →
      arrSetW array ⟨0, by decide⟩ true j = array j) ∧
    array ⟨0, by decide⟩ = false := by
  have h := (arrSetW_characterization array (arrSetW array ⟨0, by decide⟩ true)
    ⟨0, by decide⟩ true).mp rfl
  exact ⟨h.1, h.2, rfl⟩

theorem arrSetW_read_zeuge : arrSetW array ⟨0, by decide⟩ false = array :=
  arrSetW_read array ⟨0, by decide⟩

theorem arrSetW_overwrite_zeuge :
    arrSetW (arrSetW array ⟨0, by decide⟩ true) ⟨0, by decide⟩ false = array := by
  exact (arrSetW_overwrite array ⟨0, by decide⟩ true false).trans arrSetW_read_zeuge

/-- The same changed-field and sibling observations for a concrete record. -/
theorem prodSetW_overwrite_zeuge :
    prodSetW (F := D.Fn) (passt := D.passt) (FieldAt.head : FieldAt [.bool, .bool] .bool)
        (prodSetW (F := D.Fn) (passt := D.passt) FieldAt.head record true) false = record ∧
    prodGetW (F := D.Fn) (passt := D.passt) (FieldAt.tail FieldAt.head)
      (prodSetW (F := D.Fn) (passt := D.passt) FieldAt.head record true) = true :=
  ⟨rfl, rfl⟩

/-- Updating one of two equal record bindings keeps the other record unchanged.
An implementation that blindly overwrote shared backing storage would fail this
observable result: the updated first field is true, the other binding's is false. -/
theorem record_binding_isolation_zeuge :
    let ρ : Env D [.prod 7 [.bool, .bool], .prod 7 [.bool, .bool]] :=
      .cons record (.cons record .nil)
    let η := ρ.set .here (prodSetW (F := D.Fn) (passt := D.passt) FieldAt.head record true)
    prodGetW (F := D.Fn) (passt := D.passt) FieldAt.head (η.get .here) = true ∧
      prodGetW (F := D.Fn) (passt := D.passt) FieldAt.head (η.get (.there .here)) = false :=
  ⟨rfl, rfl⟩

/-- The general distinct-position premise is inhabited, even for equal values. -/
theorem get_set_other_zeuge :
    let ρ : Env D [.prod 7 [.bool, .bool], .prod 7 [.bool, .bool]] :=
      .cons record (.cons record .nil)
    (ρ.set .here (prodSetW (F := D.Fn) (passt := D.passt) FieldAt.head record true)).get
      (.there .here) = record := by
  exact Env.get_set_other _ .here (.there .here) _ (by decide)

theorem array_binding_isolation_zeuge :
    let ρ : Env D [.arr .bool 2, .arr .bool 2] := .cons array (.cons array .nil)
    let η := ρ.set .here (arrSetW array ⟨0, by decide⟩ true)
    (η.get .here) ⟨0, by decide⟩ = true ∧
      (η.get (.there .here)) ⟨0, by decide⟩ = false := ⟨rfl, rfl⟩

/-- Rebinding a string or tagged aggregate likewise leaves its copied binding. -/
theorem string_binding_isolation_zeuge :
    let ρ : Env D [.str 4, .str 4] := .cons text (.cons text .nil)
    let η := ρ.set .here (strWeitW 4 (strWeitW 1 text))
    (η.get .here).1.length = 1 ∧ (η.get (.there .here)).1.length = 2 := ⟨rfl, rfl⟩

theorem tagged_binding_isolation_zeuge :
    let ρ : Env D [.sum [some (.prod 7 [.bool, .bool]), none],
      .sum [some (.prod 7 [.bool, .bool]), none]] := .cons tagged (.cons tagged .nil)
    let η := ρ.set .here ⟨⟨1, by decide⟩, ()⟩
    (η.get .here).1.val = 1 ∧ (η.get (.there .here)).1.val = 0 := ⟨rfl, rfl⟩

/-- A nonempty prefix, and an in-bound access beyond its actual length (zero).
The source also has a later, different byte, so truncation is observable. -/
theorem strGetW_strWeitW_zeuge :
    (strGetW (strWeitW 1 text) 0).n = 65 ∧
    (strGetW (strWeitW 4 text) 3).n = 0 ∧
    (strGetW text 1).n = 66 := ⟨rfl, rfl, rfl⟩

theorem strWeitW_bytes_of_le_zeuge : (strWeitW 8 text).1 = text.1 := rfl

/-- The pointwise premise is inhabited on a heterogeneous aggregate context. -/
theorem value_ext_zeuge :
    let ρ : Env D [.prod 7 [.bool, .bool], .arr .bool 2, .str 4,
      .sum [some (.prod 7 [.bool, .bool]), none]] :=
      .cons record (.cons array (.cons text (.cons tagged .nil)))
    ∃ η : Env D [.prod 7 [.bool, .bool], .arr .bool 2, .str 4,
      .sum [some (.prod 7 [.bool, .bool]), none]],
      (∀ {τ : Ty} (x : Var _ τ), ρ.get x = η.get x) ∧ ρ = η := by
  exact ⟨_, (fun _ => rfl), rfl⟩

/-- Actual G assignment of an array replacement, with a still-live equal copy. -/
theorem execStmt_assignArray_zeuge :
    execStmt TypedPayload.oracle 0 (fun f _ _ => .logik (.abstieg f))
      (Stmt.assignVar (V := V) (l := false) (Λ := [])
        (Var.here : Var [.arr .bool 2, .arr .bool 2] (.arr .bool 2))
        (.arrSet (.var .here) (.widen (by decide) (by decide) (.lit 0)) .tru))
      TypedPayload.world (.cons array (.cons array .nil)) =
      .ok TypedPayload.world (.cons (arrSetW array ⟨0, by decide⟩ true) (.cons array .nil)) := rfl

/-- The canonical parameter context admits assignment: no immutability premise
may be silently inferred from parameter binding in the current model. -/
theorem parameter_assignment_zeuge :
    execStmt TypedPayload.oracle 0 (fun f _ _ => .logik (.abstieg f))
      (Stmt.assignVar (V := V) (l := false) (Λ := [])
        (Var.here : Var (D.params ()) (.sum TypedPayload.schema))
        (.case TypedPayload.schema ⟨0, by decide⟩ (.val .tru)))
      TypedPayload.world (.cons (eval TypedPayload.world TypedPayload.array TypedPayload.world .nil) .nil) =
      .ok TypedPayload.world (.cons ⟨⟨0, by decide⟩, true⟩ .nil) := rfl

/-- A complete callee overwrites its aggregate parameter before returning it. -/
def overwriteParameter : Programm D :=
  { requires := fun _ => .tru
    ensures := fun _ => .tru
    invariante := fun i => nomatch i
    rumpf := fun _ => .cons
      (.assignVar .here (.case TypedPayload.schema ⟨0, by decide⟩ (.val .tru)))
      (.ret (.val (.var .here)) (List.Perm.refl [])) }

theorem parameter_call_zeuge :
    rufAt overwriteParameter TypedPayload.oracle 0 1 () TypedPayload.world
      (.cons (eval TypedPayload.world TypedPayload.array TypedPayload.world .nil) .nil) =
      .ok TypedPayload.world ⟨⟨0, by decide⟩, true⟩ := rfl

/-- All call-permission premises hold for the parameter-overwriting callee. -/
theorem callFits : RufPasst D V (D.signatur ()) [] where
  hw := fun _ h => nomatch h
  hg := fun g => nomatch g
  hk := ⟨[], List.Perm.refl [], by simp only [List.Sublist.refl]⟩
  hh := fun L => nomatch L

/-- The callee changes its parameter and returns a different tagged value, yet
the complete call step keeps the caller's array payload under its original tag. -/
theorem execStmt_call_preserves_caller_zeuge :
    let ρ : Env D [.sum TypedPayload.schema] :=
      .cons (eval TypedPayload.world TypedPayload.array TypedPayload.world .nil) .nil
    execStmt TypedPayload.oracle 0 (rufAt overwriteParameter TypedPayload.oracle 0 1)
      (Stmt.call (V := V) (l := false) () (.cons (.var .here) .nil) callFits rfl)
      TypedPayload.world ρ = .ok TypedPayload.world ρ := rfl

end Gabbro.Grammatik.AggregateValues
