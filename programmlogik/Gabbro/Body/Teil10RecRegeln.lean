module

public import Gabbro.Body.Teil3

@[expose] public section

namespace Gabbro.Body

/-- Construction evaluates every field in declaration order using the same traversal as
    argument lists. Any failed field makes the whole construction stuck. -/
@[simp] theorem eval_recOf (s : State) (args : List Expr) :
    eval s (.recOf args) = (evalAll s args).map Value.record := by
  rw [eval]
  cases evalAll s args <;> rfl

/-- Projection has no default: `getElem?` returns `none` exactly outside the record. -/
@[simp] theorem eval_recGet (s : State) (base : Expr) (vs : List Value) (idx : Nat)
    (hb : eval s base = some (.record vs)) :
    eval s (.recGet base idx) = vs[idx]? := by
  rw [eval, hb]

/-- The explicit bound is the bridge's position obligation; replacement keeps arity. -/
@[simp] theorem eval_recSet (s : State) (base val : Expr) (vs : List Value) (v : Value)
    (idx : Nat) (hb : eval s base = some (.record vs)) (hv : eval s val = some v)
    (hi : idx < vs.length) :
    eval s (.recSet base idx val) = some (.record (vs.set idx v)) := by
  simp only [eval, hb, hi, hv, ↓reduceIte]

@[simp] theorem eval_recGet_oob (s : State) (base : Expr) (vs : List Value) (idx : Nat)
    (hb : eval s base = some (.record vs)) (hi : vs.length ≤ idx) :
    eval s (.recGet base idx) = none := by
  rw [eval_recGet s base vs idx hb]
  exact List.getElem?_eq_none hi

@[simp] theorem eval_recSet_oob (s : State) (base val : Expr) (vs : List Value) (idx : Nat)
    (hb : eval s base = some (.record vs)) (hi : vs.length ≤ idx) :
    eval s (.recSet base idx val) = none := by
  have hn : ¬ idx < vs.length := by omega
  simp only [eval, hb, hn, ↓reduceIte]

/-- Reading the changed field yields precisely the replacement. -/
@[simp] theorem recGet_after_recSet (s : State) (base val : Expr)
    (vs : List Value) (v : Value) (idx : Nat)
    (hb : eval s base = some (.record vs)) (hv : eval s val = some v)
    (hi : idx < vs.length) :
    eval s (.recGet (.recSet base idx val) idx) = some v := by
  rw [eval_recGet s (.recSet base idx val) (vs.set idx v) idx
    (eval_recSet s base val vs v idx hb hv hi)]
  exact List.getElem?_set_self hi

/-- Distinct positions are a frame, including an out-of-range read which stays stuck. -/
@[simp] theorem recGet_frame (s : State) (base val : Expr)
    (vs : List Value) (v : Value) (idx other : Nat)
    (hb : eval s base = some (.record vs)) (hv : eval s val = some v)
    (hi : idx < vs.length) (hne : idx ≠ other) :
    eval s (.recGet (.recSet base idx val) other) = eval s (.recGet base other) := by
  rw [eval_recGet s (.recSet base idx val) (vs.set idx v) other
    (eval_recSet s base val vs v idx hb hv hi),
    eval_recGet s base vs other hb]
  exact List.getElem?_set_ne hne

/-- Repeating a replacement at the same position has no further effect. -/
@[simp] theorem recSet_idempotent (s : State) (base val : Expr)
    (vs : List Value) (v : Value) (idx : Nat)
    (hb : eval s base = some (.record vs)) (hv : eval s val = some v)
    (hi : idx < vs.length) :
    eval s (.recSet (.recSet base idx val) idx val) = eval s (.recSet base idx val) := by
  have hs := eval_recSet s base val vs v idx hb hv hi
  have hi' : idx < (vs.set idx v).length := by simpa only [List.length_set] using hi
  rw [eval_recSet s (.recSet base idx val) val (vs.set idx v) v idx hs hv hi', hs]
  rw [List.set_set]

/-- Writing back a projected field gives the original record. The bound ensures the
    projection succeeds; the equation is not extended to an invalid access. -/
@[simp] theorem recSet_recGet (s : State) (base : Expr) (vs : List Value) (idx : Nat)
    (hb : eval s base = some (.record vs)) (hi : idx < vs.length) :
    eval s (.recSet base idx (.recGet base idx)) = eval s base := by
  have hg : eval s (.recGet base idx) = some vs[idx] := by
    rw [eval_recGet s base vs idx hb]
    exact List.getElem?_eq_getElem hi
  rw [eval_recSet s base (.recGet base idx) vs vs[idx] idx hb hg hi, hb,
    List.set_getElem_self hi]

/-- Ordered records are extensionally equal when every positional projection agrees.
    Out-of-range projections are included, so different arities cannot be identified. -/
theorem Value.record_ext (vs ws : List Value) (h : ∀ idx : Nat, vs[idx]? = ws[idx]?) :
    Value.record vs = Value.record ws :=
  congrArg Value.record (List.ext_getElem? h)

/-- Extensionality for two successfully evaluated record expressions. -/
theorem rec_ext (s : State) (left right : Expr) (vs ws : List Value)
    (hl : eval s left = some (.record vs)) (hr : eval s right = some (.record ws))
    (h : ∀ idx, eval s (.recGet left idx) = eval s (.recGet right idx)) :
    eval s left = eval s right := by
  have hp : ∀ idx : Nat, vs[idx]? = ws[idx]? := by
    intro idx
    simpa only [eval_recGet s left vs idx hl, eval_recGet s right ws idx hr] using h idx
  rw [hl, hr, Value.record_ext vs ws hp]

/-- Pointwise shape checking is preserved when a field receives its declared shape. -/
theorem Value.fieldsHaveShape_set (vs : List Value) (ss : List Shape) (idx : Nat)
    (sh : Shape) (v : Value) (h : Value.fieldsHaveShape vs ss = true)
    (hsh : ss[idx]? = some sh) (hv : v.hasShape sh = true) :
    Value.fieldsHaveShape (vs.set idx v) ss = true := by
  induction vs generalizing ss idx with
  | nil =>
      cases ss with
      | nil => simp at hsh
      | cons s ss => simp only [Value.fieldsHaveShape_nil_cons, Bool.false_eq_true] at h
  | cons a vs ih =>
      cases ss with
      | nil => simp only [Value.fieldsHaveShape_cons_nil, Bool.false_eq_true] at h
      | cons s ss =>
          have hh := Bool.and_eq_true_iff.mp h
          cases idx with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hsh
              subst s
              simpa only [List.set_cons_zero, Value.fieldsHaveShape_cons_cons,
                hv, Bool.true_and] using hh.2
          | succ idx =>
              simp only [List.getElem?_cons_succ] at hsh
              simpa only [List.set_cons_succ, Value.fieldsHaveShape_cons_cons,
                Bool.and_eq_true_iff] using And.intro hh.1 (ih ss idx hh.2 hsh)

/-- Record replacement preserves the whole shape when the new field fits its position. -/
theorem Value.hasShape_rec_set (vs : List Value) (ss : List Shape) (idx : Nat)
    (sh : Shape) (v : Value) (h : (Value.record vs).hasShape (.record ss) = true)
    (hsh : ss[idx]? = some sh) (hv : v.hasShape sh = true) :
    (Value.record (vs.set idx v)).hasShape (.record ss) = true := by
  have hh := Bool.and_eq_true_iff.mp h
  have hf := Value.fieldsHaveShape_set vs ss idx sh v hh.2 hsh hv
  simpa only [Value.hasShape_record_record, List.length_set, hf, Bool.and_true] using hh.1

/-- A local's record shape opens into its ordered values and their shape witnesses. -/
theorem shape_rec (s : State) (n : String) (ss : List Shape)
    (h : eval s (.hasShape n (.record ss)) = some (.bool true)) :
    ∃ vs, s.local' n = .record vs ∧ vs.length = ss.length ∧ Value.fieldsHaveShape vs ss = true :=
  Value.hasShape_rec_true _ ss ((eval_hasShape_true_iff s n (.record ss)).mp h)

/-- A record-typed world read has an ordered, equally long, pointwise shaped field list. -/
theorem WF_rec (Γ : Typing) (σ : World) (p : Place) (ss : List Shape) (h : WF Γ σ)
    (hp : Γ p = some (.record ss)) :
    ∃ vs, σ p = .record vs ∧ vs.length = ss.length ∧ Value.fieldsHaveShape vs ss = true :=
  Value.hasShape_rec_true _ ss (h p (.record ss) hp)

/-- Read the complete record-shape fact without choosing its field-list witness. -/
theorem WF_read_rec (Γ : Typing) (σ : World) (p : Place) (ss : List Shape) (h : WF Γ σ)
    (hp : Γ p = some (.record ss)) : (σ p).hasShape (.record ss) = true :=
  h p (.record ss) hp

/-- Storing an equally long, pointwise shaped record preserves world typing. -/
theorem WF_store_rec (Γ : Typing) (σ : World) (p : Place) (ss : List Shape)
    (vs : List Value) (h : WF Γ σ) (hp : Γ p = some (.record ss))
    (hlen : vs.length = ss.length) (hv : Value.fieldsHaveShape vs ss = true) :
    WF Γ (store σ p (.record vs)) := by
  apply WF_store Γ σ p (.record vs) h
  intro sh hsh
  rw [hp] at hsh
  cases hsh
  simp [hlen, hv]

end Gabbro.Body
