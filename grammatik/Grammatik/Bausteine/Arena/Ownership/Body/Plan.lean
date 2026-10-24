import Grammatik.Bausteine.Arena.Ownership.Body.Handoff

/-! The source side of argument handoff. A call's plan lists, per parameter
at its bottom position, the interface's passing mode and the caller origin
of the actual argument expression. The check is a finite test over the
positions: every passed argument has a caller right of its mode, an owned
origin is passed exactly once and never also lent. The caller keeps its
context with every owned origin consumed. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration}

/-! ## 1. Positions -/

/-- The modes in bottom order (position `0` is the outermost parameter). -/
def modeList : {params : Ctx} → Modes params → List (Option PassingMode)
  | _, .nil => []
  | _, .cons mode rest => modeList rest ++ [mode]

/-- The mode of one parameter. -/
def modeAt : {params : Ctx} → Modes params → {τ : Ty} → Var params τ → Option PassingMode
  | _, .cons mode _, _, .here => mode
  | _, .cons _ rest, _, .there x => modeAt rest x

/-- The caller origins of the arguments, in bottom order. -/
def originList (c : Context) {Γ : Ctx} {Λ : List (Res D)} :
    {params : Ctx} → Args D Γ Λ params → List (Option Nat)
  | _, .nil => []
  | _, .cons e rest => originList c rest ++ [origin c e]

theorem modeList_length : ∀ {params : Ctx} (modes : Modes params), (modeList modes).length = params.length
  | _, .nil => rfl
  | _, .cons _ rest => by simp [modeList, modeList_length rest]

theorem originList_length (c : Context) {Γ : Ctx} {Λ : List (Res D)} :
    ∀ {params : Ctx} (args : Args D Γ Λ params), (originList c args).length = params.length
  | _, .nil => rfl
  | _, .cons _ rest => by simp [originList, originList_length c rest]

theorem modeList_at : ∀ {params : Ctx} (modes : Modes params) {τ : Ty} (x : Var params τ),
    (modeList modes)[x.unten]? = some (modeAt modes x)
  | _ :: rest, .cons mode modes, _, .here => by
    simp [modeList, modeAt, Var.unten, List.getElem?_append_right, modeList_length modes]
  | _ :: rest, .cons mode modes, _, .there x => by
    have hx : x.unten < (modeList modes).length := by rw [modeList_length]; exact Var.unten_lt x
    simp only [modeList, modeAt, Var.unten, List.getElem?_append_left hx]
    exact modeList_at modes x

theorem originList_at (c : Context) {Γ : Ctx} {Λ : List (Res D)} :
    ∀ {params : Ctx} (args : Args D Γ Λ params) {τ : Ty} (x : Var params τ),
      (originList c args)[x.unten]? = some (origin c (argument args x))
  | _ :: rest, .cons e args, _, .here => by
    simp [originList, argument, Var.unten, List.getElem?_append_right, originList_length c args]
  | _ :: rest, .cons e args, _, .there x => by
    have hx : x.unten < (originList c args).length := by rw [originList_length]; exact Var.unten_lt x
    simp only [originList, argument, Var.unten, List.getElem?_append_left hx]
    exact originList_at c args x

/-! ## 2. The parameter context by position -/

theorem parameterContext_references : ∀ {params : Ctx} (modes : Modes params) (u : Nat),
    (Flow.parameterContext modes).references[u]? =
      ((modeList modes)[u]?).map (fun m => m.map fun _ => u)
  | _, .nil, u => by simp [Flow.parameterContext, Context.empty, modeList]
  | _ :: rest, .cons mode modes, u => by
    have hl := (parameterContext_length modes)
    have hm := modeList_length modes
    simp only [Flow.parameterContext, modeList]
    by_cases hu : u < rest.length
    · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      exact parameterContext_references modes u
    · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
      by_cases he : u = rest.length
      · subst he; simp [hl.1, hl.2, hm]
      · have h1 : u - (Flow.parameterContext modes).references.length ≠ 0 := by omega
        have h2 : u - (modeList modes).length ≠ 0 := by omega
        simp [List.getElem?_singleton, h1, h2]
where
  parameterContext_length {params : Ctx} (modes : Modes params) :=
    Flow.parameterContext_length modes

theorem parameterContext_rights : ∀ {params : Ctx} (modes : Modes params) (u : Nat),
    (Flow.parameterContext modes).rights u = ((modeList modes)[u]?).getD none
  | _, .nil, u => by simp [Flow.parameterContext, Context.empty, modeList]
  | _ :: rest, .cons mode modes, u => by
    have hl := Flow.parameterContext_length modes
    have hm := modeList_length modes
    simp only [Flow.parameterContext, modeList]
    by_cases he : u = rest.length
    · subst he
      simp [hl.2, List.getElem?_append_right, hm]
    · rw [if_neg (by rw [hl.2]; exact he), parameterContext_rights modes u]
      by_cases hu : u < rest.length
      · rw [List.getElem?_append_left (by omega)]
      · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by omega)]
        have h2 : u - (modeList modes).length ≠ 0 := by omega
        simp [List.getElem?_singleton, h2]

theorem parameterContext_reference {params : Ctx} (modes : Modes params) {τ : Ty} (x : Var params τ) :
    (Flow.parameterContext modes).reference x = (modeAt modes x).map fun _ => x.unten := by
  unfold Context.reference
  rw [parameterContext_references, modeList_at]
  cases modeAt modes x <;> rfl

/-! ## 3. The plan and its check -/

/-- Position `u` passes the caller origin `i` with mode `m`. -/
def passesAt (ms : List (Option PassingMode)) (os : List (Option Nat)) (u : Nat) (m : PassingMode)
    (i : Nat) : Bool :=
  ms[u]? == some (some m) && os[u]? == some (some i)

/-- Some position consumes origin `i`. -/
def consumes (ms : List (Option PassingMode)) (os : List (Option Nat)) (j : Nat) : Bool :=
  (List.range ms.length).any fun u => passesAt ms os u .owned j

/-- Some position lends origin `i`. -/
def lends (ms : List (Option PassingMode)) (os : List (Option Nat)) (j : Nat) : Bool :=
  (List.range ms.length).any fun u => passesAt ms os u .borrowed j

/-- One position of the plan is admissible. -/
def positionFits (c : Context) (ms : List (Option PassingMode)) (os : List (Option Nat)) (u : Nat) : Bool :=
  match ms[u]?, os[u]? with
  | some (some .owned), some (some i) =>
    c.rights i == some .owned && !(lends ms os i) &&
      (List.range ms.length).all fun v => v == u || !(passesAt ms os v .owned i)
  | some (some .borrowed), some (some i) => (c.rights i).isSome
  | some (some _), _ => false
  | _, _ => true

def planFits (c : Context) (ms : List (Option PassingMode)) (os : List (Option Nat)) : Bool :=
  ms.length == os.length && (List.range ms.length).all (positionFits c ms os)

/-- The caller's context after the call: every consumed origin has no right. -/
def _root_.Gabbro.Grammatik.ArenaOwnership.Source.Context.afterCall (c : Context) (ms : List (Option PassingMode)) (os : List (Option Nat)) : Context :=
  { c with rights := fun j => if consumes ms os j then none else c.rights j }

variable {c : Context} {ms : List (Option PassingMode)} {os : List (Option Nat)}

theorem passesAt_iff {u : Nat} {m : PassingMode} {i : Nat} :
    passesAt ms os u m i = true ↔ ms[u]? = some (some m) ∧ os[u]? = some (some i) := by
  simp [passesAt]

theorem consumes_iff {j : Nat} :
    consumes ms os j = true ↔ ∃ u : Nat, ms[u]? = some (some PassingMode.owned) ∧ os[u]? = some (some j) := by
  simp only [consumes, List.any_eq_true, List.mem_range, passesAt_iff]
  constructor
  · rintro ⟨u, _, h⟩; exact ⟨u, h⟩
  · rintro ⟨u, h1, h2⟩
    exact ⟨u, (List.getElem?_eq_some_iff.mp h1).1, h1, h2⟩

theorem lends_iff {j : Nat} :
    lends ms os j = true ↔ ∃ u : Nat, ms[u]? = some (some PassingMode.borrowed) ∧ os[u]? = some (some j) := by
  simp only [lends, List.any_eq_true, List.mem_range, passesAt_iff]
  constructor
  · rintro ⟨u, _, h⟩; exact ⟨u, h⟩
  · rintro ⟨u, h1, h2⟩
    exact ⟨u, (List.getElem?_eq_some_iff.mp h1).1, h1, h2⟩

theorem planFits_at (hp : planFits c ms os = true) {u : Nat} (hu : u < ms.length) :
    positionFits c ms os u = true :=
  List.all_eq_true.mp (Bool.and_eq_true_iff.mp hp).2 u (List.mem_range.mpr hu)

/-- A passed argument has a caller origin with a right of its mode. -/
theorem planFits_mode (hp : planFits c ms os = true) {u : Nat} {m : PassingMode}
    (hm : ms[u]? = some (some m)) :
    ∃ i, os[u]? = some (some i) ∧ (c.rights i).isSome ∧ (m = .owned → c.rights i = some .owned) := by
  have hu : u < ms.length := (List.getElem?_eq_some_iff.mp hm).1
  have hf := planFits_at hp hu
  unfold positionFits at hf
  rw [hm] at hf
  cases ho : os[u]? with
  | none => cases m <;> simp [ho] at hf
  | some o =>
    cases o with
    | none => cases m <;> simp [ho] at hf
    | some i =>
      rw [ho] at hf
      cases m with
      | owned =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hf
        exact ⟨i, rfl, by rw [hf.1.1]; rfl, fun _ => hf.1.1⟩
      | borrowed => exact ⟨i, rfl, hf, fun h => by cases h⟩

/-- An owned origin is passed at one position only and is never also lent. -/
theorem planFits_owned_unique (hp : planFits c ms os = true) {u v : Nat} {q : PassingMode} {i : Nat}
    (hu : ms[u]? = some (some .owned)) (hou : os[u]? = some (some i))
    (hv : ms[v]? = some (some q)) (hov : os[v]? = some (some i)) : u = v := by
  have hlen : u < ms.length := (List.getElem?_eq_some_iff.mp hu).1
  have hf := planFits_at hp hlen
  unfold positionFits at hf
  rw [hu, hou] at hf
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at hf
  obtain ⟨⟨_, hl⟩, hall⟩ := hf
  cases q with
  | owned =>
    have hvlen : v < ms.length := (List.getElem?_eq_some_iff.mp hv).1
    rcases hall v hvlen with he | hn
    · exact he.symm
    · simp [passesAt, hv, hov] at hn
  | borrowed =>
    have : lends ms os i = true := lends_iff.mpr ⟨v, hv, hov⟩
    rw [hl] at this
    cases this

theorem afterCall_rights {j : Nat} :
    (c.afterCall ms os).rights j = if consumes ms os j then none else c.rights j := rfl

theorem afterCall_bounded (hb : c.bounded) : (c.afterCall ms os).bounded := by
  refine ⟨?_, hb.2⟩
  intro i hi
  rw [afterCall_rights]
  by_cases hc : consumes ms os i <;> simp [hc, hb.1 i hi]

theorem afterCall_rights_sub {j : Nat} {m : PassingMode} (h : (c.afterCall ms os).rights j = some m) :
    c.rights j = some m ∧ consumes ms os j = false := by
  rw [afterCall_rights] at h
  cases hc : consumes ms os j
  · rw [hc] at h; exact ⟨h, rfl⟩
  · rw [hc] at h; cases h

#print axioms planFits_owned_unique
#print axioms parameterContext_rights

end Gabbro.Grammatik.ArenaOwnership.Body
