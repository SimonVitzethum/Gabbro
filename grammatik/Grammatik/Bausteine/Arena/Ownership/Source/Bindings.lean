import Grammatik.Bausteine.Arena.Ownership.Source.Transfer

namespace Gabbro.Grammatik.ArenaOwnership.Source

variable {D : Deklaration}

theorem Context.bind_here (c : Context) (ref : Option Nat) {Γ : Ctx} {τ : Ty}
    (hlen : c.references.length = Γ.length) :
    (c.bind ref).reference (.here : Var (τ :: Γ) τ) = ref := by
  simp only [reference, bind, Var.unten, List.length_append, hlen, List.length_cons, List.length_nil,
  Nat.zero_add, Nat.lt_add_one, getElem?_pos, Std.le_refl, List.getElem_append_right, Nat.sub_self,
  List.getElem_cons_zero, Option.getD_some]

theorem Context.bind_there (c : Context) (ref : Option Nat) {Γ : Ctx} {τ υ : Ty}
    (hlen : c.references.length = Γ.length) (x : Var Γ τ) :
    (c.bind ref).reference (.there x : Var (υ :: Γ) τ) = c.reference x := by
  have hx : x.unten < c.references.length := by rw [hlen]; exact Var.unten_lt x
  simp only [reference, bind, Var.unten, List.getElem?_append, hx, ↓reduceIte, getElem?_pos, Option.getD_some]

theorem References.bind {c : Context} {g : Ghost} {Γ : Ctx} {τ : Ty} {ρ : Env D Γ}
    (hr : References c g ρ) (value : Wert D τ) (ref : Option Nat)
    (hv : ∀ i, ref = some i → ∃ h, g i = some h ∧ intVon τ value = some h.slot) :
    References (c.bind ref) g (.cons value ρ) := by
  refine ⟨by simp only [Context.bind, List.length_append, hr.1, List.length_cons, List.length_nil, Nat.zero_add,
  Nat.add_left_cancel_iff], ?_⟩
  intro υ x i hi
  cases x with
  | here =>
    rw [Context.bind_here c ref hr.1] at hi
    exact hv i hi
  | there x =>
    rw [Context.bind_there c ref hr.1 x] at hi
    exact hr.2 x i hi

theorem Context.reference_member {c : Context} {Γ : Ctx} {τ : Ty}
    (x : Var Γ τ) (i : Nat) (hi : c.reference x = some i) : some i ∈ c.references := by
  unfold Context.reference at hi
  cases he : c.references[x.unten]? with
  | none => simp only [he, Option.getD_none, reduceCtorEq] at hi
  | some ref =>
    simp only [he, Option.getD_some] at hi
    subst ref
    exact List.mem_of_getElem? he

theorem origin_member {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (c : Context)
    (e : Expr D Γ Λ τ) (i : Nat) (hi : origin c e = some i) : some i ∈ c.references := by
  induction e using Expr.rec (motive_2 := fun _ _ _ _ => True) with
  | var x => exact Context.reference_member x i hi
  | widen _ _ _ ih => exact ih hi
  | empty => trivial
  | num _ _ => trivial
  | _ => simp only [origin, expressionOrigin, reduceCtorEq] at hi

theorem Context.bind_bounded {c : Context} (hc : c.bounded) (ref : Option Nat)
    (hbound : ∀ i, ref = some i → i < c.next) : (c.bind ref).bounded := by
  refine ⟨hc.1, ?_⟩
  intro r hm i he
  rcases List.mem_append.mp hm with hm | hm
  · exact hc.2 r hm i he
  · have hr : r = ref := by simpa using hm
    exact hbound i (hr ▸ he)

theorem checked_binding (A : FreiForm D) (c : Context) (g : Ghost) (frame : Frame)
    (s : State) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (σ0 σ : World D) (ρ : Env D Γ)
    (e : Expr D Γ Λ τ) (hc : Realizes c g A frame s σ ρ) :
    Realizes (c.bind (origin c e)) g A frame s (σ.lese Λ e.orte)
      (.cons (eval σ0 e (σ.lese Λ e.orte) ρ) ρ) := by
  obtain ⟨ha, hf, hb, href, hrights⟩ := hc
  refine ⟨State.agrees_reads ha _ _, free_invariant_reads hf _ _, ?_, ?_, hrights⟩
  · apply Context.bind_bounded hb
    intro i hi
    exact hb.2 (some i) (origin_member c e i hi) i rfl
  · apply References.bind href _ (origin c e)
    intro i hi
    exact origin_sound c g ρ href e i hi σ0 (σ.lese Λ e.orte)

#print axioms checked_binding

end Gabbro.Grammatik.ArenaOwnership.Source
