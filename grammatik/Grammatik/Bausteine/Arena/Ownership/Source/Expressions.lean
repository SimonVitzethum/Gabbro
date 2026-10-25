import Grammatik.Bausteine.Arena.Ownership.Source.Context

/-! Executable expression admission over the existing G syntax. The source
walk collects obligations once; abstract checking and concrete read safety
interpret the same obligations. Unknown/computed index provenance is refused. A read through a reference into an open region
(`Expr.slotRef`) owes what a read of another carrier owes: the region is not the tracked arena
(`range`), and the reference itself is admitted.
-/

namespace Gabbro.Grammatik.ArenaOwnership.Source

variable {D : Deklaration}

inductive Requirement (D : Deklaration) (Γ : Ctx) (Λ : List (Res D)) where
  | varUse {τ : Ty} (x : Var Γ τ)
  | access (t : D.Tab) (i : Expr D Γ Λ (Ty.index (D.count t)))
  | range (t : D.Tab)
  | unsupported

mutual
def requirements {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} : Expr D Γ Λ τ → List (Requirement D Γ Λ)
  | .var x => [.varUse x]
  | .slot t _ i _ => .access t i :: requirements i
  | .thru p t _ _ i _ => .access t i :: (requirements p ++ requirements i)
  | .oldS t _ i _ => .range t :: requirements i
  | .getBytes t _ _ _ i _ _ _ => .range t :: requirements i
  | .widen _ _ e | .neg e | .not e | .some e | .istSome e => requirements e
  | .add a b | .sub a b | .mul a b | .lt a b | .le a b | .eq a b
  | .fllt a b | .flle a b | .and a b | .or a b => requirements a ++ requirements b
  | .div _ _ a b | .rem _ _ a b | .sdiv _ a b | .srem _ a b | .band _ _ a b
  | .bor _ _ _ _ _ a b | .bxor _ _ _ _ _ a b | .shl _ _ _ _ _ a b | .shr _ _ _ _ _ a b =>
    requirements a ++ requirements b
  | .case _ _ payload => payloadRequirements payload
  | .slotRef r t _ _ _ _ => .range t :: requirements r
  | .forallSlots .. | .existsSlots .. | .reaches .. => [.unsupported]
  | .refEq a b => requirements a ++ requirements b
  | .arrNil | .strLit .. => []
  | .arrCons a b => requirements a ++ requirements b
  | .arrGet a b => requirements a ++ requirements b
  | .strCat a b => requirements a ++ requirements b
  | .arrSet a i v => requirements a ++ requirements i ++ requirements v
  | .strLen s => requirements s
  | .lit _ | .tru | .fls | .glob .. | .ptrOf .. | .fnref .. | .oldG .. | .none _ | .why .. => []

def payloadRequirements {Γ : Ctx} {Λ : List (Res D)} {c : Option (Int × Int)} :
    NutzlastExpr D Γ Λ c → List (Requirement D Γ Λ)
  | .empty => []
  | .num e => requirements e
end

def accessCheck {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (c : Context) (e : Expr D Γ Λ τ) : Bool :=
  match origin c e with
  | none => false
  | some i => (c.rights i).isSome

def Requirement.check (A : FreiForm D) (c : Context) {Γ : Ctx} {Λ : List (Res D)} :
    Requirement D Γ Λ → Bool
  | .varUse x => match c.reference x with | none => true | some i => (c.rights i).isSome
  | .access t i => if t = A.tab then accessCheck c i else true
  | .range t => decide (t ≠ A.tab)
  | .unsupported => false

def checkExpression (A : FreiForm D) (c : Context) {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (e : Expr D Γ Λ τ) : Bool := (requirements e).all (Requirement.check A c)

def AllowedIndex {Γ : Ctx} {Λ : List (Res D)} {lo hi : Int}
    (c : Context) (g : Ghost) (s : State) (frame : Frame) (σ0 σ : World D) (ρ : Env D Γ)
    (e : Expr D Γ Λ (.int lo hi)) : Prop :=
  ∃ originId h, origin c e = some originId ∧ g originId = some h ∧
    s.access frame h ∧ (eval σ0 e σ ρ).n = h.slot

def Requirement.satisfied (A : FreiForm D) (c : Context) (g : Ghost) (s : State) (frame : Frame)
    {Γ : Ctx} {Λ : List (Res D)} (σ0 σ : World D) (ρ : Env D Γ) : Requirement D Γ Λ → Prop
  | .varUse x => ∀ i, c.reference x = some i → ∃ h, g i = some h ∧ s.access frame h
  | .access t i => if t = A.tab then AllowedIndex c g s frame σ0 σ ρ i else True
  | .range t => t ≠ A.tab
  | .unsupported => False

theorem PassingMode.access_of_permits {mode : PassingMode} {s : State} {frame : Frame} {h : Handle}
    (hp : mode.permits s frame h) : s.access frame h := by
  cases mode with
  | owned => exact State.owner_access hp
  | borrowed => exact hp

theorem accessCheck_sound {Γ : Ctx} {Λ : List (Res D)} {lo hi : Int}
    (c : Context) (g : Ghost) (s : State) (frame : Frame) (σ0 σ : World D) (ρ : Env D Γ)
    (hr : References c g ρ) (hp : Rights c g s frame) (e : Expr D Γ Λ (.int lo hi))
    (hb : accessCheck c e = true) : AllowedIndex c g s frame σ0 σ ρ e := by
  cases ho : origin c e with
  | none => simp [accessCheck, ho] at hb
  | some i =>
    cases hm : c.rights i with
    | none => simp [accessCheck, ho, hm] at hb
    | some mode =>
      obtain ⟨h, hg, hpermit⟩ := hp.1 i mode hm
      obtain ⟨h', hg', hv⟩ := origin_sound c g ρ hr e i ho σ0 σ
      rw [hg] at hg'
      cases hg'
      refine ⟨i, h, ho, hg, PassingMode.access_of_permits hpermit, ?_⟩
      exact Option.some.inj hv

theorem Requirement.check_sound (A : FreiForm D) (c : Context) (g : Ghost) (s : State) (frame : Frame)
    {Γ : Ctx} {Λ : List (Res D)} (σ0 σ : World D) (ρ : Env D Γ)
    (hr : References c g ρ) (hp : Rights c g s frame) (r : Requirement D Γ Λ)
    (hb : r.check A c = true) : r.satisfied A c g s frame σ0 σ ρ := by
  cases r with
  | varUse x =>
    intro i hi
    cases hm : c.rights i with
    | none => simp [Requirement.check, hi, hm] at hb
    | some mode =>
      obtain ⟨h, hg, hright⟩ := hp.1 i mode hm
      exact ⟨h, hg, PassingMode.access_of_permits hright⟩
  | access t i =>
    by_cases ht : t = A.tab
    · simp only [Requirement.check, ht, ite_true] at hb
      simpa only [Requirement.satisfied, ite_eq_left ht] using accessCheck_sound c g s frame σ0 σ ρ hr hp i hb
    · simp [Requirement.satisfied, ht]
  | range t =>
    change t ≠ A.tab
    exact of_decide_eq_true hb
  | unsupported => cases hb

/-- Every obligation of every admitted expression has an actual current
grant. An index with the same numeric value but stale provenance cannot pass. -/
theorem checkExpression_sound (A : FreiForm D) (c : Context) (g : Ghost) (s : State) (frame : Frame)
    {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} (σ0 σ : World D) (ρ : Env D Γ)
    (hr : References c g ρ) (hp : Rights c g s frame) (e : Expr D Γ Λ τ)
    (hb : checkExpression A c e = true) :
    ∀ r ∈ requirements e, r.satisfied A c g s frame σ0 σ ρ := by
  intro r hm
  exact Requirement.check_sound A c g s frame σ0 σ ρ hr hp r ((List.all_eq_true.mp hb) r hm)

theorem accessCheck_after_consume {Γ : Ctx} {Λ : List (Res D)} {τ : Ty}
    (c : Context) (e : Expr D Γ Λ τ) (i : Nat) (hi : origin c e = some i) :
    accessCheck (c.kill i) e = false := by
  simp [accessCheck, (Context.kill_aliases e i hi).1]

#print axioms checkExpression_sound

end Gabbro.Grammatik.ArenaOwnership.Source
