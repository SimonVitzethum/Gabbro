import Grammatik.Bausteine.Arena.Unbounded.GRegion
import Grammatik.Bausteine.Arena.Unbounded.Lifetime
import Grammatik.Bausteine.Arena.Unbounded.Safety

/-! The open region of G refines the storage component `ArenaStorage.Heap` at `Capacity.unbounded`
(PLAN-DYNAMIC 14). The abstraction `RegionRepr t f H σ` says: every live payload of the abstract heap is the value
of field `f` of the G cell with the same number in the open table `t`. Then

* `read_refines`: a G read through a reference (`Expr.slotRef`) returns the abstract `Heap.read`;
* `write_refines`: a G write through a reference (`Stmt.assignSlotRef`) is the abstract `Heap.write`;
* `allocate_unbounded`: at `Capacity.unbounded` an allocation of a valid heap is never refused, whatever its extent --
  the absence of a ceiling, on the abstract side;
* `allocate_refines`: when the provider answers the heap's candidate cell (`alloc T` with a provider that realises the
  heap's allocator), the cell bound in G is the abstract allocation's, and the abstraction holds after it;
* `gregion_verfeinert`: the program of `GRegion` (`let r = alloc T; r->x = 7; return;`) is the abstract
  allocation followed by the abstract write, on the actual G run. -/

namespace Gabbro.Grammatik.ArenaStorage

open ArenaOwnership (Frame)

variable {D : Deklaration} {region : Type}

/-- **The abstraction**: every live abstract payload is the G cell's field. -/
def RegionRepr (t : D.Tab) (f : D.Feld t) (H : Heap region (Wert D (D.typ t f))) (σ : World D) : Prop :=
  ∀ i v, H.payload i = some v → σ.slots t i f = v

/-- A read records events only: an expression gives the same value after it. -/
theorem eval_lese {Γ : Ctx} {Λ Λ' : List (Res D)} {τ : Ty} (e : Expr D Γ Λ τ) (σ : World D)
    (os : List (D.Tab ⊕ D.Glob)) (ρ : Env D Γ) :
    eval (σ.lese Λ' os) e (σ.lese Λ' os) ρ = eval σ e σ ρ :=
  Extraktion.eval_liest_nur_orte e e.orte (fun _ h => h) _ _ _ _ ρ
    (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ => rfl)

/-- **A read through a reference returns the abstract read.** -/
theorem read_refines {t : D.Tab} {f : D.Feld t} {H : Heap region (Wert D (D.typ t f))} {σ σ₀ : World D}
    (hrep : RegionRepr t f H σ) {frame : Frame} {ref : Ref region} {v : Wert D (D.typ t f)}
    (he : H.read frame ref = some v) {Γ : Ctx} {Λ : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.ref n))
    (ht : D.tabNr n = some t) (ho : D.offen t = true) (hL : darf D t Λ) (ρ : Env D Γ)
    (hz : ((eval σ₀ r σ ρ).zelle : Int) = ref.handle.slot) :
    eval σ₀ (.slotRef r t ht ho f hL) σ ρ = v := by
  have hp : H.payload ref.handle.slot = some v := by
    unfold Heap.read at he
    split at he
    · exact he
    · cases he
  show σ.slots t ((eval σ₀ r σ ρ).zelle : Int) f = v
  rw [hz]
  exact hrep _ _ hp

section Execution

variable (O : Orakel D) (passes : Nat) (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)

/-- **A write through a reference is the abstract write**: the G statement runs, and the abstraction holds
    between the written heap and the written world. -/
theorem write_refines {V : Vertrag D} {l : Bool} {t : D.Tab} {f : D.Feld t}
    {H H' : Heap region (Wert D (D.typ t f))} {σ : World D} (hrep : RegionRepr t f H σ)
    {Γ : Ctx} {Λ : List (Res D)} {n : Nat} (r : Expr D Γ Λ (.ref n)) (ht : D.tabNr n = some t)
    (ho : D.offen t = true) (e : Expr D Γ Λ (D.typ t f)) (hw : V.schreibt t = true) (hL : darf D t Λ)
    (ρ : Env D Γ) {frame : Frame} {ref : Ref region}
    (hz : ((eval σ r σ ρ).zelle : Int) = ref.handle.slot)
    (hH : H.write frame ref (eval σ e σ ρ) = some H') :
    ∃ σ', execStmt O passes R (l := l) (.assignSlotRef r t ht ho f e hw hL) σ ρ = .ok σ' ρ ∧
      RegionRepr t f H' σ' := by
  refine ⟨_, rfl, ?_⟩
  have hput : H' = H.put ref.handle.slot (some (eval σ e σ ρ)) := by
    unfold Heap.write at hH
    split at hH
    · exact (Option.some.inj hH).symm
    · cases hH
  subst hput
  intro i v hv
  simp only [eval_lese]
  rw [hz]
  by_cases hi : i = ref.handle.slot
  · subst hi
    simp only [Heap.put, ite_true, Option.some.injEq] at hv
    subst hv
    exact schreibSlot_slots_same _ _ _ _ _ _
  · simp only [Heap.put, hi, ite_false] at hv
    rw [schreibSlot_slots_other _ _ _ _ _ _ _ hi]
    exact hrep i v hv

end Execution

/-- **No ceiling**: at `Capacity.unbounded` the allocation of a valid heap succeeds whatever its extent; the cell
    is the heap's candidate and the heap stays valid. -/
theorem allocate_unbounded {α : Type} (H : Heap region α) (hv : H.Valid .unbounded) (frame : Frame) (value : α) :
    ∃ H' ref, H.allocate .unbounded true frame value = some (H', ref) ∧
      ref.handle.slot = (H.candidate : Int) ∧ H'.Valid .unbounded := by
  have hempty := (H.candidate_facts hv).1
  cases h : H.allocate .unbounded true frame value with
  | none =>
    simp only [Heap.allocate, Capacity.permits, Bool.and_self, ↓reduceIte, ArenaOwnership.State.allocate, hempty,
  Option.bind_eq_bind, Option.bind_some, reduceCtorEq] at h
  | some x =>
    obtain ⟨H', ref⟩ := x
    obtain ⟨hv', _, hs, _⟩ := Heap.allocate_valid hv h
    exact ⟨H', ref, rfl, hs, hv'⟩

/-- **The allocation keeps the abstraction**, when the installed payload is what the G cell holds (the provider's
    fresh cell, with whatever its memory held before the first write). -/
theorem allocate_refines {t : D.Tab} {f : D.Feld t} {H H' : Heap region (Wert D (D.typ t f))} {σ : World D}
    (hrep : RegionRepr t f H σ) {frame : Frame} {ref : Ref region}
    (he : H.allocate .unbounded true frame (σ.slots t (H.candidate : Int) f) = some (H', ref)) :
    RegionRepr t f H' σ := by
  obtain ⟨_, _, _, hinst⟩ := Heap.allocate_parts he
  intro i v hv
  rw [hinst] at hv
  simp only [Heap.install] at hv
  by_cases hi : i = (H.candidate : Int)
  · simp only [hi, ite_true, Option.some.injEq] at hv
    subst hi
    exact hv
  · simp only [hi, ite_false] at hv
    exact hrep i v hv

/-- The empty heap is valid at `Capacity.unbounded` and represents every world. -/
theorem empty_repr (t : D.Tab) (f : D.Feld t) (σ : World D) :
    RegionRepr t f (Heap.empty : Heap region (Wert D (D.typ t f))) σ := fun _ _ h => by cases h

/-! ## The program of `GRegion`, abstractly -/

open GRegion

/-- **`let r = alloc T; r->x = 7; return;` refines the abstract heap**: from the empty heap the abstract allocation
    (`Capacity.unbounded`) yields the candidate cell `0`, the abstract write stores `7` there, and the actual G run --
    the provider answering the candidate -- ends in a world the written heap represents. -/
theorem gregion_verfeinert (passes : Nat) (R : ∀ f : rD.Fn, World rD → Env rD (rD.params f) → RufAusgang f)
    (frame : Frame) :
    ∃ (H1 H2 : Heap region (Wert rD (rD.typ () ()))) (ref : Ref region) (σ' : World rD),
      (Heap.empty : Heap region _).allocate .unbounded true frame (w0.slots () 0 ()) = some (H1, ref) ∧
      ref.handle.slot = 0 ∧
      H1.write frame ref ⟨7, by decide, by decide⟩ = some H2 ∧
      execEnd (oK 0) passes R rumpf w0 .nil = .zurueck σ' () ∧
      RegionRepr () () H2 σ' := by
  obtain ⟨H1, ref, ha, hs, hv1⟩ := allocate_unbounded (Heap.empty : Heap region (Wert rD (rD.typ () ())))
    (Heap.empty_valid _) frame (w0.slots () 0 ())
  have hcand : ((Heap.empty : Heap region (Wert rD (rD.typ () ()))).candidate : Int) = 0 := rfl
  obtain ⟨_, hown, _, _⟩ := Heap.allocate_valid (Heap.empty_valid _) ha
  have hacc : H1.rights.access frame ref.handle := ArenaOwnership.State.owner_access hown
  have hw : H1.write frame ref ⟨7, by decide, by decide⟩ = some (H1.put ref.handle.slot (some ⟨7, by decide, by decide⟩)) := by
    simp only [Heap.write, hacc, ↓reduceIte]
  obtain ⟨σ', hrun, h7⟩ := zelle_geschrieben 0 passes R
  refine ⟨H1, _, ref, σ', ha, hs.trans hcand, hw, hrun, ?_⟩
  intro i v hv
  by_cases hi : i = ref.handle.slot
  · subst hi
    simp only [Heap.put, ite_true] at hv
    obtain rfl := Option.some.inj hv
    rw [hs, hcand]
    show σ'.slots () 0 () = ⟨7, _, _⟩
    cases hc : σ'.slots () 0 () with
    | mk m h1 h2 =>
      have h7' : (σ'.slots () 0 ()).n = 7 := by exact_mod_cast h7
      rw [hc] at h7'
      simp only at h7'
      subst h7'
      rfl
  · simp only [Heap.put, hi, ite_false] at hv
    obtain ⟨_, _, _, hinst⟩ := Heap.allocate_parts ha
    rw [hinst] at hv
    unfold Heap.install at hv
    simp only at hv
    rw [if_neg (by rw [← hs]; exact hi)] at hv
    simp only [Heap.empty, reduceCtorEq] at hv

end Gabbro.Grammatik.ArenaStorage
