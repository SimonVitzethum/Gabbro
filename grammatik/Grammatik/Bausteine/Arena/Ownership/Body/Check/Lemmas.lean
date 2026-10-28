import Grammatik.Bausteine.Arena.Ownership.Body.Check.Checker

/-! Facts about the check's outcome combinators and Bool tests, used by the
soundness proof of the check. -/

namespace Gabbro.Grammatik.ArenaOwnership.Body

open Source

variable {D : Deklaration}

theorem joinR_live {r1 r2 : Out} {j : Context} (h : joinR r1 r2 = some (some j)) :
    (r1 = some none ∧ r2 = some (some j)) ∨ (r2 = some none ∧ r1 = some (some j)) ∨
      ∃ a b, r1 = some (some a) ∧ r2 = some (some b) ∧ joinB a b = some j := by
  match r1, r2, h with
  | some none, _, h => exact Or.inl ⟨rfl, by simpa [joinR] using h⟩
  | some (some a), some none, h => exact Or.inr (Or.inl ⟨rfl, by simpa [joinR] using h⟩)
  | some (some a), some (some b), h =>
    refine Or.inr (Or.inr ⟨a, b, rfl, rfl, ?_⟩)
    simp only [joinR, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, hxj⟩ := h
    cases hxj
    exact hx
  | some (some a), none, h => simp only [joinR, reduceCtorEq] at h
  | none, some none, h => simp only [joinR, reduceCtorEq] at h
  | none, some (some _), h => simp only [joinR, reduceCtorEq] at h
  | none, none, h => simp only [joinR, reduceCtorEq] at h

theorem joinR_dead {r1 r2 : Out} (h : joinR r1 r2 = some none) : r1 = some none ∧ r2 = some none := by
  match r1, r2, h with
  | some none, some none, _ => exact ⟨rfl, rfl⟩
  | some none, some (some _), h => simp only [joinR, Option.some.injEq, reduceCtorEq] at h
  | some none, none, h => simp only [joinR, reduceCtorEq] at h
  | some (some a), some none, h => simp only [joinR, Option.some.injEq, reduceCtorEq] at h
  | some (some a), some (some b), h =>
    simp only [joinR, Option.map_eq_some_iff] at h
    obtain ⟨x, _, hx⟩ := h
    cases hx
  | some (some a), none, h => simp only [joinR, reduceCtorEq] at h
  | none, some none, h => simp only [joinR, reduceCtorEq] at h
  | none, some (some _), h => simp only [joinR, reduceCtorEq] at h
  | none, none, h => simp only [joinR, reduceCtorEq] at h

theorem mapR_live {f : Context → Context} {r : Out} {c' : Context} (h : mapR f r = some (some c')) :
    ∃ c, r = some (some c) ∧ c' = f c := by
  match r, h with
  | some (some c), h => simp only [mapR, Option.some.injEq] at h; exact ⟨c, rfl, h.symm⟩
  | some none, h => simp only [mapR, Option.some.injEq, reduceCtorEq] at h
  | none, h => simp only [mapR, reduceCtorEq] at h

theorem mapR_dead {f : Context → Context} {r : Out} (h : mapR f r = some none) : r = some none := by
  match r, h with
  | some (some c), h => simp only [mapR, Option.some.injEq, reduceCtorEq] at h
  | some none, _ => rfl
  | none, h => simp only [mapR, reduceCtorEq] at h

theorem seqR_live {r : Out} {f : Context → Out} {c' : Context} (h : seqR r f = some (some c')) :
    ∃ c, r = some (some c) ∧ f c = some (some c') := by
  match r, h with
  | some (some c), h => exact ⟨c, rfl, h⟩
  | some none, h => simp only [seqR, Option.some.injEq, reduceCtorEq] at h
  | none, h => simp only [seqR, reduceCtorEq] at h

theorem seqR_dead {r : Out} {f : Context → Out} (h : seqR r f = some none) :
    r = some none ∨ ∃ c, r = some (some c) ∧ f c = some none := by
  match r, h with
  | some (some c), h => exact Or.inr ⟨c, rfl, h⟩
  | some none, _ => exact Or.inl rfl
  | none, h => simp only [seqR, reduceCtorEq] at h

theorem backB_sound {kk : Context} {r : Out} (h : backB kk r = true) :
    r = some none ∨ ∃ c1, r = some (some c1) ∧ weakerB kk c1 = true := by
  match r, h with
  | some (some c1), h => exact Or.inr ⟨c1, rfl, h⟩
  | some none, _ => exact Or.inl rfl
  | none, h => simp only [backB, Bool.false_eq_true] at h

theorem Context.bind_drop (c : Context) (o : Option Nat) : (c.bind o).drop = c := by
  cases c
  simp only [Context.drop, Context.bind, ne_eq, List.cons_ne_self, not_false_eq_true,
  List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil]

theorem Context.bindFresh_drop_bounded {c : Context} (hc : c.bounded) : c.bindFresh.drop.bounded :=
  Context.drop_bounded (Context.bindFresh_bounded hc)

theorem dropContext_bounded {A : FreiForm D} {c : Context} (hc : c.bounded) {erg : Option Ty}
    (out : Flow.Output A erg) : (dropContext c out).bounded := by
  cases out
  · exact hc
  · exact Context.drop_bounded (Context.bindFresh_bounded hc)

theorem resultContext_bounded {A : FreiForm D} {c : Context} (hc : c.bounded) {erg : Option Ty}
    (out : Flow.Output A erg) : (resultContext c out).bounded := by
  rw [resultContext_isOwner]; exact resultContextB_bounded hc _

theorem slotIsLink_sound {A : FreiForm D} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} {e : Expr D Γ Λ τ} {p : Nat}
    (h : slotIsLink A e p = true) : exprSlotRead e = some ⟨A.tab, A.nxt, p⟩ := by
  unfold slotIsLink at h
  split at h
  · rename_i t f q he
    split at h
    · rename_i ht
      subst ht
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      obtain ⟨hf, hq⟩ := h
      subst hf hq
      exact he
    · cases h
  · cases h

theorem linkField_sound {A : FreiForm D} {t : D.Tab} {f : D.Feld t}
    (h : (if ht : t = A.tab then decide (ht ▸ f = A.nxt) else false) = true) :
    ∃ ht : t = A.tab, ht ▸ f = A.nxt := by
  split at h
  · rename_i ht; exact ⟨ht, of_decide_eq_true h⟩
  · cases h

theorem sigCompatB_sound {A : FreiForm D} {I : Interfaces A} {fs : List D.Fn} (hvoll : ∀ f, f ∈ fs)
    {n : Nat} {J : Modes (D.sigNr n).params} {owner : Bool} (h : sigCompatB A I fs n J owner = true) :
    SigCompatible I n J owner := by
  intro f hf
  have := List.all_eq_true.mp h f (hvoll f)
  simp only [hf, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at this
  exact this

end Gabbro.Grammatik.ArenaOwnership.Body
