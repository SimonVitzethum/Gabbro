module

public import Gabbro.Body
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Order.Lattice
public import Gabbro.Sicherheit.Ausdruck.Teil1
public import Gabbro.Sicherheit.Ausdruck.Record

@[expose] public section

namespace Gabbro.Sicherheit
open Gabbro.Body

mutual
/-- **Der Pruefer.** `schluss D Δ e = some sh`: der Pass nimmt `e` an und gibt ihm die
    Gestalt `sh`; `none` ist die Absage. -/
def schluss (D : Deklaration) : Lokal → Expr → Option Shape
  | _, .lit v => literalShape v
  | Δ, .name n => Δ n
  | _, .global g => D.global g
  | Δ, .place c i f =>
      -- `M103`: der Index liegt in `0 ..< count`, oder der Pass sagt ab.
      match schluss D Δ i with
      | some (.intIn lo hi) => if 0 ≤ lo ∧ hi < D.count c then D.slot c f else none
      | _ => none
  | _, .fieldOf c f => D.feld c f
  | Δ, .un .not a =>
      match schluss D Δ a with
      | some .bool => some .bool
      | _ => none
  | Δ, .un .neg a =>
      match schluss D Δ a with
      | some .int => some .int
      | some (.intIn lo hi) => some (.intIn (-hi) (-lo))
      | _ => none
  | Δ, .bin op a b =>
      match schluss D Δ a, schluss D Δ b with
      | some sa, some sb =>
          match arith op sa sb with
          | some sh => some sh
          | none => vergleich op sa sb
      | _, _ => none
  | Δ, .someOf a =>
      match schluss D Δ a with
      | some sh => if (zahl sh).isSome then some .opt else none
      | none => none
  | Δ, .forallSlots v n b =>
      -- Der Binder traegt den Indexbereich der Domaene (`slots of`: `0 ..< count`).
      match schluss D (fun m => if m = v then some (.intIn 0 (n - 1)) else Δ m) b with
      | some .bool => some .bool
      | _ => none
  | Δ, .existsSlots v n b =>
      match schluss D (fun m => if m = v then some (.intIn 0 (n - 1)) else Δ m) b with
      | some .bool => some .bool
      | _ => none
  | Δ, .reaches c a z via _ =>
      -- (S2): das `via`-Feld ist an jedem Index eine Option, sonst Absage.
      match schluss D Δ a, schluss D Δ z, D.slot c via with
      | some sa, some sz, some .opt => if (zahl sa).isSome ∧ (zahl sz).isSome then some .bool else none
      | _, _, _ => none
  | Δ, .chainFrom c h x via _ =>
      match schluss D Δ h, schluss D Δ x, D.slot c via with
      | some .opt, some sx, some .opt => if (zahl sx).isSome then some .bool else none
      | _, _, _ => none
  | _, .hasShape _ _ => some .bool
  | Δ, .wrapTo _ _ a =>
      match schluss D Δ a with
      | some sh => if (zahl sh).isSome then some .int else none
      | none => none
  -- Tagged construction needs the target's case declaration, as before.
  | _, .tagOf _ none => none
  | _, .tagOf _ (some _) => none
  | Δ, .recOf args => (schlussAll D Δ args).map Shape.record
  | Δ, .recGet base idx =>
      match schluss D Δ base with
      | some (.record ss) => ss[idx]?
      | _ => none
  | Δ, .recSet base idx val =>
      match schluss D Δ base, schluss D Δ val with
      | some (.record ss), some sh =>
          if idx < ss.length then some (.record (ss.set idx sh)) else none
      | _, _ => none
termination_by structural _ e => e

/-- Record construction succeeds exactly when every field has an inferred shape. -/
def schlussAll (D : Deklaration) (Δ : Lokal) : List Expr → Option (List Shape)
  | [] => some []
  | e :: es =>
      match schluss D Δ e, schlussAll D Δ es with
      | some sh, some ss => some (sh :: ss)
      | _, _ => none
termination_by structural es => es
end

/-- `Some` against the target option's payload bound (F10, `M101`): with no target any
    number passes, as before; with `(lo, hi)` only a ranged payload inside it does.
    `gift/170` (`Some(8)` on `count 8`) is refused here instead of flowing on. The
    bound lives at the use site, so `schluss` above does not thread it -- the carrier
    `schlussMitZiel` does, and wiring it into `pruefe` is its own step. -/
def somePasst : Option (Int × Int) → Shape → Option Shape
  | none, sh => if (zahl sh).isSome then some .opt else none
  | some (lo, hi), sh =>
    match sh with
    | .intIn lo' hi' => if lo ≤ lo' ∧ hi' ≤ hi then some .opt else none
    | _ => none

/-- The checker with the option target bound carried into `someOf`: every other form
    delegates to `schluss`, so the two can never drift apart -- and the safety proof
    below reuses `schluss_sicher` arm by arm for the same reason. -/
def schlussMitZiel (D : Deklaration) (ziel : Option (Int × Int)) : Lokal → Expr → Option Shape
  | Δ, .someOf a =>
      match schluss D Δ a with
      | some sh => somePasst ziel sh
      | none => none
  | Δ, e => schluss D Δ e

/-! ## 3. Der Satz -- ein angenommener Ausdruck wird nie `none`, und sein Wert passt -/

/-- **(S2) als Praemisse:** das `via`-Feld ist an JEDEM Index option-gestaltig. -/
def KettenWohlgeformt (D : Deklaration) (σ : World) : Prop :=
  ∀ c via k, D.slot c via = some .opt → (σ (.slot c k via)).hasShape .opt = true

theorem zahl_some_int {sh : Shape} {v : Value} (hz : (zahl sh).isSome = true)
    (hv : v.hasShape sh = true) : ∃ n, v = .int n := by
  cases sh <;> simp only [zahl, Option.isSome_some, Option.isSome_none, Bool.false_eq_true] at hz
  · exact Value.hasShape_int_true v hv
  · obtain ⟨n, hn, _⟩ := Value.hasShape_intIn_true v _ _ hv; exact ⟨n, hn⟩

theorem zahl_some_of_zahl {sh : Shape} {r : Option (Int × Int)} (h : zahl sh = some r) :
    (zahl sh).isSome = true := by rw [h]; rfl

theorem bereich_of_zahl {sh : Shape} {lo hi : Int} (h : zahl sh = some (some (lo, hi))) :
    sh = .intIn lo hi := by
  cases sh <;> simp only [zahl, Option.some.injEq, reduceCtorEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl

theorem int_of_zahl_none {sh : Shape} (h : zahl sh = some none) : sh = .int := by
  cases sh <;> simp only [zahl, reduceCtorEq, Option.some.injEq] at h; rfl

/-- `allBelow` ueber einer Funktion, die immer einen `bool` liefert, liefert einen `bool`. -/
theorem allBelow_bool (f : Nat → Option Value) :
    ∀ n, (∀ k, k < n → ∃ b, f k = some (.bool b)) → ∃ b, allBelow f n = some (.bool b) := by
  intro n
  rw [allBelow_eq]
  induction n with
  | zero => intro _; exact ⟨true, rfl⟩
  | succ n ih =>
      intro hf
      obtain ⟨a, ha⟩ := ih (fun k hk => hf k (Nat.lt_succ_of_lt hk))
      obtain ⟨b, hb⟩ := hf n (Nat.lt_succ_self n)
      exact ⟨a && b, by simp only [allBelowImpl, ha, hb]⟩

theorem anyBelow_bool (f : Nat → Option Value) :
    ∀ n, (∀ k, k < n → ∃ b, f k = some (.bool b)) → ∃ b, anyBelow f n = some (.bool b) := by
  intro n
  rw [anyBelow_eq]
  induction n with
  | zero => intro _; exact ⟨false, rfl⟩
  | succ n ih =>
      intro hf
      obtain ⟨a, ha⟩ := ih (fun k hk => hf k (Nat.lt_succ_of_lt hk))
      obtain ⟨b, hb⟩ := hf n (Nat.lt_succ_self n)
      exact ⟨a || b, by simp only [anyBelowImpl, ha, hb]⟩

/-- `chase` ueber wohlgeformten Ketten liefert einen `bool` -- mit jedem Treibstoff. -/
theorem chase_bool (σ : World) (c via : String) (bis : Int)
    (hk : ∀ k, (σ (.slot c k via)).hasShape .opt = true) :
    ∀ n k, ∃ b, chase σ c via bis k n = some (.bool b) := by
  intro n
  rw [chase_eq]
  induction n with
  | zero => intro k; exact ⟨_, rfl⟩
  | succ n ih =>
      intro k
      simp only [chaseImpl]
      split
      · exact ⟨true, rfl⟩
      · rcases Value.hasShape_opt_true _ (hk k) with h | ⟨m, h⟩
        · rw [h]; exact ⟨false, rfl⟩
        · rw [h]; exact ih m

/-- **Der Rumpf eines Quantors**: unter dem Binder mit dem Indexbereich `0 ..< n` liefert
    er fuer jeden GERUFENEN Index einen `bool`. Herausgezogen, weil `forall` und `exists`
    denselben Schritt brauchen. -/
theorem quant_rumpf (D : Deklaration) (Γ : Typing) {b : Expr}
    (ih : ∀ (Δ : Lokal) (s : State) (sh : Shape), WF Γ s.world → WFL Δ s.local' →
        KettenWohlgeformt D s.world → schluss D Δ b = some sh →
        ∃ v, eval s b = some v ∧ v.hasShape sh = true)
    (Δ : Lokal) (s : State) (n : Int) {v : String}
    (hw : WF Γ s.world) (hl : WFL Δ s.local') (hk : KettenWohlgeformt D s.world)
    (hb : schluss D (fun m => if m = v then some (.intIn 0 (n - 1)) else Δ m) b = some .bool) :
    ∀ k : Nat, k < n.toNat →
      ∃ t, eval { s with local' := bindLocal s.local' v (.int k) } b = some (.bool t) := by
  intro k hkn
  have hl' : WFL (fun m => if m = v then some (.intIn 0 (n - 1)) else Δ m)
      (bindLocal s.local' v (.int k)) := by
    intro m sh hm
    by_cases hmv : m = v
    · subst hmv; simp only [↓reduceIte, Option.some.injEq] at hm; subst hm
      simp only [Value.hasShape, bindLocal_here, Nat.cast_nonneg, true_and, decide_eq_true_eq]
      omega
    · simp only [hmv, ↓reduceIte] at hm; simpa [bindLocal, hmv] using hl m sh hm
  obtain ⟨t, ht, hts⟩ := ih _ ⟨s.world, bindLocal s.local' v (.int k)⟩ _ hw hl' hk hb
  obtain ⟨tb, rfl⟩ := Value.hasShape_bool_true t hts
  exact ⟨tb, ht⟩

set_option linter.unusedSectionVars false in
theorem schluss_sicher_global (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ)
    (g)
    (Δ : Lokal)
    (s : State)
    (sh : Shape)
    : WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ (.global g : Expr) = some sh → ∃ v, eval s (.global g : Expr) = some v ∧ v.hasShape sh = true :=
  by
  intro hw _ _ h
  refine ⟨_, rfl, hw _ sh ?_⟩
  rw [hD.2.2 g]; exact h

set_option linter.unusedSectionVars false in
theorem schluss_sicher_place (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ)
    (c)
    (i)
    (f)
    (Δ : Lokal)
    (s : State)
    (sh : Shape)
    (ih_schluss_sicher_i : ∀ (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ), ∀ (Δ : Lokal), ∀ (s : State), ∀ (sh : Shape), WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ i = some sh → ∃ v, eval s i = some v ∧ v.hasShape sh = true)
    : WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ (.place c i f : Expr) = some sh → ∃ v, eval s (.place c i f : Expr) = some v ∧ v.hasShape sh = true :=
  by
  have ih := ih_schluss_sicher_i D Γ hD
  intro hw hl hk h
  simp only [schluss] at h
  split at h
  · rename_i lo hi hi'
    split at h
    · rename_i hb
      obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk hi'
      obtain ⟨k, hk', hlo, hhi⟩ := Value.hasShape_intIn_true v lo hi hvs
      subst hk'
      refine ⟨_, ?_, hw (.slot c k f) sh ?_⟩
      · simp only [eval, hv]
      · rw [hD.1 c k f (by omega) (by omega)]; exact h
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

set_option linter.unusedSectionVars false in
theorem schluss_sicher_fieldOf (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ)
    (c)
    (f)
    (Δ : Lokal)
    (s : State)
    (sh : Shape)
    : WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ (.fieldOf c f : Expr) = some sh → ∃ v, eval s (.fieldOf c f : Expr) = some v ∧ v.hasShape sh = true :=
  by
  intro hw _ _ h
  refine ⟨_, rfl, hw _ sh ?_⟩
  rw [hD.2.1 c f]; exact h

set_option linter.unusedSectionVars false in
theorem schluss_sicher_un (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ)
    (op)
    (a)
    (Δ : Lokal)
    (s : State)
    (sh : Shape)
    (ih_schluss_sicher_a : ∀ (D : Deklaration) (Γ : Typing) (hD : Deklariert D Γ), ∀ (Δ : Lokal), ∀ (s : State), ∀ (sh : Shape), WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ a = some sh → ∃ v, eval s a = some v ∧ v.hasShape sh = true)
    : WF Γ s.world → WFL Δ s.local' → KettenWohlgeformt D s.world → schluss D Δ (.un op a : Expr) = some sh → ∃ v, eval s (.un op a : Expr) = some v ∧ v.hasShape sh = true :=
  by
      have ih := ih_schluss_sicher_a D Γ hD
      intro hw hl hk h
      cases op with
      | not =>
          simp only [schluss] at h
          split at h
          · rename_i ha
            obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk ha
            obtain ⟨b, rfl⟩ := Value.hasShape_bool_true v hvs
            cases h
            simp only [eval, hv, unop, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
          · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
      | neg =>
          simp only [schluss] at h
          split at h
          · rename_i ha
            obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk ha
            obtain ⟨n, rfl⟩ := Value.hasShape_int_true v hvs
            cases h
            simp only [eval, hv, unop, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left']
          · rename_i lo hi ha
            obtain ⟨v, hv, hvs⟩ := ih Δ s _ hw hl hk ha
            obtain ⟨n, rfl, h1, h2⟩ := Value.hasShape_intIn_true v lo hi hvs
            cases h
            simp only [eval, hv, unop, Option.some.injEq, Value.hasShape, Bool.decide_and, exists_eq_left',
  neg_le_neg_iff, Bool.and_eq_true, decide_eq_true_eq]; omega
          · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

end Gabbro.Sicherheit
