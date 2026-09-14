/-
  File:      Grammatik/Isabelle/Table_Zaehlung.lean
  Part of:   Gabbro -- Lean port of `beweise/Table_Zaehlung.thy`
             («B13» -- the aggregation `count(s in slots of A : P s)`;
             lane 168).

  What this file is: what a generated counting loop delivers (Part I),
  the preservation question a template owes (Part II: one mutation must
  rewrite to a decrement plus an increment, not two loops), the counted
  COST (Part III: the nested loop really does `m * n` steps), and the
  boundaries as counterexamples (Part IV).

  Model notes: the generator writes a loop with an accumulator, so the
  loop (`zaehle`) stands here, not cardinality -- and the first theorem
  holds the two against each other. Isabelle `card {s. s < n ∧ P s}` is
  `((List.range n).filter P).length`: the range enumerates exactly the
  set below the bound, so it is the same number. Isabelle `Suc` is
  `+ 1` (definitionally equal). Isabelle function update `f(s0 := b)`
  is `upd` below (`Function.update` does not exist in this core).
  Predicates `(nat ⇒ bool)` are `Nat → Bool`, written with `decide`.

  No bridge to the model semantics: the aggregation form was declined
  (`messung/AGGREGATION.md` §4 stands); there is no `count` syntax in
  `Syntax.lean` to tie to.
-/

namespace Gabbro.Grammatik.TableZaehlung

set_option linter.unusedVariables false

/-- Point update: `f` with `s0` remapped to `b`. -/
def upd (f : Nat → α) (s0 : Nat) (b : α) : Nat → α :=
  fun s => if s = s0 then b else f s

theorem upd_self (f : Nat → α) (s0 : Nat) (b : α) : upd f s0 b s0 = b := by
  simp [upd]

theorem upd_other {f : Nat → α} {s0 s : Nat} {b : α} (h : s ≠ s0) :
    upd f s0 b s = f s := by
  simp [upd, h]

/-! ## Part I -- the generated loop IS the count -/

/-- The loop the generator writes: an accumulator over the slots. -/
def zaehle (P : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => zaehle P n + (if P n then 1 else 0)

/-- Z-0, the congruence, standing first because every theorem below
    needs it: two predicates agreeing below the bound count equally.
    The frame statement of the count. -/
theorem zaehle_kongruent {P Q : Nat → Bool} {n : Nat}
    (h : ∀ s, s < n → P s = Q s) : zaehle P n = zaehle Q n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have e : P k = Q k := h k (Nat.lt_succ_self k)
    have hk : ∀ s, s < k → P s = Q s := fun s hs => h s (by omega)
    simp only [zaehle, ih hk, e]

/-- Z-1: the loop delivers the cardinality of the hit set below the
    bound. This is what makes `count(...)` a count at all. -/
theorem zaehle_ist_kardinalitaet (P : Nat → Bool) (n : Nat) :
    zaehle P n = ((List.range n).filter P).length := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have e1 : List.range (k + 1) = List.range k ++ [k] := List.range_succ
    rw [e1, List.filter_append, List.length_append, ← ih]
    cases hPk : P k <;> simp [zaehle, hPk]

/-- Z-2: the count is bounded by the bound. The line carrying a range
    promise on the counter field. -/
theorem zaehle_beschraenkt (P : Nat → Bool) (n : Nat) : zaehle P n ≤ n := by
  induction n with
  | zero => simp [zaehle]
  | succ k ih =>
    cases hPk : P k <;> simp [zaehle, hPk] <;> omega

/-! ## Part II -- the preservation question -/

/-- Z-3: the slot whose naming is TAKEN AWAY: the old object's count
    falls by exactly one. Written with `+ 1`, not `-`, so the statement
    does not hang on natural subtraction. -/
theorem zaehlung_faellt_um_eins {f : Nat → Nat} {s0 a b n : Nat}
    (hfa : f s0 = a) (hne : b ≠ a) (hlt : s0 < n)
    : zaehle (fun s => decide (f s = a)) n
      = zaehle (fun s => decide (upd f s0 b s = a)) n + 1 := by
  revert hlt
  induction n with
  | zero =>
    intro hlt
    exact absurd hlt (Nat.not_lt_zero _)
  | succ k ih =>
    intro hlt
    by_cases heq : s0 = k
    · have hcong : zaehle (fun s => decide (f s = a)) k
          = zaehle (fun s => decide (upd f s0 b s = a)) k := by
        apply zaehle_kongruent
        intro s hs
        have hne2 : s ≠ s0 := by
          intro hcon
          rw [hcon, heq] at hs
          exact absurd hs (Nat.lt_irrefl _)
        show decide (f s = a) = decide (upd f s0 b s = a)
        rw [upd_other hne2]
      have e1 : decide (f k = a) = true := by
        have hfk : f k = a := by rw [← heq]; exact hfa
        simp [hfk]
      have e2 : decide (upd f s0 b k = a) = false := by
        have huk : upd f s0 b k = b := by rw [← heq]; exact upd_self _ _ _
        rw [huk]
        exact decide_eq_false hne
      have s1 : zaehle (fun s => decide (f s = a)) (k + 1)
          = zaehle (fun s => decide (f s = a)) k + 1 := by simp [zaehle, e1]
      have s2 : zaehle (fun s => decide (upd f s0 b s = a)) (k + 1)
          = zaehle (fun s => decide (upd f s0 b s = a)) k := by simp [zaehle, e2]
      omega
    · have hle : s0 ≤ k := Nat.le_of_lt_succ hlt
      have hlt' : s0 < k := Nat.lt_of_le_of_ne hle heq
      have ih' := ih hlt'
      have e : decide (f k = a) = decide (upd f s0 b k = a) := by
        have hne2 : k ≠ s0 := fun hcon => heq hcon.symm
        have u : upd f s0 b k = f k := upd_other hne2
        rw [u]
      simp only [zaehle, e, ih']
      ac_rfl

/-- Z-4, the other side: the NEW object's count rises by exactly one. -/
theorem zaehlung_steigt_um_eins {f : Nat → Nat} {s0 a b n : Nat}
    (hfa : f s0 = a) (hne : b ≠ a) (hlt : s0 < n)
    : zaehle (fun s => decide (upd f s0 b s = b)) n
      = zaehle (fun s => decide (f s = b)) n + 1 := by
  revert hlt
  induction n with
  | zero =>
    intro hlt
    exact absurd hlt (Nat.not_lt_zero _)
  | succ k ih =>
    intro hlt
    by_cases heq : s0 = k
    · have hcong : zaehle (fun s => decide (upd f s0 b s = b)) k
          = zaehle (fun s => decide (f s = b)) k := by
        apply zaehle_kongruent
        intro s hs
        have hne2 : s ≠ s0 := by
          intro hcon
          rw [hcon, heq] at hs
          exact absurd hs (Nat.lt_irrefl _)
        show decide (upd f s0 b s = b) = decide (f s = b)
        rw [upd_other hne2]
      have e1 : decide (upd f s0 b k = b) = true := by
        have huk : upd f s0 b k = b := by rw [← heq]; exact upd_self _ _ _
        simp [huk]
      have e2 : decide (f k = b) = false := by
        have hfk : f k = a := by rw [← heq]; exact hfa
        rw [hfk]
        exact decide_eq_false (fun hcon => hne hcon.symm)
      have s1 : zaehle (fun s => decide (upd f s0 b s = b)) (k + 1)
          = zaehle (fun s => decide (upd f s0 b s = b)) k + 1 := by simp [zaehle, e1]
      have s2 : zaehle (fun s => decide (f s = b)) (k + 1)
          = zaehle (fun s => decide (f s = b)) k := by simp [zaehle, e2]
      omega
    · have hle : s0 ≤ k := Nat.le_of_lt_succ hlt
      have hlt' : s0 < k := Nat.lt_of_le_of_ne hle heq
      have ih' := ih hlt'
      have e : decide (upd f s0 b k = b) = decide (f k = b) := by
        have hne2 : k ≠ s0 := fun hcon => heq hcon.symm
        have u : upd f s0 b k = f k := upd_other hne2
        rw [u]
      simp only [zaehle, e, ih']
      ac_rfl

/-- Z-5, the frame, and it is the most expensive of the three: every
    other count stays untouched. -/
theorem zaehlung_bleibt_sonst {f : Nat → Nat} {s0 a b c n : Nat}
    (hfa : f s0 = a) (hca : c ≠ a) (hcb : c ≠ b)
    : zaehle (fun s => decide (upd f s0 b s = c)) n
      = zaehle (fun s => decide (f s = c)) n := by
  apply zaehle_kongruent
  intro s _
  by_cases heq : s = s0
  · have e1 : decide (upd f s0 b s = c) = false := by
      have u : upd f s0 b s = b := by rw [heq]; exact upd_self _ _ _
      rw [u]
      exact decide_eq_false (fun hcon => hcb hcon.symm)
    have e2 : decide (f s = c) = false := by
      have fs : f s = a := by rw [heq]; exact hfa
      rw [fs]
      exact decide_eq_false (fun hcon => hca hcon.symm)
    show decide (upd f s0 b s = c) = decide (f s = c)
    rw [e1, e2]
  · show decide (upd f s0 b s = c) = decide (f s = c)
    rw [upd_other heq]

/-- Z-6, the preservation statement a generator template would carry:
    if the bookkeeping holds for every object before, and the mutation
    writes the decrement and the increment, it holds after again.
    `z` is `objects.slots[o].counter`, `f` is `slots[s].object`. -/
theorem buchfuehrung_erhaelt {z f : Nat → Nat} {n s0 a b : Nat}
    (vorher : ∀ ob, z ob = zaehle (fun s => decide (f s = ob)) n)
    (hschranke : s0 < n) (halt : f s0 = a) (hneu : b ≠ a)
    : ∀ ob, upd (upd z a (z a - 1)) b (z b + 1) ob
      = zaehle (fun s => decide (upd f s0 b s = ob)) n := by
  intro ob
  by_cases hea : ob = a
  · rw [hea]
    have hfall := zaehlung_faellt_um_eins halt hneu hschranke
    have hz : z a - 1 = zaehle (fun s => decide (upd f s0 b s = a)) n := by
      rw [vorher a, hfall]
      exact Nat.add_sub_cancel _ _
    have u1 : upd (upd z a (z a - 1)) b (z b + 1) a = z a - 1 := by
      have e : upd (upd z a (z a - 1)) b (z b + 1) a = upd z a (z a - 1) a :=
        upd_other (Ne.symm hneu)
      rw [e]
      exact upd_self _ _ _
    rw [u1, hz]
  · by_cases heb : ob = b
    · rw [heb]
      have hsteig := zaehlung_steigt_um_eins halt hneu hschranke
      have u1 : upd (upd z a (z a - 1)) b (z b + 1) b = z b + 1 :=
        upd_self _ _ _
      rw [u1, vorher b]
      exact hsteig.symm
    · have hrahmen : zaehle (fun s => decide (upd f s0 b s = ob)) n
          = zaehle (fun s => decide (f s = ob)) n :=
        zaehlung_bleibt_sonst halt hea heb
      have u1 : upd (upd z a (z a - 1)) b (z b + 1) ob = z ob := by
        have e1 : upd (upd z a (z a - 1)) b (z b + 1) ob
            = upd z a (z a - 1) ob := upd_other heb
        have e2 : upd z a (z a - 1) ob = z ob := upd_other hea
        rw [e1, e2]
      rw [u1, vorher ob]
      exact hrahmen.symm

/-! ## Part III -- the COST, counted instead of estimated -/

/-- The inner loop's steps: one per slot considered. -/
def schritte : Nat → Nat
  | 0 => 0
  | n + 1 => schritte n + 1

theorem schritte_der_inneren (n : Nat) : schritte n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [schritte, ih]

/-- Z-7: the outer loop over `m` objects, the inner over `n` slots. -/
def doppelt : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => doppelt k n + schritte n

theorem doppelte_schleife_kostet_produkt (m n : Nat) : doppelt m n = m * n := by
  induction m with
  | zero => simp [doppelt]
  | succ k ih => simp [doppelt, ih, schritte_der_inneren, Nat.succ_mul]

/-- Z-8: so `cost O(n)` on such an invariant is wrong, as a
    counterexample and not as a claim. -/
theorem doppelt_ist_mehr_als_einfach {m n : Nat} (hm : 1 < m) (hn : 0 < n) :
    schritte n < doppelt m n := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 + k := ⟨m - 2, by omega⟩
  rw [doppelte_schleife_kostet_produkt, schritte_der_inneren, Nat.add_mul]
  have e : 2 * n = n + n := by omega
  rw [e]
  have hnn : n + n ≤ n + n + k * n := Nat.le_add_right _ _
  omega

/-! ## Part IV -- the boundaries, as COUNTEREXAMPLE -/

/-- G-1: without `s0 < n` the preservation falls, and it falls on
    exactly that. One slot (`n = 1`), slot `1` rewritten -- outside.
    The object's count stays put while a generated counter would have
    moved. -/
theorem erhaltung_faellt_ohne_schranke :
    zaehle (fun s => decide (upd (fun _ => 0) 1 1 s = 0)) 1
      = zaehle (fun s => decide ((fun _ => 0) s = 0)) 1 := by
  decide

/-- G-2: the count says nothing about OCCUPANCY. It counts every slot
    naming the object, used or not. -/
theorem belegung_ist_nicht_mitgezaehlt :
    zaehle (fun _ => decide ((0 : Nat) = 0)) 2 = 2 ∧
    zaehle (fun s => decide ((0 : Nat) = 0 ∧ (fun _ => False) s)) 2 = 0 := by
  decide

/-! ## Witnesses: the constant table over two slots.

`f` names object `0` everywhere; slot `0` is rewritten to `1`. -/

theorem zaehle_kongruent_zeuge :
    zaehle (fun _ => (true : Bool)) 2 = zaehle (fun _ => (true : Bool)) 2 :=
  zaehle_kongruent (fun _ _ => rfl)

theorem zaehlung_faellt_um_eins_zeuge (h : 0 < 2) :
    zaehle (fun s => decide ((fun _ => 0) s = 0)) 2
      = zaehle (fun s => decide (upd (fun _ => 0) 0 1 s = 0)) 2 + 1 :=
  zaehlung_faellt_um_eins rfl (by decide) h

theorem zaehlung_steigt_um_eins_zeuge (h : 0 < 2) :
    zaehle (fun s => decide (upd (fun _ => 0) 0 1 s = 1)) 2
      = zaehle (fun s => decide ((fun _ => 0) s = 1)) 2 + 1 :=
  zaehlung_steigt_um_eins rfl (by decide) h

theorem zaehlung_bleibt_sonst_zeuge :
    zaehle (fun s => decide (upd (fun _ => 0) 0 1 s = 7)) 2
      = zaehle (fun s => decide ((fun _ => 0) s = 7)) 2 :=
  zaehlung_bleibt_sonst rfl (by decide) (by decide)

theorem buchfuehrung_erhaelt_zeuge (h : 0 < 2) :
    upd (upd (fun ob => if ob = 0 then 2 else 0) 0
        ((fun ob => if ob = 0 then 2 else 0) 0 - 1)) 1
      (((fun ob => if ob = 0 then 2 else 0)) 1 + 1) 0
      = zaehle (fun s => decide (upd (fun _ => 0) 0 1 s = 0)) 2 := by
  have vorher : ∀ ob, (fun ob => if ob = 0 then 2 else 0) ob
      = zaehle (fun s => decide ((fun _ => (0 : Nat)) s = ob)) 2 := by
    intro ob
    by_cases hob : ob = 0
    · subst hob
      decide
    · have hz : zaehle (fun s => decide ((fun _ => (0 : Nat)) s = ob)) 2 = 0 := by
        have c := zaehle_kongruent (P := (fun s => decide ((fun _ => (0 : Nat)) s = ob)))
          (Q := fun _ => false) (n := 2)
          (fun s _ => decide_eq_false (fun hcon => hob hcon.symm))
        rw [c]
        decide
      show (if ob = 0 then 2 else 0) = _
      rw [if_neg hob, hz]
  exact buchfuehrung_erhaelt (z := (fun ob => if ob = 0 then 2 else 0))
    (f := fun _ => 0) vorher h rfl (by decide) 0

end Gabbro.Grammatik.TableZaehlung
