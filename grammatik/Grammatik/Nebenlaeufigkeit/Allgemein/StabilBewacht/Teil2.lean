module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.InterferenzAllgemein
public import Grammatik.Korpus.Referenz.ReferenzB
public import Grammatik.Nebenlaeufigkeit.Allgemein.StabilBewacht.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

/-- Per-step rely on the witness chain: the guarded slot-5 write leaves
    `Q`'s slots 0 and 1 alone. (Guard, holdings, and disequality carried
    for shape; agreement is by computation.) -/
theorem zbRelyT : ∀ (f : Faden), f ∈ zbJ.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World refD),
    g ∈ zbJ.faeden → g ≠ f → zbJ.schrittFaden[k]? = some g →
      zbJ.welten[k]? = some vor → zbJ.welten[k + 1]? = some nach →
      ∀ (t : refD.Tab) (k' : Int) (fld : refD.Feld t),
        zbSf f t k' fld → refD.schreibt (zbCode g) t = true →
        ∀ (L : refD.Lock), Bewacht (D := refD) (.inl t) L → L ∈ refD.haelt (zbCode f) →
          L ∈ refD.haelt (zbCode g) → nach.slots t k' fld = vor.slots t k' fld := by
  intro f hf k g vor nach hgm hne hk hv hn t k' fld hSf hwrite L hL hLf hLg
  rw [zbJ_schritt] at hk
  rw [zbJ_welten] at hv hn
  cases k with
  | zero =>
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one, getElem?_pos,
  List.getElem_cons_zero, Option.some.injEq, Nat.reduceAdd, Nat.zero_lt_succ, List.getElem_cons_succ] at hk hv hn
    subst hv
    subst hn
    obtain ⟨rfl, hk' | hk'⟩ := hSf
    · subst hk'
      show (if (0 : Int) = 5 then zbV7 else zbV0) = zbV0
      rw [if_neg (by decide)]
    · subst hk'
      show (if (1 : Int) = 5 then zbV7 else zbV0) = zbV0
      rw [if_neg (by decide)]
  | succ k => simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff, Nat.add_eq_zero_iff,
  Nat.succ_ne_self, and_false, not_false_eq_true, getElem?_neg, reduceCtorEq] at hk

/-- No globals exist, so the global rely holds vacuously. (Premises
    carried for shape.) -/
theorem zbRelyG : ∀ (f : Faden), f ∈ zbJ.faeden → ∀ (k : Nat) (g : Faden) (vor nach : World refD),
    g ∈ zbJ.faeden → g ≠ f → zbJ.schrittFaden[k]? = some g →
      zbJ.welten[k]? = some vor → zbJ.welten[k + 1]? = some nach →
      ∀ x : refD.Glob, zbGf f x = true → refD.gschreibt (zbCode g) x = true →
        ∀ (L : refD.Lock), Bewacht (D := refD) (.inr x) L → L ∈ refD.haelt (zbCode f) →
          L ∈ refD.haelt (zbCode g) → nach.globs x = vor.globs x := by
  intro f hf k g vor nach hgm hne hk hv hn x hx hwrite L hL hLf hLg
  exact nomatch x

/-- The witness step really wrote slot 5. -/
theorem zbW1_slot5 : zbW1.slots () 5 () = zbV7 := by
  show (if (5 : Int) = 5 then zbV7 else zbV0) = zbV7
  rw [if_pos rfl]

/-- Slot 5 was `0` at the head. -/
theorem zbW0_slot5 : zbW0.slots () 5 () = zbV0 := by rfl

/-- Memory really moved: slot 5 reads `7`, the head reads `0`. -/
theorem zbMemMoved : zbW1.slots () 5 () ≠ zbW0.slots () 5 () := by
  intro hcon
  rw [zbW1_slot5, zbW0_slot5] at hcon
  have hn := congrArg Zahl.n hcon
  simp only [zbV7, zbV0, Int.reduceEq] at hn

/-- A function of the witness writes the shared table. -/
theorem zbSchreibt : TraegerSchreibt (zbCode 1) (.inl ()) = true :=
  zbSchreibtEin

/-- **Inhabitation for `stabil_ohne_form`.** All premises hold jointly on
    the two-thread witness chain: head validity, own-step and foreign-step
    preservation of `slot 0 = slot 1` -- plus non-degeneracy (a function
    writes the shared table; the step moves slot 5). -/
theorem stabil_ohne_form_zeuge :
    (∀ f ∈ zbJ.faeden, ∀ (k : Nat) (σ : World refD),
      zbJ.welten[k]? = some σ → zbQ f σ) ∧
    TraegerSchreibt (zbCode 1) (.inl ()) = true ∧
    zbW1.slots () 5 () ≠ zbW0.slots () 5 () :=
  ⟨stabil_ohne_form zbNb zbJ zbQ zbKopf zbEigen zbStabil,
    zbSchreibt, zbMemMoved⟩

/-- **Inhabitation for `stabil_aus_bewachung`.** All premises hold jointly
    on the witness chain: slot dependence, the static guard guarantee, the
    per-step rely -- plus the derived checker shape (`HaengtAb`) and
    non-degeneracy (a function writes the shared table; the step moves
    slot 5 while `Q` reads slots 0 and 1). -/
theorem stabil_aus_bewachung_zeuge :
    (∀ f ∈ zbJ.faeden, ∀ (k : Nat) (g : Faden) (vor nach : World refD),
      g ∈ zbJ.faeden → g ≠ f → zbJ.schrittFaden[k]? = some g →
        zbJ.welten[k]? = some vor → zbJ.welten[k + 1]? = some nach →
        zbQ f vor → zbQ f nach) ∧
    (∀ f ∈ zbJ.faeden, HaengtAb (zbWf f) (zbGf f) (zbQ f)) ∧
    TraegerSchreibt (zbCode 1) (.inl ()) = true ∧
    zbW1.slots () 5 () ≠ zbW0.slots () 5 () :=
  ⟨stabil_aus_bewachung zbNb zbJ zbQ zbSf zbGf zbDep zbWacheT zbWacheG zbRelyT zbRelyG,
    haengtAb_aus_slotDep zbNb zbJ zbQ zbSf zbWf zbGf zbDep zbCover,
    zbSchreibt, zbMemMoved⟩

/-! ## CUTS: what is not proved here

  (S1) Table-level `HaengtAb` alone does not suffice for `hStabil`, and is
    therefore not the working premise: a foreign write to another slot of
    the same table breaks table-level frame agreement while preserving `Q`,
    so no theorem from table-level `HaengtAb` plus the guard story alone can
    conclude foreign-step preservation without slot information. The slot
    read-set `Sf` (checker-computable in principle, like `orte`) and the
    slot-level dependence/rely are the unavoidable extra premises; table
    `HaengtAb` is derived (`haengtAb_aus_slotDep`), not assumed.
  (S2) No mutual exclusion is derived: the rely (a guarded foreign write
    leaves `Q`'s slots alone in this step) arrives per step and is not
    proved from the guard -- the model has no mutual-exclusion theorem over
    `haelt` lists (`LesenStabil` L1 carries over). The guarantee (foreign
    writes only under a co-held guard) is static and checker-dischargeable;
    the rely is memory-level slot agreement, checker-comparable per run.
    What the theorems remove is assertion-level per-step reasoning.
  (S3) One direction only: stability never concludes the backward leg, so
    break-and-restore across a step stays excluded by shape (the `hBlattAll`
    B5 boundary).
  (S4) Own-step preservation (`hEigen`) is assumed, not executed (G7
    carries over): sequential-logic adequacy belongs to another lane.
  (S5) The witness is a single-step two-thread chain; `Q` (`slot 0 =
    slot 1`) stands for "my slot equals my local counter". That `Q` is not
    of invariant form is documented by shape (it constrains two slots while
    the table keeps changing elsewhere), not proved as a negation over all
    `TraegerInv`. The witness `Q`-assumptions are carried for exact shape
    match and discharged by computation on concrete worlds.
-/

#print axioms Gabbro.Grammatik.stabil_ohne_form_zeuge
#print axioms Gabbro.Grammatik.stabil_aus_bewachung_zeuge

end Gabbro.Grammatik
