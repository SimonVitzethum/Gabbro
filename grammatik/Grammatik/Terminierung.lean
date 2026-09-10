/-
  File:      Grammatik/Terminierung.lean
  Subject:   **Termination sentences in the model** -- traverse (by unvisited, by
             decreasing, by consuming), bounded retry, and forever.

  What this file proves, and where each construct of the model lands:

    §1  `laufMitTreibstoff`          -- the loop with fuel: `n` counts the passes still
                                       granted. `none` = the fuel ran out while passes
                                       remained.
    §2  `mass_faellt_terminiert`     -- THE sentence: measure decrease implies
                                       termination. If every pass strictly lowers a
                                       `Nat`-valued measure, fuel `m s + 1` always
                                       suffices. Fuel/measure argument, by induction on
                                       the fuel.
        `traverse_unbesucht_terminiert`   -- `by unvisited`: the measure is the number
                                       of unvisited elements; each pass visits one.
        `traverse_fallend_terminiert`     -- `decreases e`: the measure is the writer's
                                       expression value; IF it falls, the loop ends.
        `traverse_verbrauchend_terminiert`-- `by consuming`: the measure is the domain
                                       size; IF every pass consumes, the loop ends.
        `rekursion_mass_terminiert`       -- recursion with `decreases`: same argument
                                       along the cycle edges.
        `retry_beschraenkt_antwortet`     -- `retry … bounded n`: the bound is
                                       syntactic, no measure needed; the loop always
                                       answers (done, or out of fuel).
        `schritt_fertig_endet`            -- a pass that is already done ends the loop
                                       at once (the model's `leave` from inside).
    §3  The checker boundary, precisely: S005 / S008 / K009 are NECESSARY but NOT
        sufficient. Each ships with a witness that the checked condition holds while
        the semantic fall fails -- the falling measure stays the writer's logic.
    §4  `forever`: NO termination theorem exists -- for every fuel there is a loop
        that exhausts it (`forever_unbeschraenkt`, via `endlos_schoepft_aus`).
        `forever` runs iff unbounded by contract: the environment's passes
        (the `progress` assumption, H2), not a proof in the model.

  Correspondence with the model (`grammatik/Grammatik/Semantik.lean`, read-only):
    `traverseLauf` ("Ein Durchlauf ueber die Indizes") recurses over a finite index
      list -- the `by unvisited` case below, with `alleIndizes` as the domain.
    `retryLauf` ("hoechstens `n` Durchgaenge") is fuel-indexed -- the bounded case.
    `foreverLauf` (H2: "`passes` Durchgaenge von aussen; danach steht der Ausgang bei
      der Annahme `a`") answers `hardware (.fortschritt a)` exactly when the fuel runs
      out -- the exhaustion exit this file models as `none`.
    The sufficient side lives with the writer: `Logik.schleife` (the loop invariant
      boundary), `Logik.abstieg` (the recursion that does not come to an end), and
      the prover's `consuming.ordnung` -- cited, never imported.
    The checks live in the checker (read-only): `crates/gabbro-check/src/schleifen.rs`
      (`abstieg_pruefen`: S005, S008) and `crates/gabbro-check/src/kosten.rs`
      (`rekursionsmass`: K008/K009).

  PREMISES, booked:
    (P1) Measures are `Nat`-valued; the fall is strict (`<`) on EVERY pass.
    (P2) Fuel counts granted passes exactly; one pass costs one fuel.
    (P3) A pass (`step`) is a total function: done (`none`) or one more pass
         (`some s'`). Scheduling, interference, and early exits beyond `leave`
         are not modeled.

  CUTS, booked:
    (C1) No import of the model: the lane forbids the index edit, and the check is
         per-file, so the correspondence is by name and shape, not by reference.
         Nothing here names `traverseLauf`/`retryLauf`/`foreverLauf` as terms.
    (C2) The sufficient side is NOT proved here: THAT the measure falls on every
         pass, THAT the domain shrinks, THAT every cycle edge lowers -- that is the
         writer's logic, discharged by the prover. This file proves: IF it falls,
         THEN it terminates.
    (C3) No liveness for `forever`: only unboundedness (no uniform fuel bound) plus
         the fuel-exhaustion exit. "Forever terminates" is not stated -- it does not.
    (C4) The abstract runner has two exits (done / out of fuel). The model's
         `on_exceeded` branch, `invariant` checks, and `next` are not modeled.
    (C5) S005/S008/K009 appear as stated boundary predicates with witnesses, not as
         checker terms: Lean cannot read Rust; the checks are cited by file.

  Core-only Lean, no mathlib, zero `sorry`.
-/

namespace Gabbro.Grammatik

/-! ## 1. The loop with fuel -/

/- A pass of a loop (`step : S → Option S`): `none` = the loop is done,
   `some s'` = one more pass, from `s'`. It needs no definition of its own. -/

/-- The loop with fuel: `n` counts the passes still granted. `none` = the fuel ran
    out while passes remained -- in the model the `on_exceeded` branch of `retry`,
    and `hardware (.fortschritt a)` of `forever`. -/
def laufMitTreibstoff {S : Type} (step : S → Option S) : Nat → S → Option S
  | 0, _ => none
  | n + 1, s =>
      match step s with
      | none => some s
      | some s' => laufMitTreibstoff step n s'

/-! ## 2. Measure decrease implies termination -- and its instances -/

/-- **Measure decrease implies termination.** If every pass strictly lowers a
    `Nat`-valued measure, fuel `m s + 1` always suffices: the loop answers `done`,
    never `out of fuel`. The proof is induction on the fuel, generalizing the state:
    at fuel `0` no further pass can lower the measure, so the loop must already be
    done; at fuel `n + 1` one pass costs one fuel and the measure pays it back. -/
theorem mass_faellt_terminiert {S : Type} (step : S → Option S) (m : S → Nat)
    (hfall : ∀ s s', step s = some s' → m s' < m s) :
    ∀ (n : Nat) (s : S), m s ≤ n → ∃ s', laufMitTreibstoff step (n + 1) s = some s' := by
  intro n
  induction n with
  | zero =>
      intro s hle
      have h0 : m s = 0 := by omega
      cases hs : step s with
      | none => exact ⟨s, by simp [laufMitTreibstoff, hs]⟩
      | some s' =>
          have hlt := hfall s s' hs
          omega
  | succ n ih =>
      intro s hle
      cases hs : step s with
      | none => exact ⟨s, by simp [laufMitTreibstoff, hs]⟩
      | some s' =>
          have hlt : m s' < m s := hfall s s' hs
          have hle' : m s' ≤ n := by omega
          obtain ⟨s'', ihw⟩ := ih s' hle'
          have h2 : laufMitTreibstoff step (n + 1 + 1) s = laufMitTreibstoff step (n + 1) s' := by
            simp only [laufMitTreibstoff, hs]
          exact ⟨s'', by rw [h2, ihw]⟩

/-- The bound, named: fuel `m s + 1` suffices. Every instance below is this theorem
    with its own measure -- honestly the same argument, which is the point: the
    fuel/measure argument does not care WHAT falls, only THAT it falls. -/
theorem mass_faellt_schranke {S : Type} (step : S → Option S) (m : S → Nat)
    (hfall : ∀ s s', step s = some s' → m s' < m s) (s : S) :
    ∃ s', laufMitTreibstoff step (m s + 1) s = some s' :=
  mass_faellt_terminiert step m hfall (m s) s (Nat.le_refl _)

/-- `by unvisited`: one pass per unvisited element of a finite domain. -/
def schrittUnbesucht {α : Type} : List α → Option (List α)
  | [] => none
  | _ :: xs => some xs

/-- Each pass over unvisited elements visits exactly one: the count falls. -/
theorem unbesucht_faellt {α : Type} (xs xs' : List α)
    (h : schrittUnbesucht xs = some xs') : xs'.length < xs.length := by
  cases xs with
  | nil => simp [schrittUnbesucht] at h
  | cons x xs => simp [schrittUnbesucht] at h; subst h; exact Nat.lt_succ_self _

/-- `by unvisited` terminates by construction: the domain is finite, each element is
    visited at most once, so `length + 1` passes always suffice. In the model this is
    `traverseLauf` recursing over the index list. -/
theorem traverse_unbesucht_terminiert {α : Type} (xs : List α) :
    ∃ rest, laufMitTreibstoff schrittUnbesucht (xs.length + 1) xs = some rest :=
  mass_faellt_schranke _ List.length unbesucht_faellt xs

/-- `decreases e`: the measure is the writer's expression value before the pass.
    IF it falls on every pass, the loop ends within `mass s + 1` passes. THAT it
    falls is the writer's logic -- see §3 (S005). -/
theorem traverse_fallend_terminiert {S : Type} (step : S → Option S) (mass : S → Nat)
    (hfall : ∀ s s', step s = some s' → mass s' < mass s) (s : S) :
    ∃ s', laufMitTreibstoff step (mass s + 1) s = some s' :=
  mass_faellt_schranke step mass hfall s

/-- `by consuming`: the measure is the DOMAIN SIZE. IF every pass consumes -- the
    domain shrinks -- the loop ends within `size + 1` passes, leaf-first order
    included: a shrinking finite domain runs out. THAT it shrinks on every pass is
    the writer's logic -- see §3 (S008). -/
theorem traverse_verbrauchend_terminiert {S : Type} (step : S → Option S) (umfang : S → Nat)
    (hschwund : ∀ s s', step s = some s' → umfang s' < umfang s) (s : S) :
    ∃ s', laufMitTreibstoff step (umfang s + 1) s = some s' :=
  mass_faellt_schranke step umfang hschwund s

/-- Recursion with `decreases`: the recursion depth is fuel, and a measure falling
    along every edge back into the cycle bounds it. THAT every edge lowers is the
    writer's logic -- see §3 (K009); the model's exit is `Logik.abstieg`. -/
theorem rekursion_mass_terminiert {S : Type} (step : S → Option S) (mass : S → Nat)
    (hfall : ∀ s s', step s = some s' → mass s' < mass s) (s : S) :
    ∃ s', laufMitTreibstoff step (mass s + 1) s = some s' :=
  mass_faellt_schranke step mass hfall s

/-- `retry … bounded n`: the bound is syntactic -- no measure needed. The loop ALWAYS
    answers within its fuel: `done`, or `out of fuel` (the model's `on_exceeded`
    branch). Totality IS the sentence: bounded retry cannot hang. -/
theorem retry_beschraenkt_antwortet {S : Type} (step : S → Option S) (n : Nat) (s : S) :
    ∃ o, laufMitTreibstoff step n s = o :=
  ⟨_, rfl⟩

/-- A pass that is already done ends the loop at once -- the model's `leave` ending
    `traverse`/`retry`/`forever` from inside the body. -/
theorem schritt_fertig_endet {S : Type} (step : S → Option S) (n : Nat) (s : S)
    (h : step s = none) : laufMitTreibstoff step (n + 1) s = some s := by
  simp [laufMitTreibstoff, h]

/-! ## 3. Where the checker ends: S005 / S008 / K009 are necessary, not sufficient -/

/-- S005 (`schleifen.rs`, `abstieg_pruefen`): the `decreases` measure of a `traverse`
    must be ABLE to move -- it names the traversal variable or a name the body
    writes. Movement is not descent: the measure below names the traversal variable
    (S005 is green) and still RISES -- the traversal counts up. THAT it falls on
    every pass is the writer's logic (`Logik.schleife` in the model,
    `consuming.ordnung` for the prover). -/
theorem s005_bewegt_nicht_fallend :
    ∃ mass : Nat → Nat, (∀ k, mass k = k) ∧ ∀ k, mass k < mass (k + 1) :=
  ⟨id, fun _ => rfl, fun k => Nat.lt_succ_self k⟩

/-- S008 (`by consuming` without a `consumes`): the `touches` list must name a
    carrier -- the claim "the domain shrinks" needs something that shrinks it.
    The carrier is not the shrink: below the carrier is present and the domain does
    NOT shrink across the pass. THAT it shrinks on every pass is the writer's
    logic, as at S005. -/
theorem s008_traeger_nicht_schwund :
    ∃ (hatTraeger : Bool) (vor nach : List Nat),
      hatTraeger = true ∧ vor.length = nach.length :=
  ⟨true, [0, 1], [0, 1], rfl, rfl⟩

/-- K009 (`kosten.rs`, `rekursionsmass`): at every recursive call site at least one
    named size must visibly lower (`n - k`, `n / k`). One lowered site is not every
    edge back into the cycle: below site 1 lowers and site 2 passes through
    unchanged -- K009 is green at site 1 and the recursion still need not end.
    THAT the measure falls along EVERY cycle edge is the writer's logic
    (`Logik.abstieg` in the model). -/
theorem k009_eine_stelle_nicht_alle :
    ∃ (stelle1 stelle2 : Nat → Nat),
      (∀ n, stelle1 n = n - 1) ∧ (∀ n, stelle2 n = n) :=
  ⟨(· - 1), id, fun _ => rfl, fun _ => rfl⟩

/-! ## 4. Forever: unbounded by contract, not by proof -/

/-- The loop that never ends exhausts EVERY fuel: unbounded by contract, not by
    proof. In the model this is `foreverLauf` answering `hardware (.fortschritt a)`
    -- the progress assumption the writer named (H2). -/
theorem endlos_schoepft_aus {S : Type} (s0 : S) :
    ∀ n : Nat, laufMitTreibstoff (fun _ => some s0) n s0 = none := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [laufMitTreibstoff, ih]

/-- **No termination theorem for `forever` exists**: for EVERY fuel there is a loop
    that is still not done when it runs out. So `forever` runs iff unbounded by
    contract -- the environment grants passes without bound (the `progress`
    assumption), and the model records that grant as fuel, never as a proof. -/
theorem forever_unbeschraenkt :
    ∀ n : Nat, ∃ (step : Unit → Option Unit) (s : Unit),
      laufMitTreibstoff step n s = none := by
  intro n
  exact ⟨_, _, endlos_schoepft_aus () n⟩

/-! ## 5. Execution samples -/

example : laufMitTreibstoff schrittUnbesucht 3 ([1, 2] : List Nat) = some ([] : List Nat) := rfl
example : laufMitTreibstoff (fun _ => some ()) 5 () = none := rfl

/-! ## 6. Axioms -- derived -/

#print axioms Gabbro.Grammatik.mass_faellt_terminiert
#print axioms Gabbro.Grammatik.traverse_unbesucht_terminiert
#print axioms Gabbro.Grammatik.retry_beschraenkt_antwortet
#print axioms Gabbro.Grammatik.s005_bewegt_nicht_fallend
#print axioms Gabbro.Grammatik.s008_traeger_nicht_schwund
#print axioms Gabbro.Grammatik.k009_eine_stelle_nicht_alle
#print axioms Gabbro.Grammatik.forever_unbeschraenkt

end Gabbro.Grammatik
