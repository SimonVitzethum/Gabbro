/- Part 2 of 3 of `SchablonenT5` (split by instrumente/teile/lean-teilen.py; the umbrella `SchablonenT5.lean` imports all parts). -/
module
public import Grammatik.Bausteine.Schablonen.SchablonenT5.T1
@[expose] public section


namespace Gabbro.Grammatik

/-! ## 11. `accumulates.monoid` (accumulates: 23 corpus lines).

The merge set is a commutative monoid (mechanically checkable: the
closed `MergeOp` vocabulary over integral types). What Lean checks is
the order-independence core (`faltung_ist_reihenfolgeunabhaengig`):
under associativity (`hassoc`) and commutativity (`hcomm`) the fold
does not see adjacent swaps -- hence no interleaving. The quiescent
point (`am_ruhepunkt_gleich_dem_atomaren_rmw`) and the per-operator
units (`min` starts at the type maximum) are booked in CUTS. -/

/-- Soundness core of `accumulates.monoid`: adjacent swaps leave the
    fold unchanged. `hassoc`/`hcomm` are both consumed. -/
theorem merge_swap_invariant (op : Nat → Nat → Nat)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c))
    (hcomm : ∀ a b, op a b = op b a)
    (xs ys : List Nat) (a b s : Nat) :
    (xs ++ [a, b] ++ ys).foldl (fun t x => op t x) s =
    (xs ++ [b, a] ++ ys).foldl (fun t x => op t x) s := by
  have key : ∀ t, op (op t a) b = op (op t b) a := by
    intro t
    rw [hassoc, hcomm a b, ← hassoc]
  simp only [List.foldl_append]
  have h2 : ([a, b] : List Nat).foldl (fun t x => op t x)
        (xs.foldl (fun t x => op t x) s) =
      ([b, a] : List Nat).foldl (fun t x => op t x)
        (xs.foldl (fun t x => op t x) s) :=
    key _
  rw [h2]

/-- Witness for `merge_swap_invariant`: addition folds `[1, 2]` and
    `[2, 1]` to the same value. -/
theorem merge_swap_invariant_zeuge :
    (([1, 2] : List Nat).foldl (fun t x => t + x) 0 =
      ([2, 1] : List Nat).foldl (fun t x => t + x) 0)
:= by
  have h := merge_swap_invariant (· + ·) Nat.add_assoc Nat.add_comm
    ([] : List Nat) [] 1 2 0
  exact h

/-! ## 12. `walk.mappings` (mappings: 23 corpus lines).

The generated domain `mappings of` meets every reachable entry that
CARRIES a mapping -- together with va and level. That is not the same
as `leaf entry`: a large page maps above the full depth. The meeting
holds BY CONSTRUCTION of the domain (filter); whether the generator
builds that filter -- and whether it meets large pages -- is the open
half, booked in CUTS. -/

/-- A page-table entry: address, level, and whether it carries a mapping. -/
def ptEntry : Type := Nat × Nat × Bool

/-- It carries a mapping (possibly above the full depth). -/
def carriesMapping (e : ptEntry) : Bool := e.2.2

/-- The generated domain: every entry that carries a mapping. -/
def mappingsOf (entries : List ptEntry) : List ptEntry :=
  entries.filter carriesMapping

/-- Soundness core of `walk.mappings`: a carried mapping is met.
    `hmem`/`hcar` are both consumed. -/
theorem walk_hits_mapping (entries : List ptEntry) (e : ptEntry)
    (hmem : e ∈ entries) (hcar : carriesMapping e = true) :
    e ∈ mappingsOf entries :=
  List.mem_filter.mpr ⟨hmem, hcar⟩

/-- Witness for `walk_hits_mapping`:     entry `(7, 1, true)` is met. -/
theorem walk_hits_mapping_zeuge :
    ((7, 1, true) ∈ mappingsOf [(7, 1, true), (8, 2, false)])
:= by
  have hmem : ((7, 1, true) : ptEntry) ∈ [(7, 1, true), (8, 2, false)] := by
    decide
  have hcar : carriesMapping (7, 1, true) = true := rfl
  exact walk_hits_mapping _ _ hmem hcar

/-! ## 13. `consuming.ordnung` (consuming: 13 corpus lines).

The domain delivers its witnesses in the generated well-founded
order. Under the REMOVAL of the visited witness the order is
preserved -- the edge set shrinks (`wf_subset` at list level: what
remains was there), and consumption strictly drops the domain measure,
so the traversal terminates. Leaf status at the moment of consumption
does NOT follow -- it additionally requires the choice to be MINIMAL
(`waehlt_minimal`, owed by the witness-order generator). -/

/-- Soundness core of `consuming.ordnung`: removal shrinks the domain
    (`hrem`: the consumed witness is gone from the rest is NOT needed --
    only the membership `hmem` in the remainder) and drops its measure
    (`ha`: the consumed witness was there). Both are consumed. -/
theorem consume_shrinks (domain : List Nat) (a x : Nat)
    (hmem : x ∈ domain.erase a) (ha : a ∈ domain) :
    x ∈ domain ∧ (domain.erase a).length < domain.length := by
  have hpos : 0 < domain.length := by
    cases he : domain with
    | nil =>
      rw [he] at ha
      exact absurd ha List.not_mem_nil
    | cons _ _ => exact Nat.zero_lt_succ _
  exact ⟨List.mem_of_mem_erase hmem,
    by rw [List.length_erase_of_mem ha]; omega⟩

/-- Witness for `consume_shrinks`: consuming `1` out of `[0, 1]`
    leaves `[0]` present and shorter. -/
theorem consume_shrinks_zeuge :
    ((0 : Nat) ∈ [0, 1] ∧ (([0, 1] : List Nat).erase 1).length < [0, 1].length)
:= by
  have hmem : (0 : Nat) ∈ ([0, 1] : List Nat).erase 1 := by decide
  have ha : (1 : Nat) ∈ ([0, 1] : List Nat) := by decide
  exact consume_shrinks _ 1 0 hmem ha

/-! ## 14. `consuming.leermenge`.

The generated witness set is COMPLETE at a NAMED state (`hC`: every
domain element at that state is witnessed) -- if it is empty there
(`hempty`), the domain is empty there. Without the named state the
sentence is ambiguous in a consuming traversal
(`leermenge_ist_zustandsabhaengig`). -/

/-- Soundness core of `consuming.leermenge`. The named state is the
    explicit pair `(domain, wit)`; `hC`/`hempty` are both consumed. -/
theorem consume_empty_at (domain wit : List Nat)
    (hC : ∀ x ∈ domain, x ∈ wit) (hempty : wit = []) :
    domain = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro x hx
  have h := hC x hx
  rw [hempty] at h
  exact absurd h List.not_mem_nil

/-- Witness for `consume_empty_at`:     empty witnesses over `[]`. -/
theorem consume_empty_at_zeuge :
    (([] : List Nat) = [])
:= by
  have hC : ∀ x ∈ ([] : List Nat), x ∈ ([] : List Nat) := by
    intro x hx
    contradiction
  exact consume_empty_at [] [] hC rfl

/-! ## 15. `consuming.umhaengen` (the refuted blanket version).

A generated mutation that ADDS edges preserves well-foundedness -- and
that is NOT covered by `wf_subset`; it has to be shown per mutation.
The blanket version is REFUTED, not open
(`umhaengen_kann_zyklus_erzeugen`): one re-hang turns the acyclic edge
`(0, 1)` into a self-loop. What Lean exhibits is that loop. -/

/-- Re-hang the head edge's target. -/
def rehang (edges : List (Nat × Nat)) (a b c : Nat) : List (Nat × Nat) :=
  (edges.erase (a, b)) ++ [(a, c)]

/-- The refutation exhibit: re-hanging `(0, 1)` onto `0` leaves the
    self-loop `(0, 0)` -- a cycle from one move. -/
theorem rehang_can_cycle : (0, 0) ∈ rehang [(0, 1)] 0 1 0 := by
  decide

/-- Witness for `rehang_can_cycle`: the loop exhibit. -/
theorem rehang_can_cycle_zeuge :
    ((0, 0) ∈ rehang [(0, 1)] 0 1 0) :=
  rehang_can_cycle

/-! ## 16. `gruppe.ops` (group: 10 corpus lines).

The connecting invariant of the group is preserved under every group
operation. The lock footprint under which that holds does NOT stand
here but in `gruppe.sperrabdruck` -- this template presupposes it
(the `lock_order_no_reentry` half above). What Lean checks is the
composition core: two footprint-covered group operations that each
preserve the link (`h1`/`h2`) preserve it in sequence. (The
single-carrier operations that BREAK a connecting invariant --
`verbindung_nicht_gedeckt` -- are exactly why this entry exists.) -/

/-- Soundness core of `gruppe.ops`: preservation composes. `h1`/`h2`
   /`hp` are all consumed. -/
theorem group_ops_compose (A B : Type) (link : A → B → Prop)
    (g1 g2 : A × B → A × B)
    (h1 : ∀ p, link p.1 p.2 → link (g1 p).1 (g1 p).2)
    (h2 : ∀ p, link p.1 p.2 → link (g2 p).1 (g2 p).2)
    (p : A × B) (hp : link p.1 p.2) :
    link (g2 (g1 p)).1 (g2 (g1 p)).2 :=
  h2 _ (h1 _ hp)

/-- Witness for `group_ops_compose`: the equality link over `Nat`
    survives `(+1, +1)` then `(*2, *2)`. -/
theorem group_ops_compose_zeuge :
    ((12 : Nat) = 12)
:= by
  have h1 : ∀ p : Nat × Nat, p.1 = p.2 →
      ((fun q : Nat × Nat => (q.1 + 1, q.2 + 1)) p).1 =
      ((fun q : Nat × Nat => (q.1 + 1, q.2 + 1)) p).2 := by
    intro p hp
    simp only []
    omega
  have h2 : ∀ p : Nat × Nat, p.1 = p.2 →
      ((fun q : Nat × Nat => (q.1 * 2, q.2 * 2)) p).1 =
      ((fun q : Nat × Nat => (q.1 * 2, q.2 * 2)) p).2 := by
    intro p hp
    simp only []
    omega
  exact group_ops_compose Nat Nat (fun a b => a = b)
    (fun q : Nat × Nat => (q.1 + 1, q.2 + 1))
    (fun q : Nat × Nat => (q.1 * 2, q.2 * 2)) h1 h2 (5, 5) rfl


end Gabbro.Grammatik
