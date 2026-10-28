/- Part 2 of 3 of `SchablonenT5` (split by instrumente/teile/lean-teilen.py; the umbrella `SchablonenT5.lean` imports all parts). -/
import Grammatik.Bausteine.Schablonen.SchablonenT5.T1

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

/-! ## 17. `state.reset` (reset: 9 corpus lines).

The generated transition into the initial state holds from every
state in which no linear value is held (`h`: the held-flag is down),
and is itself a `transset` (single move, no middle -- see §9). From a
state with a held linear value it is a leak and is rejected -- M2, not
this template (`reset_rejects_held`). Model: a value plus a
held-linear flag. -/

/-- The generated reset: clean states go home, holding states abort. -/
def treset (s : Nat × Bool) : Option (Nat × Bool) :=
  if s.2 then none else some (0, false)

/-- Soundness core of `state.reset`: total on clean states. `h` is
    consumed by the branch. -/
theorem reset_from_clean (s : Nat × Bool) (h : s.2 = false) :
    treset s = some (0, false) := by
  simp only [treset, h, Bool.false_eq_true, ↓reduceIte]

/-- The M2 side: a held linear value is rejected, not leaked. -/
theorem reset_rejects_held (v : Nat) : treset (v, true) = none :=
  rfl

/-- Witness for `reset_from_clean`: `(7, false)` goes home. -/
theorem reset_from_clean_zeuge :
    (treset (7, false) = some (0, false)) :=
  reset_from_clean _ rfl

/-! ## 18. `table.induktion` (induction: 3 corpus lines).

The induction scheme generated from the `table` declaration is
well-founded and complete: (N-1) chaining edges stay inside the table
(`hfin`: the predecessor bound, from `table.indexschranke` via
`M103`); (N-2) the principle holds for ONE state; (N-3) no
empty-set clause of its own -- the base case is absorbed (vacuous
predecessors discharge `hstep`); (N-4) for `chain(a,b) in` the domain
has TWO kinds of edge and the scheme takes TWO premises
(`e1`/`e2` both feed the step). Well-foundedness is a HYPOTHESIS
(`hwf`: the declaration names the carrying invariant), not a result.
`induct_edge_in_type` is the `im_bereich` direction of (N-1). -/

/-- Soundness core of `table.induktion`. `hfin` bounds predecessors,
    `hwf` carries accessibility, `hstep` is the two-premise step, `hx`
    puts the target in the carrier. All are consumed. -/
theorem table_induction (N : Nat) (e1 e2 : Nat → Nat → Prop)
    (hfin : ∀ a b, e1 a b ∨ e2 a b → a < N)
    (hwf : WellFounded (fun a b => e1 a b ∨ e2 a b))
    (P : Nat → Prop)
    (hstep : ∀ x, x < N → (∀ y, e1 y x ∨ e2 y x → P y) → P x)
    (x : Nat) (hx : x < N) : P x := by
  have key : ∀ z, Acc (fun a b => e1 a b ∨ e2 a b) z → z < N → P z := by
    intro z ha
    induction ha with
    | intro z _ ih =>
      intro hz
      exact hstep z hz (fun y hy => ih y hy (hfin y z hy))
  exact key x (hwf.apply x) hx

/-- The `im_bereich` direction: a chained edge lands in the type. -/
theorem induct_edge_in_type (N : Nat) (e1 e2 : Nat → Nat → Prop)
    (hfin : ∀ a b, e1 a b ∨ e2 a b → b < N)
    (a b : Nat) (h : e1 a b ∨ e2 a b) : b < N :=
  hfin a b h

/-- Witness for `table_induction`: successor edges below `2`, property
    `True`. -/
theorem table_induction_zeuge :
    (True)
:= by
  have hfin : ∀ a b : Nat,
      (a + 1 = b ∧ b < 2 ∨ False) → a < (refD.count ()).toNat := by
    intro a b h
    have h2 : (refD.count ()).toNat = 2 := rfl
    rw [h2]
    rcases h with h | h'
    · omega
    · contradiction
  have hsub : Subrelation (fun a b : Nat => a + 1 = b ∧ b < 2 ∨ False)
      (· < ·) := by
    intro a b h
    rcases h with h | h'
    · omega
    · contradiction
  have hwf : WellFounded (fun a b : Nat => a + 1 = b ∧ b < 2 ∨ False) :=
    Subrelation.wf hsub Nat.lt_wfRel.wf
  have hstep : ∀ x : Nat, x < (refD.count ()).toNat →
      (∀ y : Nat, (y + 1 = x ∧ x < 2 ∨ False) → True) → True := by
    intro x _ _
    trivial
  have hx : (0 : Nat) < (refD.count ()).toNat := by
    have h2 : (refD.count ()).toNat = 2 := rfl
    rw [h2]
    decide
  exact table_induction _ _ _ hfin hwf _ hstep 0 hx

/-! ## 20. `table.ops.erhaltung` (by-ops: `16-by-ops-am-feld.gab` plus
    the `by ops`/`maintains` corpus sites).

Per generated mutation every `online` invariant OF THIS CARRIER is
preserved -- once over the declaration, not per call site (`h`: each
generated operation preserves `inv`). Invariants ACROSS carriers are
expressly not covered; they are `gruppe.ops` (§16). What Lean checks
is the amortisation: a whole run of generated operations (`hr`: every
run step is generated) preserves the invariant from a good state
(`hs`). All three are consumed. -/

/-- Soundness core of `table.ops.erhaltung`: the declaration-level
    check covers every call-site run. -/
private theorem table_ops_keep_aux (S : Type) (inv : S → Prop)
    (ops : List (S → S))
    (h : ∀ op ∈ ops, ∀ s, inv s → inv (op s)) :
    ∀ (run : List (S → S)), (∀ op ∈ run, op ∈ ops) →
      ∀ (s : S), inv s → inv (run.foldl (fun acc op => op acc) s)
  | [], _, _s, hs => hs
  | op :: rest, hr, s, hs =>
    have hop : op ∈ ops := hr _ (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ _op' ∈ rest, _op' ∈ ops :=
      fun _op' hm => hr _ (List.mem_cons_of_mem _ hm)
    table_ops_keep_aux S inv ops h rest hrest (op s) (h _ hop _ hs)

theorem table_ops_keep (S : Type) (inv : S → Prop) (ops : List (S → S))
    (h : ∀ op ∈ ops, ∀ s, inv s → inv (op s))
    (run : List (S → S)) (hr : ∀ op ∈ run, op ∈ ops)
    (s : S) (hs : inv s) :
    inv (run.foldl (fun acc op => op acc) s) :=
  table_ops_keep_aux S inv ops h run hr s hs

/-- Witness for `table_ops_keep`: operations `[+1, *2]` keep
    nonnegativity along the run. -/
theorem table_ops_keep_zeuge :
    ((0 : Nat) ≤ ([(· + 1), (· * 2)] : List (Nat → Nat)).foldl
      (fun acc op => op acc) 0)
:= by
  have h : ∀ op ∈ ([(· + 1), (· * 2)] : List (Nat → Nat)),
      ∀ s : Nat, 0 ≤ s → 0 ≤ op s := by
    intro op hop s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl <;> simp_all <;> omega
  have hr : ∀ op ∈ ([(· + 1), (· * 2)] : List (Nat → Nat)),
      op ∈ ([(· + 1), (· * 2)] : List (Nat → Nat)) := by
    intro op hop
    exact hop
  exact table_ops_keep Nat (fun s => 0 ≤ s) _ h _ hr 0 (Nat.zero_le 0)

/-! ## 21. `ops.suche` (candidate from «B10»: no corpus use yet).

The generated search returns the first hit in a GENERATED, NAMED
enumeration order (`hpre`: everything before the hit misses; `hpx`:
the hit hits) and leaves the set unchanged (the search is pure: the
fst-projection is the input list). For domains with several kinds of
edge the order has to be fixed on top -- it does not fall out of the
domain (booked in CUTS). -/

/-- The generated search: input list plus first hit. -/
def opSearch : List Nat → (Nat → Bool) → List Nat × Option Nat
  | [], _ => ([], none)
  | x :: xs, p =>
    if p x then (x :: xs, some x)
    else (x :: (opSearch xs p).1, (opSearch xs p).2)

/-- The search leaves every list unchanged. -/
private theorem op_search_keeps_all :
    ∀ (xs : List Nat) (p : Nat → Bool), (opSearch xs p).1 = xs
  | [], _ => rfl
  | y :: ys, p => by
    simp only [opSearch]
    split
    · rfl
    · rw [op_search_keeps_all ys p]

/-- The search leaves the set unchanged. -/
theorem op_search_keeps (pre : List Nat) (x : Nat) (post : List Nat)
    (p : Nat → Bool) :
    (opSearch (pre ++ [x] ++ post) p).1 = pre ++ [x] ++ post :=
  op_search_keeps_all _ _

/-- The search returns the first hit. `hpre`/`hpx` are both consumed. -/
theorem op_search_first (pre : List Nat) (x : Nat) (post : List Nat)
    (p : Nat → Bool)
    (hpre : ∀ y ∈ pre, p y = false) (hpx : p x = true) :
    (opSearch (pre ++ [x] ++ post) p).2 = some x := by
  induction pre with
  | nil =>
    show (opSearch ([x] ++ post) p).2 = some x
    simp only [List.cons_append, List.nil_append, opSearch, hpx, ↓reduceIte]
  | cons y ys ih =>
    have hy : p y = false := hpre _ (List.mem_cons.mpr (Or.inl rfl))
    have hrest : ∀ z ∈ ys, p z = false :=
      fun z hz => hpre z (List.mem_cons_of_mem _ hz)
    have hys := ih hrest
    show (opSearch ((y :: ys) ++ [x] ++ post) p).2 = some x
    simp only [show (y :: ys) ++ [x] ++ post = y :: (ys ++ [x] ++ post) from rfl,
      opSearch, hy]
    exact hys

/-- Witness for the `ops.suche` pair: searching `[1, 3, 2, 4]` for an
    even number returns `2` and keeps the list. -/
theorem op_search_zeuge :
    ((opSearch ([1, 3] ++ [2] ++ [4]) (fun n => n == 2)).1 = [1, 3, 2, 4] ∧
      (opSearch ([1, 3] ++ [2] ++ [4]) (fun n => n == 2)).2 = some 2)
:= by
  have hpre : ∀ y ∈ ([1, 3] : List Nat), (y == 2) = false := by decide
  have hpx : ((2 : Nat) == 2) = true := rfl
  exact ⟨op_search_keeps _ _ _ _,
    op_search_first _ _ _ _ hpre hpx⟩

/-! ## 19. `restrict.alleinzugriff` (restrict: 5 corpus lines).

UNDER H1 (the frame is COMPLETE -- every access of the body has a
root from the declared set: in the model an access IS a rooted pair,
so H1 holds by construction, established checker-side by `E008`/`E010`)
and H2 (no other root meets the same place: at most ONE pointer
parameter per carrier type, syntactically -- `emit::darf_restrict` --
and no pointer to a global table formable in the language): every
access to the object behind `p` runs through `p`, so the C11-6.7.3.1
condition holds. -/

/-- Soundness core of `restrict.alleinzugriff`: two accesses meeting
    at one place share the one root. `hOnly` (H2) is consumed twice;
    `h1`/`h2` fix the two accesses. -/
theorem single_root (q : Nat) (reach : Nat → Nat → Prop) (p r1 r2 : Nat)
    (hOnly : ∀ r, reach r q → r = p) (h1 : reach r1 q)
    (h2 : reach r2 q) : r1 = r2 := by
  rw [hOnly _ h1, hOnly _ h2]

/-- Witness for `single_root`:     both accesses run through root `7`. -/
theorem single_root_zeuge :
    ((7 : Nat) = 7)
:= by
  have hOnly : ∀ r, (r = 7 ∧ (0 : Nat) = 0) → r = 7 := by
    intro r hr
    exact hr.1
  have h1 : (7 : Nat) = 7 ∧ (0 : Nat) = 0 := ⟨rfl, rfl⟩
  exact single_root 0 (fun r qq => r = 7 ∧ qq = 0) 7 7 7 hOnly h1 h1


end Gabbro.Grammatik
