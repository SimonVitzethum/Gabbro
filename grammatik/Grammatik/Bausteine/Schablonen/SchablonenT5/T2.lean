/- Part 2 of 3 of `SchablonenT5` (split by instrumente/teile/lean-teilen.py; the umbrella `SchablonenT5.lean` imports all parts). -/
module
public import Grammatik.Bausteine.Schablonen.SchablonenT5.T2Basis
import all Grammatik.Bausteine.Schablonen.SchablonenT5.T2Basis
public import Grammatik.Bausteine.Schablonen.SchablonenT5.T1
@[expose] public section


namespace Gabbro.Grammatik
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
  by rfl

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

/-! ## 20. `table.ops.erhaltung` (by-ops: `0016-by-ops-am-feld.gab` plus
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
