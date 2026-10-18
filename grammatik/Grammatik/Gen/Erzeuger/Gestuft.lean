/-
  File:      Grammatik/Gen/Erzeuger/Gestuft.lean
  Subject:   The FRAME of the size-stratified generator: `Sz α`, the items of EXACT size `k` for every `k`, with
             the combinators the clauses are written in (`bind` adds sizes, `knoten` costs one, `wahl` is a free
             finite choice), and the NUMERIC SCHEME (`Zahlen`): what a free number (a literal, a bound, a width, a
             count) costs and which numbers cost what.

  WHY EXACT SIZE. A generator by fuel builds every term of depth `m` from every term of depth `m - 1`, so its
  lists contain terms of size exponential in `m`, and each step squares the list (measured: 9, 142, ~10^5,
  killed). Here a term of size `k` is built from parts whose sizes SUM to `k - 1`: `bind A F k` runs over the
  splits `i + (k - i)`, so the work is proportional to the number of terms of that size and nothing else.

  THE NUMERIC SCHEME is the one place where the statement is parametrised. `exakt M` costs a number by its
  magnitude (`|n|` for `|n| ≤ M`, infinity beyond): the statement of the first generator. `kanon N` costs the
  numbers of a finite alphabet `N` one each and every other number infinity: the reduction "constants folded to
  the boundary values of the declaration". A theorem about a size bound below `unendlich` therefore speaks only of
  programs whose numbers the scheme names; this is stated, not hidden.
-/
import Grammatik.Gen.Erzeuger.Grund

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik

set_option warn.classDefReducibility false

/-- The cost of a number the scheme does not name. Every size bound of a theorem is below it. -/
def unendlich : Nat := 1000000000

/-- **The numeric scheme**: the cost of a free integer / natural number and the numbers of each cost. -/
class Zahlen where
  kost : Int → Nat
  liste : Nat → List Int
  mem : ∀ n, kost n < unendlich → n ∈ liste (kost n)
  kostN : Nat → Nat
  listeN : Nat → List Nat
  memN : ∀ n, kostN n < unendlich → n ∈ listeN (kostN n)
  /-- The pairs of integers (the bounds of a float type) with their cost. -/
  kostP : Int × Int → Nat
  listeP : Nat → List (Int × Int)
  memP : ∀ p, kostP p < unendlich → p ∈ listeP (kostP p)

/-- Numbers by magnitude, up to `M` (costs `|n|`; a natural number costs itself). -/
def Zahlen.exakt (M : Nat) : Zahlen where
  kost n := if n.natAbs ≤ M then n.natAbs else unendlich
  liste c := if c = 0 then [0] else [(c : Int), -(c : Int)]
  mem n h := by
    by_cases hM : n.natAbs ≤ M
    · simp only [hM, if_true]
      by_cases h0 : n.natAbs = 0
      · have : n = 0 := by omega
        simp [this]
      · simp only [h0, if_false, List.mem_cons, List.not_mem_nil, or_false]
        omega
    · simp only [hM, if_false] at h
      exact absurd h (Nat.lt_irrefl _)
  kostN n := if n ≤ M then n else unendlich
  listeN c := [c]
  memN n h := by
    by_cases hM : n ≤ M
    · simp [hM]
    · simp only [hM, if_false] at h
      exact absurd h (Nat.lt_irrefl _)
  kostP p := (if p.1.natAbs ≤ M then p.1.natAbs else unendlich) + (if p.2.natAbs ≤ M then p.2.natAbs else unendlich)
  listeP c := (List.range (c + 1)).flatMap fun (a : Nat) =>
    (if a = 0 then [(0 : Int)] else [(a : Int), -(a : Int)]).flatMap fun x =>
      (if c - a = 0 then [(0 : Int)] else [Int.ofNat (c - a), -(Int.ofNat (c - a))]).map fun y => (x, y)
  memP p h := by
    obtain ⟨x, y⟩ := p
    simp only at h ⊢
    have h1 : x.natAbs ≤ M := by
      by_cases hc : x.natAbs ≤ M
      · exact hc
      · simp only [hc, if_false] at h
        omega
    have h2 : y.natAbs ≤ M := by
      by_cases hc : y.natAbs ≤ M
      · exact hc
      · simp only [hc, if_false] at h
        omega
    simp only [h1, h2, if_true]
    rw [List.mem_flatMap]
    refine ⟨x.natAbs, List.mem_range.2 (by omega), ?_⟩
    rw [List.mem_flatMap]
    have hx : x ∈ (if x.natAbs = 0 then [(0 : Int)] else [(x.natAbs : Int), -(x.natAbs : Int)]) := by
      by_cases h0 : x.natAbs = 0
      · have : x = 0 := by omega
        simp [this]
      · simp only [h0, if_false, List.mem_cons, List.not_mem_nil, or_false]
        omega
    refine ⟨x, hx, ?_⟩
    have hca : x.natAbs + y.natAbs - x.natAbs = y.natAbs := by omega
    rw [hca]
    refine List.mem_map.2 ⟨y, ?_, rfl⟩
    by_cases h0 : y.natAbs = 0
    · have : y = 0 := by omega
      simp [this]
    · simp only [h0, if_false, List.mem_cons, List.not_mem_nil, or_false, Int.ofNat_eq_natCast]
      omega

/-- A finite alphabet: every listed number costs one, every other number infinity. -/
def Zahlen.kanon (N : List Int) (NN : List Nat) (NP : List (Int × Int)) : Zahlen where
  kost n := if n ∈ N then 1 else unendlich
  liste c := if c = 1 then N else []
  mem n h := by
    by_cases hn : n ∈ N
    · simp [hn]
    · simp only [hn, if_false] at h
      exact absurd h (Nat.lt_irrefl _)
  kostN n := if n ∈ NN then 1 else unendlich
  listeN c := if c = 1 then NN else []
  memN n h := by
    by_cases hn : n ∈ NN
    · simp [hn]
    · simp only [hn, if_false] at h
      exact absurd h (Nat.lt_irrefl _)
  kostP p := if p ∈ NP then 1 else unendlich
  listeP c := if c = 1 then NP else []
  memP p h := by
    by_cases hn : p ∈ NP
    · simp [hn]
    · simp only [hn, if_false] at h
      exact absurd h (Nat.lt_irrefl _)

/-! ## Sized streams -/

/-- The items of exact size `k`, for every `k`. -/
abbrev Sz (α : Type) := Nat → List α

namespace Sz

variable {α β : Type}

/-- One item of size zero. -/
def pure (a : α) : Sz α := fun k => if k = 0 then [a] else []

/-- A free finite choice (size zero). -/
def wahl (xs : List α) : Sz α := fun k => if k = 0 then xs else []

/-- A leaf of size one, from a list of alternatives. -/
def blatt (xs : List α) : Sz α := fun k => if k = 1 then xs else []

/-- One node: the items of size `k` cost one more than the items of the argument. -/
def knoten (A : Sz α) : Sz α
  | 0 => []
  | k + 1 => A k

/-- **Sum of sizes**: `F a` is run on the budget that `a` leaves. -/
def bind (A : Sz α) (F : α → Sz β) : Sz β := fun k =>
  (List.range (k + 1)).flatMap fun i => (A i).flatMap fun a => F a (k - i)

def map (f : α → β) (A : Sz α) : Sz β := fun k => (A k).map f

def vereint (A B : Sz α) : Sz α := fun k => A k ++ B k

/-- A decided guard: the rule's premise is a proof argument of the term. -/
def wenn (p : Prop) [Decidable p] (X : p → Sz α) : Sz α := fun k => if h : p then X h k else []

theorem mem_pure (a : α) : a ∈ pure a 0 := by simp [pure]

theorem mem_wahl {xs : List α} {x : α} (h : x ∈ xs) : x ∈ wahl xs 0 := by simp [wahl, h]

theorem mem_blatt {xs : List α} {x : α} (h : x ∈ xs) : x ∈ blatt xs 1 := by simp [blatt, h]

theorem mem_knoten {A : Sz α} {k : Nat} {x : α} (h : x ∈ A k) : x ∈ knoten A (k + 1) := h

theorem mem_bind {A : Sz α} {F : α → Sz β} {a : α} {x : β} {i j : Nat} (ha : a ∈ A i) (hx : x ∈ F a j) :
    x ∈ bind A F (i + j) := by
  unfold bind
  rw [List.mem_flatMap]
  refine ⟨i, List.mem_range.2 (by omega), ?_⟩
  rw [List.mem_flatMap]
  refine ⟨a, ha, ?_⟩
  have : i + j - i = j := by omega
  rw [this]
  exact hx

/-- Several clauses side by side. -/
def alle (cs : List (Sz α)) : Sz α := fun k => cs.flatMap fun c => c k

theorem mem_alle {cs : List (Sz α)} {c : Sz α} (hc : c ∈ cs) {x : α} {k : Nat} (hx : x ∈ c k) :
    x ∈ alle cs k :=
  List.mem_flatMap.2 ⟨c, hc, hx⟩

/-- The same item at an equal size. -/
theorem mem_cast {A : Sz α} {x : α} {k k' : Nat} (h : x ∈ A k) (hk : k = k') : x ∈ A k' := hk ▸ h

theorem mem_map {A : Sz α} {f : α → β} {a : α} {k : Nat} (ha : a ∈ A k) : f a ∈ map f A k :=
  List.mem_map.2 ⟨a, ha, rfl⟩

theorem mem_vereint_l {A B : Sz α} {x : α} {k : Nat} (h : x ∈ A k) : x ∈ vereint A B k :=
  List.mem_append.2 (Or.inl h)

theorem mem_vereint_r {A B : Sz α} {x : α} {k : Nat} (h : x ∈ B k) : x ∈ vereint A B k :=
  List.mem_append.2 (Or.inr h)

theorem mem_wenn {p : Prop} [Decidable p] {X : p → Sz α} {x : α} {k : Nat} (h : p) (hx : x ∈ X h k) :
    x ∈ wenn p X k := by
  unfold wenn
  rw [dif_pos h]
  exact hx

end Sz

/-! ## Context-changing binds

  A part whose remaining parts live in ANOTHER context (the rest of a block after a `let`, the body of a lock) is
  drawn from a stream `R` that depends on a coarse key of the first part (its type, the resources after it). The
  stream is built ONCE per size of the first part and key, with the bound the budget leaves, and shared by every
  first part of that key: this is the sharing of sub-enumerations by (type, context) key. -/

/-- The distinct keys of a list, in order of first occurrence. -/
def schluessel {α κ : Type} [DecidableEq κ] (key : α → κ) (xs : List α) : List κ :=
  xs.foldl (fun acc a => if key a ∈ acc then acc else acc ++ [key a]) []

theorem mem_schluessel_aux {α κ : Type} [DecidableEq κ] (key : α → κ) (xs : List α) (acc : List κ) (c : κ) :
    (c ∈ acc ∨ ∃ a ∈ xs, key a = c) → c ∈ xs.foldl (fun acc a => if key a ∈ acc then acc else acc ++ [key a]) acc := by
  induction xs generalizing acc with
  | nil => intro h; rcases h with h | ⟨a, ha, _⟩ <;> simp_all
  | cons x xs ih =>
    intro h
    simp only [List.foldl_cons]
    apply ih
    by_cases hx : key x ∈ acc
    · simp only [hx, if_true]
      rcases h with h | ⟨a, ha, hac⟩
      · exact Or.inl h
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact Or.inl (hac ▸ hx)
        · exact Or.inr ⟨a, ha, hac⟩
    · simp only [hx, if_false]
      rcases h with h | ⟨a, ha, hac⟩
      · exact Or.inl (List.mem_append.2 (Or.inl h))
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact Or.inl (List.mem_append.2 (Or.inr (by simp [hac])))
        · exact Or.inr ⟨a, ha, hac⟩

theorem mem_schluessel {α κ : Type} [DecidableEq κ] (key : α → κ) {xs : List α} {a : α} (h : a ∈ xs) :
    key a ∈ schluessel key xs :=
  mem_schluessel_aux key xs [] (key a) (Or.inr ⟨a, h, rfl⟩)

namespace Sz

/-- **Bind with a shared rest**: the stream `R` of the rest is built once per size of the first part and handed the
    budget the first part leaves. -/
def bindR {α β γ : Type} (A : Sz α) (R : Nat → Sz β) (F : α → β → Sz γ) : Sz γ := fun k =>
  (List.range (k + 1)).flatMap fun i =>
    let Rc := R (k - i)
    (A i).flatMap fun a => (bind Rc (F a)) (k - i)

theorem mem_bindR {α β γ : Type} {A : Sz α} {R : Nat → Sz β} {F : α → β → Sz γ} {a : α} {b : β} {y : γ}
    {i j j' : Nat} (ha : a ∈ A i) (hb : b ∈ R (j + j') j) (hy : y ∈ F a b j') :
    y ∈ bindR A R F (i + (j + j')) := by
  unfold bindR
  rw [List.mem_flatMap]
  refine ⟨i, List.mem_range.2 (by omega), ?_⟩
  have h1 : i + (j + j') - i = j + j' := by omega
  simp only [h1]
  rw [List.mem_flatMap]
  exact ⟨a, ha, mem_bind hb hy⟩

/-- **Bind with a shared rest per key**: the first parts of one size are grouped by their key (the first
    component of the Σ-pair, here a type or a resource list), and the stream of the rest is built once per key. -/
def bindS {κ : Type} [DecidableEq κ] {X β : κ → Type} {γ : Type} (A : Sz (Σ c, X c)) (R : (c : κ) → Nat → Sz (β c))
    (F : (c : κ) → X c → β c → Sz γ) : Sz γ := fun k =>
  (List.range (k + 1)).flatMap fun i =>
    let As := A i
    (schluessel (fun p => p.1) As).flatMap fun c =>
      let Rc := R c (k - i)
      (ofTy As c).flatMap fun x => (bind Rc (F c x)) (k - i)

theorem mem_bindS {κ : Type} [DecidableEq κ] {X β : κ → Type} {γ : Type} {A : Sz (Σ c, X c)}
    {R : (c : κ) → Nat → Sz (β c)} {F : (c : κ) → X c → β c → Sz γ} {c : κ} {x : X c} {b : β c} {y : γ}
    {i j j' : Nat} (ha : (⟨c, x⟩ : Σ c, X c) ∈ A i) (hb : b ∈ R c (j + j') j) (hy : y ∈ F c x b j') :
    y ∈ bindS A R F (i + (j + j')) := by
  unfold bindS
  rw [List.mem_flatMap]
  refine ⟨i, List.mem_range.2 (by omega), ?_⟩
  have h1 : i + (j + j') - i = j + j' := by omega
  simp only [h1]
  rw [List.mem_flatMap]
  refine ⟨c, mem_schluessel (fun p => p.1) ha, ?_⟩
  rw [List.mem_flatMap]
  exact ⟨x, mem_ofTy ha, mem_bind hb hy⟩

end Sz

/-! ## Numbers as streams -/

/-- The integers of cost exactly `c`. -/
def zS [Zahlen] : Sz Int := fun c => Zahlen.liste c

/-- The naturals of cost exactly `c`. -/
def nS [Zahlen] : Sz Nat := fun c => Zahlen.listeN c

theorem mem_zS [Zahlen] {n : Int} {c : Nat} (h : Zahlen.kost n = c) (hc : c < unendlich) : n ∈ zS c := by
  subst h
  exact Zahlen.mem n hc

theorem mem_nS [Zahlen] {n : Nat} {c : Nat} (h : Zahlen.kostN n = c) (hc : c < unendlich) : n ∈ nS c := by
  subst h
  exact Zahlen.memN n hc

/-- Pairs of integers (the bounds of a float type). -/
def paarS [Zahlen] : Sz (Int × Int) := fun c => Zahlen.listeP c

theorem mem_paarS [Zahlen] {p : Int × Int} {c : Nat} (h : Zahlen.kostP p = c) (hc : c < unendlich) :
    p ∈ paarS c := by
  subst h
  exact Zahlen.memP p hc

/-- Pairs of integers charged number by number (the payload range of a sum case). -/
def paarI [Zahlen] : Sz (Int × Int) := Sz.bind zS fun a => Sz.bind zS fun b => Sz.pure (a, b)

/-- The cost of such a pair. -/
def kostI [Zahlen] (p : Int × Int) : Nat := Zahlen.kost p.1 + Zahlen.kost p.2

theorem mem_paarI [Zahlen] {p : Int × Int} {c : Nat} (h : kostI p = c) (hc : c < unendlich) : p ∈ paarI c := by
  obtain ⟨a, b⟩ := p
  unfold kostI at h
  simp only at h
  have h1 : Zahlen.kost a < unendlich := by omega
  have h2 : Zahlen.kost b < unendlich := by omega
  have h2' : (a, b) ∈ (Sz.bind zS fun b' => Sz.pure (a, b')) (Zahlen.kost b + 0) :=
    Sz.mem_bind (mem_zS rfl h2) (Sz.mem_pure _)
  exact Sz.mem_cast (Sz.mem_bind (mem_zS rfl h1) h2') (by omega)

end Gabbro.Grammatik.Gen
