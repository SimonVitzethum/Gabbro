module

public import Grammatik.Kern.Syntax.Typen.Teil2

@[expose] public section

/-
  File:       Grammatik/Bausteine/Walk/Abbildung.lean
  Subject:    C01, walk MAPPING PRODUCTS: the generated product of a `mappings of` quantifier. A mapping carries
              all node-entry fields plus the three fields the POSITION supplies: `va`, `level`, `index`. The type
              is a `Ty.prod` of the entry fields, `va`, `level` and `[Ty.index N; L]`.

  Conventions (the recommended answers of `dokumente/IR-COMPILATION-LANES.md`, "Walk mapping products"):
    * `L` finite positive levels, node arity `N`; the root table has level `L - 1` and a table at depth `d` the
      level `L - 1 - d`; an entry at level 0 cannot be descended into.
    * `index[ell]` is the index visited at level `ell`; the positions below the entry's level are canonically zero
      and the active suffix is `[level, L)`; they are not extra visited nodes.
    * `va` is the radix prefix of the path, times `N ^ level`, in LOGICAL leaf units (an early leaf covers
      `N ^ level` such units); a byte `va` needs a checked layout scale and is not defined here.
    * Selection: at an entry the LEAF predicate is evaluated first (a leaf yields exactly one mapping and stops
      the descent, also with a true `dwhen`); otherwise the entry is descended into only if `dwhen` holds and
      another level exists. Neither predicate replaces the other.
  This is the pure enumeration model (`visitT`) and its exact correctness. `Binding.lean` supplies a safe
  node-cell view and `Expansion.lean` generates G traversals. Source walkers remain refused until their full
  enumeration, mapping construction, control and invariant correspondence is proved.
-/

namespace Gabbro.Grammatik

/-! ## 1. The mapping product type -/

/-- The synthesized field names of a mapping: they may not clash with a node-entry field. -/
def walkReserviert : List String := ["va", "level", "index"]

/-- The node-entry field names are free of the synthesized names and of each other. -/
def walkNamenOk (names : List String) : Bool :=
  names.all (fun n => !walkReserviert.contains n) && names.eraseDups.length == names.length

/-- The shape of a walk: positive finite level count, node arity and the node-entry field types. -/
structure WalkShape where
  levels : Nat
  arity : Nat
  entry : List Ty
  levels_pos : 0 < levels

/-- `va`: a logical leaf number below `N ^ L`. -/
def WalkShape.vaTy (s : WalkShape) : Ty := .int 0 ((s.arity : Int) ^ s.levels - 1)

/-- `level`: `0 .. L - 1`. -/
def WalkShape.levelTy (s : WalkShape) : Ty := .int 0 ((s.levels : Int) - 1)

/-- `index`: one entry index per level. -/
def WalkShape.indexTy (s : WalkShape) : Ty := .arr (Ty.index (s.arity : Int)) s.levels

/-- The fields of a mapping in order: the node-entry fields, `va`, `level`, `index`. -/
def WalkShape.mappingFields (s : WalkShape) : List Ty := s.entry ++ [s.vaTy, s.levelTy, s.indexTy]

/-- **The mapping product type** of the declaration number `name`. -/
def WalkShape.mappingTy (s : WalkShape) (name : Nat) : Ty := Ty.prodOf name s.mappingFields

theorem WalkShape.mappingFields_length (s : WalkShape) : s.mappingFields.length = s.entry.length + 3 := by
  simp only [WalkShape.mappingFields, List.length_append, List.length_cons, List.length_nil]

/-- The mapping type is exactly the nominal product over the listed fields. -/
theorem WalkShape.mappingTy_felder (s : WalkShape) (name : Nat) :
    s.mappingTy name = .prod name s.mappingFields :=
  rfl

/-- The level of a table at a depth: root highest, the last level zero. -/
def walkLevel (levels depth : Nat) : Nat := levels - 1 - depth

theorem walkLevel_wurzel (levels : Nat) : walkLevel levels 0 = levels - 1 := by
  simp only [walkLevel, Nat.sub_zero]

/-- The `index` array of the mapping at the end of `path` (root to entry): zero below the entry's level, the
    visited index on the active suffix `[level, L)`. -/
def walkIndexAt (levels : Nat) {N : Nat} (path : List (Fin N)) (ell : Nat) : Nat :=
  if ell < levels - path.length then 0
  else if ell < levels then ((path[levels - 1 - ell]?).map (·.val)).getD 0
  else 0

theorem walkIndexAt_unten (levels : Nat) {N : Nat} (path : List (Fin N)) (ell : Nat)
    (h : ell < levels - path.length) : walkIndexAt levels path ell = 0 := by
  simp only [walkIndexAt, h, if_true]

/-- `va` in logical leaf units: the radix-`N` prefix of the path times `N ^ level`. -/
def walkVa (levels N : Nat) (path : List (Fin N)) : Nat :=
  (path.foldl (fun r k => r * N + k.val) 0) * N ^ (levels - path.length)

theorem walkRadix_lt (N : Nat) :
    ∀ (path : List (Fin N)) (acc a : Nat), acc < N ^ a →
      path.foldl (fun r k => r * N + k.val) acc < N ^ (a + path.length)
  | [], acc, a, h => by simpa using h
  | k :: rest, acc, a, h => by
      have hk := k.isLt
      have h0 : acc + 1 ≤ N ^ a := h
      have h1 : acc * N + k.val < N ^ (a + 1) :=
        calc acc * N + k.val < acc * N + N := by omega
          _ = (acc + 1) * N := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ N ^ a * N := Nat.mul_le_mul_right N h0
          _ = N ^ (a + 1) := (Nat.pow_succ N a).symm
      have h2 := walkRadix_lt N rest (acc * N + k.val) (a + 1) h1
      have e : a + 1 + rest.length = a + (k :: rest).length := by
        simp only [List.length_cons]; omega
      rw [e] at h2
      exact h2

/-- **`va` stays below `N ^ L`** for every path of at most `L` indices. -/
theorem walkVa_lt (levels N : Nat) (path : List (Fin N)) (hN : 0 < N) (h : path.length ≤ levels) :
    walkVa levels N path < N ^ levels := by
  have h1 := walkRadix_lt N path 0 0 (by simp only [Nat.pow_zero]; omega)
  have h2 : N ^ (levels - path.length) * N ^ path.length = N ^ levels := by
    rw [← Nat.pow_add]; congr 1; omega
  have h3 : 0 < N ^ (levels - path.length) := Nat.one_le_pow _ _ hN
  calc walkVa levels N path
      = (path.foldl (fun r k => r * N + k.val) 0) * N ^ (levels - path.length) := rfl
    _ < N ^ (0 + path.length) * N ^ (levels - path.length) := Nat.mul_lt_mul_of_pos_right h1 h3
    _ = N ^ levels := by rw [Nat.zero_add, Nat.mul_comm]; exact h2

/-! ## 2. The enumeration of the leaf entries, by path -/

/-- A walk over abstract entries: the leaf predicate, `dwhen`, and the child table of an entry (`down`). -/
structure WalkTree (α : Type) (N : Nat) where
  leaf : α → Bool
  dwhen : α → Bool
  down : α → Option (Fin N → α)

variable {α : Type} {N : Nat}

/-- The visits of the entry `e` at position `k`, given the visits `sub` of a lower table: a leaf yields exactly its
    own mapping and stops, else a `dwhen` entry yields the visits of its child table below `k`. -/
def entryVisits (T : WalkTree α N) (sub : (Fin N → α) → List (List (Fin N) × α)) (k : Fin N) (e : α) :
    List (List (Fin N) × α) :=
  if T.leaf e = true then [([k], e)]
  else if T.dwhen e = true then
    (match T.down e with
     | none => []
     | some t' => (sub t').map fun p => (k :: p.1, p.2))
  else []

/-- **The mappings of a table of level `l`**, in lexicographic path order (entry 0 first); a path runs from the
    root table to the leaf entry, each step an entry index. At level 0 no entry is descended into. -/
def visitT (T : WalkTree α N) : Nat → (Fin N → α) → List (List (Fin N) × α)
  | 0, tbl => (List.finRange N).flatMap fun k => if T.leaf (tbl k) = true then [([k], tbl k)] else []
  | l + 1, tbl => (List.finRange N).flatMap fun k => entryVisits T (visitT T l) k (tbl k)

/-- The specification: the leaf entry `m` at the path `p` from the table `tbl` of level `l`. -/
inductive WalkHit (T : WalkTree α N) : Nat → (Fin N → α) → List (Fin N) → α → Prop where
  | leaf {l : Nat} {tbl : Fin N → α} {k : Fin N} :
      T.leaf (tbl k) = true → WalkHit T l tbl [k] (tbl k)
  | down {l : Nat} {tbl : Fin N → α} {k : Fin N} {t' : Fin N → α} {q : List (Fin N)} {m : α} :
      T.leaf (tbl k) = false → T.dwhen (tbl k) = true → T.down (tbl k) = some t' →
      WalkHit T l t' q m → WalkHit T (l + 1) tbl (k :: q) m

theorem entryVisits_kopf {T : WalkTree α N} {sub : (Fin N → α) → List (List (Fin N) × α)} {k : Fin N}
    {e : α} {x : List (Fin N) × α} (h : x ∈ entryVisits T sub k e) : ∃ q, x.1 = k :: q := by
  unfold entryVisits at h
  by_cases hl : T.leaf e = true
  · rw [if_pos hl] at h
    simp only [List.mem_singleton] at h
    exact ⟨[], by rw [h]⟩
  · by_cases hd : T.dwhen e = true
    · rw [if_neg hl, if_pos hd] at h
      cases hdn : T.down e with
      | none => simp only [hdn, List.not_mem_nil] at h
      | some t' =>
        simp only [hdn, List.mem_map] at h
        obtain ⟨⟨q, m⟩, _, hx⟩ := h
        exact ⟨q, by rw [← hx]⟩
    · rw [if_neg hl, if_neg hd] at h
      simp at h

theorem entryVisits_pfade {T : WalkTree α N} {sub : (Fin N → α) → List (List (Fin N) × α)} {k : Fin N}
    (hsub : ∀ t', (sub t').Pairwise (fun x y => x.1 ≠ y.1)) (e : α) :
    (entryVisits T sub k e).Pairwise (fun x y => x.1 ≠ y.1) := by
  unfold entryVisits
  by_cases hl : T.leaf e = true
  · rw [if_pos hl]
    exact List.pairwise_singleton _ _
  · by_cases hd : T.dwhen e = true
    · rw [if_neg hl, if_pos hd]
      cases hdn : T.down e with
      | none => exact List.Pairwise.nil
      | some t' =>
        simp only [List.pairwise_map]
        refine List.Pairwise.imp ?_ (hsub t')
        intro a b hab hk
        exact hab (List.cons.inj hk).2
    · rw [if_neg hl, if_neg hd]
      exact List.Pairwise.nil

/-- **The exact enumeration**: `m` is visited at the path `p` exactly when it is a leaf entry reached by the
    descent rules (leaf first, then `dwhen`, then a further level). -/
theorem visitT_mem_iff (T : WalkTree α N) :
    ∀ (l : Nat) (tbl : Fin N → α) (p : List (Fin N)) (m : α),
      (p, m) ∈ visitT T l tbl ↔ WalkHit T l tbl p m
  | 0, tbl, p, m => by
      constructor
      · intro h
        simp only [visitT, List.mem_flatMap] at h
        obtain ⟨k, _, hk⟩ := h
        by_cases hl : T.leaf (tbl k) = true
        · rw [if_pos hl] at hk
          simp only [List.mem_singleton, Prod.mk.injEq] at hk
          obtain ⟨rfl, rfl⟩ := hk
          exact WalkHit.leaf hl
        · rw [if_neg hl] at hk
          simp at hk
      · intro h
        cases h with
        | @leaf l tbl' k hl =>
          simp only [visitT, List.mem_flatMap]
          exact ⟨k, List.mem_finRange k, by rw [if_pos hl]; exact List.mem_singleton_self _⟩
  | l + 1, tbl, p, m => by
      constructor
      · intro h
        simp only [visitT, List.mem_flatMap] at h
        obtain ⟨k, _, hk⟩ := h
        unfold entryVisits at hk
        by_cases hl : T.leaf (tbl k) = true
        · rw [if_pos hl] at hk
          simp only [List.mem_singleton, Prod.mk.injEq] at hk
          obtain ⟨rfl, rfl⟩ := hk
          exact WalkHit.leaf hl
        · have hl' : T.leaf (tbl k) = false := by simpa using hl
          by_cases hd : T.dwhen (tbl k) = true
          · rw [if_neg hl, if_pos hd] at hk
            cases hdn : T.down (tbl k) with
            | none =>
              simp only [hdn] at hk
              simp at hk
            | some t' =>
              simp only [hdn, List.mem_map] at hk
              obtain ⟨⟨q, m'⟩, hq, hx⟩ := hk
              simp only [Prod.mk.injEq] at hx
              obtain ⟨rfl, rfl⟩ := hx
              exact WalkHit.down hl' hd hdn ((visitT_mem_iff T l t' q m').mp hq)
          · rw [if_neg hl, if_neg hd] at hk
            simp at hk
      · intro h
        cases h with
        | @leaf l' tbl' k hl =>
          simp only [visitT, List.mem_flatMap]
          refine ⟨k, List.mem_finRange k, ?_⟩
          unfold entryVisits
          rw [if_pos hl]
          exact List.mem_singleton_self _
        | @down l' tbl' k t' q m' hl hd hdn hq =>
          simp only [visitT, List.mem_flatMap]
          refine ⟨k, List.mem_finRange k, ?_⟩
          unfold entryVisits
          have hl'' : ¬ T.leaf (tbl' k) = true := by simp [hl]
          rw [if_neg hl'', if_pos hd]
          simp only [hdn, List.mem_map]
          exact ⟨(q, m'), (visitT_mem_iff T l' t' q m').mpr hq, rfl⟩

/-- **No duplicate paths**: two different mappings have different paths (shared child tables reached through
    different paths stay different mappings). -/
theorem visitT_pfade (T : WalkTree α N) :
    ∀ (l : Nat) (tbl : Fin N → α), (visitT T l tbl).Pairwise (fun x y => x.1 ≠ y.1)
  | 0, tbl => by
      simp only [visitT]
      rw [List.pairwise_flatMap]
      refine ⟨?_, ?_⟩
      · intro k _
        try dsimp only
        by_cases hl : T.leaf (tbl k) = true
        · rw [if_pos hl]
          exact List.pairwise_singleton _ _
        · rw [if_neg hl]
          exact List.Pairwise.nil
      · refine List.Pairwise.imp ?_ (List.nodup_finRange N)
        intro a b hab x hx y hy hxy
        try dsimp only at hx hy
        by_cases hla : T.leaf (tbl a) = true
        · by_cases hlb : T.leaf (tbl b) = true
          · rw [if_pos hla] at hx
            rw [if_pos hlb] at hy
            simp only [List.mem_singleton] at hx hy
            rw [hx, hy] at hxy
            exact hab (List.cons.inj hxy).1
          · rw [if_neg hlb] at hy
            simp at hy
        · rw [if_neg hla] at hx
          simp at hx
  | l + 1, tbl => by
      simp only [visitT]
      rw [List.pairwise_flatMap]
      refine ⟨fun k _ => entryVisits_pfade (fun t' => visitT_pfade T l t') _, ?_⟩
      refine List.Pairwise.imp ?_ (List.nodup_finRange N)
      intro a b hab x hx y hy hxy
      try dsimp only at hx hy
      obtain ⟨q, hq⟩ := entryVisits_kopf hx
      obtain ⟨r, hr⟩ := entryVisits_kopf hy
      rw [hq, hr] at hxy
      exact hab (List.cons.inj hxy).1

theorem sum_le_mul {β : Type} (xs : List β) (f : β → Nat) (b : Nat) (h : ∀ x ∈ xs, f x ≤ b) :
    (xs.map f).sum ≤ xs.length * b := by
  induction xs with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons x xs ih =>
      have h1 := h x List.mem_cons_self
      have h2 := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- **The number of mappings** of a table of level `l` is at most `N ^ (l + 1)`. -/
theorem visitT_length_le (T : WalkTree α N) :
    ∀ (l : Nat) (tbl : Fin N → α), (visitT T l tbl).length ≤ N ^ (l + 1)
  | 0, tbl => by
      simp only [visitT, List.length_flatMap]
      have h := sum_le_mul (List.finRange N)
        (fun k => (if T.leaf (tbl k) = true then [([k], tbl k)] else []).length) 1 (by
          intro k _
          by_cases hl : T.leaf (tbl k) = true
          · rw [if_pos hl]; exact Nat.le_refl _
          · rw [if_neg hl]; exact Nat.zero_le _)
      simpa only [List.length_finRange, Nat.mul_one, Nat.zero_add, Nat.pow_one] using h
  | l + 1, tbl => by
      simp only [visitT, List.length_flatMap]
      have h := sum_le_mul (List.finRange N) (fun k => (entryVisits T (visitT T l) k (tbl k)).length)
        (N ^ (l + 1)) (by
          intro k _
          have hN : 0 < N := k.pos
          have hpos : 1 ≤ N ^ (l + 1) := Nat.one_le_pow _ _ hN
          unfold entryVisits
          by_cases hl : T.leaf (tbl k) = true
          · rw [if_pos hl]; exact hpos
          · by_cases hd : T.dwhen (tbl k) = true
            · rw [if_neg hl, if_pos hd]
              cases hdn : T.down (tbl k) with
              | none => exact Nat.zero_le _
              | some t' =>
                simp only [List.length_map]
                exact visitT_length_le T l t'
            · rw [if_neg hl, if_neg hd]; exact Nat.zero_le _)
      have e : N ^ (l + 1 + 1) = N * N ^ (l + 1) := by
        rw [Nat.pow_succ]; exact Nat.mul_comm _ _
      rw [e]
      simpa only [List.length_finRange] using h

/-! ## 3. The bill: internal entries count, not only leaves -/

/-- The entries visited in a table of level `l`: every entry of the table, plus the entries of every child table
    that a non-leaf `dwhen` entry descends into. -/
def walkWork (T : WalkTree α N) : Nat → (Fin N → α) → Nat
  | 0, _ => N
  | l + 1, tbl => ((List.finRange N).map fun k =>
      1 + (if T.leaf (tbl k) = true then 0
           else if T.dwhen (tbl k) = true then
             (match T.down (tbl k) with
              | none => 0
              | some t' => walkWork T l t')
           else 0)).sum

/-- **The bound by the sum of the level bounds** (`N + N*N + … + N^(l+1)`, not `L*N` and not the leaf count). -/
def walkBound (N : Nat) : Nat → Nat
  | 0 => N
  | l + 1 => N * (1 + walkBound N l)

theorem walkWork_le (T : WalkTree α N) :
    ∀ (l : Nat) (tbl : Fin N → α), walkWork T l tbl ≤ walkBound N l
  | 0, _ => Nat.le_refl _
  | l + 1, tbl => by
      simp only [walkWork, walkBound]
      have h := sum_le_mul (List.finRange N)
        (fun k => 1 + (if T.leaf (tbl k) = true then 0
           else if T.dwhen (tbl k) = true then
             (match T.down (tbl k) with
              | none => 0
              | some t' => walkWork T l t')
           else 0)) (1 + walkBound N l) (by
          intro k _
          by_cases hl : T.leaf (tbl k) = true
          · rw [if_pos hl]; omega
          · by_cases hd : T.dwhen (tbl k) = true
            · rw [if_neg hl, if_pos hd]
              cases hdn : T.down (tbl k) with
              | none => omega
              | some t' =>
                have := walkWork_le T l t'
                omega
            · rw [if_neg hl, if_neg hd]; omega)
      simpa only [List.length_finRange] using h

end Gabbro.Grammatik
