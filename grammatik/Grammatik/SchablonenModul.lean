/-
  File:      Grammatik/SchablonenModul.lean
  Part of:   Gabbro -- the generator-template library (T5 of
             dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md): the runtime of a `module` unit
             (a loadable kernel module) as GENERATED text (C-free lane, C2, 2026-09-30).

  Rows of `crates/gabbro-check/src/schablonen.rs`:

  * `arena.modul` -- the arena runtime the module driver writes (`treiber.rs::KMOD_ARENA`):
    each dynamic arena's storage is a static pool of the manifest's provision `V`, the span is
    `min(max * elem, V)`, the committed floor must fit it (else the LOAD is refused), a `grow`
    past the ceiling is a fail-stop the load function reads back, a `grow` past the span
    answers `false` with `committed` unchanged.
  * `modul.lebenslauf` -- the loader's two entry points the driver writes
    (`treiber.rs::erzeuge_kmod`): load = every arena bound, every lock initialised, the unit's
    init, the fail-stop read back, one thread per root; unload = every root awaited, then the
    unit's exit.

  Both are ABSTRACT CORES like `arena.dyn` and `faden.laufzeit` (SchablonenArena.lean,
  SchablonenFaden.lean): machine G has the arena as a table of `max` slots (ArenaDyn.lean) and
  the declared starts as threads (premise (d) of the goal, Zielsatz/Spec.lean). What is proved
  here is the mechanics the templates add:

  * `arena_modul_inv_reserve`, `arena_modul_inv_grow`: the invariant `committed <= max` and
    `committed * elem <= span <= V` is established by a successful reservation and kept by
    every `grow` -- so every slot the unit can reach lies inside its pool
    (`arena_modul_slot_im_lager`), which is the memory-safety half of the template;
  * `arena_modul_kein_ueberlauf`: no `uint64_t` product of the C wraps (`max`, `elem` are
    32-bit, and the span product is formed only below the ceiling);
  * `arena_modul_monoton`: the committed prefix only grows, and a refused `grow` changes
    nothing;
  * `laden_erfolg`, `laden_init_erst_nach_bindung`, `laden_ruft_kein_exit`,
    `laden_verweigert_wartet`, `entladen_wartet_vor_exit`: the load runs the unit's init only
    after every arena is bound and every lock initialised, never calls the unit's exit, starts
    roots only after an init that answered 0 with no fail-stop, and on a refusal waits for
    every root it started; the unload waits for every root before the exit.

  NOT proved: that the program's binding keeps its contract (a lock operation takes and gives
  the lock, a thread start runs the root and a failed start completes at once) -- the program's
  own declarations, user logic, premise (c).

  No `sorry`, no `native_decide`, no new axiom; each theorem has a witness instantiating ALL
  its premises jointly.
-/

namespace Gabbro.Grammatik

namespace ModulLaufzeit

/-! ## 1. `arena.modul` -/

/-- The descriptor fields the template reads (the emitter's `gabbro_arena_desc`). -/
structure Desk where
  elem : Nat
  max : Nat
  floor : Nat
  committed : Nat
  deriving DecidableEq

/-- `gabbro_modul_spanne`: the ceiling in bytes, cut at the provision `V`. -/
def spanne (d : Desk) (V : Nat) : Nat := min (d.max * d.elem) V

/-- `gabbro_modul_reserve`: `none` is a refused LOAD (a bad descriptor or a floor the span
    cannot hold); otherwise the descriptor with `committed = floor`. -/
def reserve (d : Desk) (V : Nat) : Option Desk :=
  if d.max = 0 ∨ d.elem = 0 ∨ d.max < d.floor then none
  else if spanne d V < d.floor * d.elem then none
  else some { d with committed := d.floor }

/-- The three answers of `gabbro_arena_grow`. -/
inductive Wachs where
  | stopp          -- past the ceiling: the fail-stop (`gabbro_modul_stopp` set)
  | nein           -- past the span: `false`, the program's `else` runs
  | ja (d : Desk)  -- committed moved
  deriving DecidableEq

/-- `gabbro_arena_grow(d, n)` for `n > 0` (the C answers `true` for `n = 0` and changes
    nothing). -/
def grow (d : Desk) (V n : Nat) : Wachs :=
  if d.max < d.committed + n then .stopp
  else if spanne d V < (d.committed + n) * d.elem then .nein
  else .ja { d with committed := d.committed + n }

/-- The invariant: every committed slot lies inside the span, the span inside the pool. -/
def Inv (d : Desk) (V : Nat) : Prop :=
  d.committed ≤ d.max ∧ d.committed * d.elem ≤ spanne d V ∧ spanne d V ≤ V

theorem spanne_le (d : Desk) (V : Nat) : spanne d V ≤ V := Nat.min_le_right _ _

theorem arena_modul_inv_reserve (d d' : Desk) (V : Nat) (h : reserve d V = some d') :
    Inv d' V ∧ d'.committed = d.floor ∧ d'.elem = d.elem ∧ d'.max = d.max := by
  unfold reserve at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i h1 h2
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨⟨?_, ?_, spanne_le _ _⟩, rfl, rfl, rfl⟩
      · simp only; omega
      · simp only [spanne] at h2 ⊢; omega

theorem arena_modul_inv_grow (d d' : Desk) (V n : Nat) (_hI : Inv d V)
    (h : grow d V n = .ja d') : Inv d' V ∧ d'.committed = d.committed + n ∧
      d'.elem = d.elem ∧ d'.max = d.max := by
  unfold grow at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i h1 h2
      simp only [Wachs.ja.injEq] at h
      subst h
      refine ⟨⟨?_, ?_, spanne_le _ _⟩, rfl, rfl, rfl⟩
      · simp only; omega
      · simp only [spanne] at h2 ⊢; omega

/-- A refused `grow` (either kind) leaves the descriptor as it was: the C returns before any
    store to `committed`. -/
theorem arena_modul_monoton (d d' : Desk) (V n : Nat) (h : grow d V n = .ja d') :
    d.committed ≤ d'.committed := by
  unfold grow at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · simp only [Wachs.ja.injEq] at h; subst h; simp

/-- **Every slot the unit can reach lies inside its pool**: slot `i < committed` occupies the
    bytes `[i * elem, (i+1) * elem)`, all below `V` (the static `uint8_t [V]` row). -/
theorem arena_modul_slot_im_lager (d : Desk) (V i : Nat) (hI : Inv d V) (hi : i < d.committed) :
    (i + 1) * d.elem ≤ V := by
  obtain ⟨_, h2, h3⟩ := hI
  have : (i + 1) * d.elem ≤ d.committed * d.elem := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **No 64-bit product wraps**: with 32-bit `max` and `elem`, the ceiling product and the
    floor product are below `2^64`, and the span product `neu * elem` is formed only when
    `neu <= max` (the ceiling test comes first). -/
theorem arena_modul_kein_ueberlauf (d : Desk) (neu : Nat) (hm : d.max < 2 ^ 32)
    (he : d.elem < 2 ^ 32) (hf : d.floor ≤ d.max) (hn : neu ≤ d.max) :
    d.max * d.elem < 2 ^ 64 ∧ d.floor * d.elem < 2 ^ 64 ∧ neu * d.elem < 2 ^ 64 := by
  have hmax : d.max * d.elem < 2 ^ 32 * 2 ^ 32 := by
    calc d.max * d.elem ≤ d.max * (2 ^ 32 - 1) := Nat.mul_le_mul_left _ (by omega)
      _ < 2 ^ 32 * 2 ^ 32 := by
        have : d.max * (2 ^ 32 - 1) ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
  have h64 : (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 := by rfl
  rw [h64] at hmax
  refine ⟨hmax, ?_, ?_⟩
  · exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hf) hmax
  · exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hn) hmax

/-- A grow past the ceiling is the fail-stop, never a commit. -/
theorem arena_modul_ueber_der_decke (d : Desk) (V n : Nat) (h : d.max < d.committed + n) :
    grow d V n = .stopp := by
  unfold grow; simp [h]

/-! ### Witness: the `halde` probe (`messung/proben/kmodul/halde-treiber.gab`) -/

/-- `arena Knoten capacity 2 .. 4 max 4096 of Wert` (8-byte slots) under `provision 24576`. -/
def haldeD : Desk := { elem := 8, max := 4096, floor := 4, committed := 0 }

theorem arena_modul_zeuge :
    ∃ d1 d2 d3,
      reserve haldeD 24576 = some d1 ∧ Inv d1 24576 ∧
      grow d1 24576 1024 = .ja d2 ∧ grow d2 24576 1024 = .ja d3 ∧
      d3.committed = 2052 ∧ Inv d3 24576 ∧
      grow d3 24576 1024 = .nein ∧          -- the third grow is refused below the ceiling
      grow d3 24576 3000 = .stopp ∧          -- and one past the ceiling is the fail-stop
      (2051 + 1) * d3.elem ≤ 24576 := by
  refine ⟨{ haldeD with committed := 4 }, { haldeD with committed := 1028 },
    { haldeD with committed := 2052 }, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩ <;>
    simp (config := { decide := true }) [Inv]

/-! ## 2. `modul.lebenslauf` -/

/-- What the driver's two entry points do, in order. -/
inductive Schritt where
  | binde (a : Nat)        -- arena `a`'s pool bound (`gabbro_modul_reserve`)
  | sperre (l : Nat)       -- lock `l` initialised (`gabbro_kern_sperre_init`)
  | init                   -- the unit's init
  | start (w : Nat)        -- root `w` handed to the binding's thread start
  | warte (w : Nat)        -- root `w` awaited
  | exit                   -- the unit's exit
  deriving DecidableEq

/-- The outcomes the driver reads: each arena's reservation, the init's answer, whether a
    fail-stop fired during it, each root's start. -/
structure Lage where
  arenen : List Bool
  sperren : Nat
  antwort : Nat
  stopp : Bool
  wurzeln : List Bool

/-- The arena loop: stops at the first refusal (the C `return` inside the loop). -/
def bindeAlle : Nat → List Bool → List Schritt × Bool
  | _, [] => ([], true)
  | i, b :: rest =>
    if b then
      let (t, ok) := bindeAlle (i + 1) rest
      (Schritt.binde i :: t, ok)
    else ([Schritt.binde i], false)

/-- The loader's load symbol. `true` = loaded (answers 0). -/
def laden (L : Lage) : List Schritt × Bool :=
  let (tA, okA) := bindeAlle 0 L.arenen
  if ¬ okA then (tA, false) else
  let tS := (List.range L.sperren).map Schritt.sperre
  if L.antwort ≠ 0 then (tA ++ tS ++ [Schritt.init], false) else
  if L.stopp then (tA ++ tS ++ [Schritt.init], false) else
  let n := L.wurzeln.length
  let tW := (List.range n).map Schritt.start
  if L.wurzeln.all id then (tA ++ tS ++ [Schritt.init] ++ tW, true)
  else (tA ++ tS ++ [Schritt.init] ++ tW ++ (List.range n).map Schritt.warte, false)

/-- The loader's unload symbol (called only after a load that answered 0). -/
def entladen (n : Nat) : List Schritt :=
  (List.range n).map Schritt.warte ++ [Schritt.exit]

theorem bindeAlle_spec (i : Nat) (bs : List Bool) :
    (bindeAlle i bs).2 = bs.all id ∧ Schritt.init ∉ (bindeAlle i bs).1 ∧
      Schritt.exit ∉ (bindeAlle i bs).1 ∧ (∀ w, Schritt.start w ∉ (bindeAlle i bs).1) ∧
      ((bindeAlle i bs).2 = true → (bindeAlle i bs).1 = (List.range bs.length).map (fun k => Schritt.binde (i + k))) := by
  induction bs generalizing i with
  | nil => simp [bindeAlle]
  | cons b rest ih =>
    cases b
    · simp [bindeAlle]
    · obtain ⟨h1, h2, h3, h4, h5⟩ := ih (i + 1)
      simp only [bindeAlle, if_true, List.all_cons, id, Bool.true_and]
      refine ⟨h1, ?_, ?_, ?_, ?_⟩
      · simp [h2]
      · simp [h3]
      · intro w; simp [h4 w]
      · intro h
        rw [h5 h, List.length_cons, List.range_succ_eq_map]
        simp [Function.comp_def, Nat.add_assoc, Nat.add_comm 1]

/-- **A load that answers 0**: every arena bound, the init answered 0 with no fail-stop, and
    every root started -- in exactly the order bind, lock, init, start. -/
theorem laden_erfolg (L : Lage) (h : (laden L).2 = true) :
    L.arenen.all id = true ∧ L.antwort = 0 ∧ L.stopp = false ∧ L.wurzeln.all id = true ∧
      (laden L).1 = (List.range L.arenen.length).map Schritt.binde ++
        (List.range L.sperren).map Schritt.sperre ++ [Schritt.init] ++
        (List.range L.wurzeln.length).map Schritt.start := by
  obtain ⟨hA1, -, -, -, hA5⟩ := bindeAlle_spec 0 L.arenen
  have hok : (bindeAlle 0 L.arenen).2 = true := by
    cases hn : (bindeAlle 0 L.arenen).2
    · unfold laden at h; simp [hn] at h
    · rfl
  have ha : L.antwort = 0 := by
    by_cases hn : L.antwort = 0
    · exact hn
    · unfold laden at h; simp [hok, hn] at h
  have hs : L.stopp = false := by
    cases hn : L.stopp
    · rfl
    · unfold laden at h; simp [hok, ha, hn] at h
  have hw : L.wurzeln.all id = true := by
    cases hn : L.wurzeln.all id
    · unfold laden at h; simp [hok, ha, hs, hn] at h
    · rfl
  refine ⟨hA1 ▸ hok, ha, hs, hw, ?_⟩
  unfold laden
  simp only [hok, ha, hs, hw, not_true_eq_false, ne_eq, if_false, if_true, Bool.false_eq_true]
  rw [hA5 hok]; simp

/-- **The unit's init runs only after every arena is bound** -- a refused reservation returns
    before any lock or any of the unit's code. -/
theorem laden_init_erst_nach_bindung (L : Lage) (h : Schritt.init ∈ (laden L).1) :
    L.arenen.all id = true := by
  obtain ⟨hA1, hA2, -, -, -⟩ := bindeAlle_spec 0 L.arenen
  unfold laden at h
  by_cases hok : (bindeAlle 0 L.arenen).2 = true
  · exact hA1 ▸ hok
  · simp [hok] at h; exact absurd h hA2

/-- **The load never calls the unit's exit** -- on a refusal the unit was never loaded. -/
theorem laden_ruft_kein_exit (L : Lage) : Schritt.exit ∉ (laden L).1 := by
  obtain ⟨-, -, hA3, -, -⟩ := bindeAlle_spec 0 L.arenen
  unfold laden
  by_cases hok : (bindeAlle 0 L.arenen).2 = true
  · simp only [hok, not_true_eq_false, if_false]
    split
    · simp [hA3]
    · split
      · simp [hA3]
      · split <;> simp [hA3]
  · simp [hok, hA3]

/-- **Roots start only after an init that answered 0 and fired no fail-stop.** -/
theorem laden_start_nach_init (L : Lage) (w : Nat) (h : Schritt.start w ∈ (laden L).1) :
    L.antwort = 0 ∧ L.stopp = false ∧ L.arenen.all id = true := by
  obtain ⟨hA1, -, -, hA4, -⟩ := bindeAlle_spec 0 L.arenen
  unfold laden at h
  by_cases hok : (bindeAlle 0 L.arenen).2 = true
  · simp only [hok, not_true_eq_false, if_false] at h
    by_cases ha : L.antwort = 0
    · simp only [ha, ne_eq, not_true_eq_false, if_false] at h
      cases hs : L.stopp
      · exact ⟨ha, rfl, hA1 ▸ hok⟩
      · simp [hs, hA4] at h
    · simp [ha, hA4] at h
  · simp [hok, hA4] at h

/-- **A refused load waits for every root it started** -- no thread of the unit outlives a
    load that did not succeed. -/
theorem laden_verweigert_wartet (L : Lage) (w : Nat) (hv : (laden L).2 = false)
    (h : Schritt.start w ∈ (laden L).1) : Schritt.warte w ∈ (laden L).1 := by
  obtain ⟨-, -, -, hA4, -⟩ := bindeAlle_spec 0 L.arenen
  unfold laden at h hv ⊢
  by_cases hok : (bindeAlle 0 L.arenen).2 = true
  · simp only [hok, not_true_eq_false, if_false] at h hv ⊢
    by_cases ha : L.antwort = 0
    · simp only [ha, ne_eq, not_true_eq_false, if_false] at h hv ⊢
      cases hs : L.stopp
      · simp only [hs, Bool.false_eq_true, if_false] at h hv ⊢
        by_cases hw : L.wurzeln.all id = true
        · simp [hw] at hv
        · simp only [hw, Bool.false_eq_true, if_false] at h ⊢
          have hS : Schritt.start w ∉ (List.range L.sperren).map Schritt.sperre := by simp
          have hk : w < L.wurzeln.length := by
            simp only [List.mem_append, List.mem_singleton] at h
            rcases h with (((h | h) | h) | h) | h
            · exact absurd h (hA4 w)
            · exact absurd h hS
            · exact absurd h (by simp)
            · simpa using h
            · simp at h
          simp only [List.mem_append, List.mem_map, List.mem_range]
          exact Or.inr ⟨w, hk, rfl⟩
      · simp [hs, hA4] at h
    · simp [ha, hA4] at h
  · simp [hok, hA4] at h

/-- **The unload waits for every root before the unit's exit**, and calls the exit once. -/
theorem entladen_wartet_vor_exit (n w : Nat) (hw : w < n) :
    ∃ vor nach, entladen n = vor ++ [Schritt.exit] ++ nach ∧ Schritt.warte w ∈ vor ∧
      nach = [] := by
  refine ⟨(List.range n).map Schritt.warte, [], by simp [entladen], ?_, rfl⟩
  simp only [List.mem_map, List.mem_range]
  exact ⟨w, hw, rfl⟩

/-! ### Witnesses: the three probes of `instrumente/pruefe-kernelmodul.sh` -/

/-- `halde`: one arena, no lock, no root -- the load succeeds. -/
theorem lebenslauf_zeuge_halde :
    laden { arenen := [true], sperren := 0, antwort := 0, stopp := false, wurzeln := [] } =
      ([Schritt.binde 0, Schritt.init], true) := by decide

/-- `atomar`: two roots, the second fails to start -- the load refuses and waits for both. -/
theorem lebenslauf_zeuge_atomar_verweigert :
    laden { arenen := [], sperren := 0, antwort := 0, stopp := false, wurzeln := [true, false] } =
      ([Schritt.init, Schritt.start 0, Schritt.start 1, Schritt.warte 0, Schritt.warte 1], false) := by
  decide

/-- The harness's gift 4 (a ceiling below the program's grows): the fail-stop fires during
    the init, and the load refuses without starting anything. -/
theorem lebenslauf_zeuge_stopp :
    laden { arenen := [true], sperren := 1, antwort := 0, stopp := true, wurzeln := [true] } =
      ([Schritt.binde 0, Schritt.sperre 0, Schritt.init], false) := by decide

/-- A refused reservation: nothing of the unit runs. -/
theorem lebenslauf_zeuge_reserve :
    laden { arenen := [true, false, true], sperren := 2, antwort := 0, stopp := false,
            wurzeln := [true] } = ([Schritt.binde 0, Schritt.binde 1], false) := by decide

end ModulLaufzeit

end Gabbro.Grammatik
