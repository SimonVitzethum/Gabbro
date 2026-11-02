module
public import Grammatik.Bausteine.Schablonen.SchablonenModul.Teil1Basis
import all Grammatik.Bausteine.Schablonen.SchablonenModul.Teil1Basis


@[expose] public section


namespace Gabbro.Grammatik

namespace ModulLaufzeit
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
  | nil => simp only [bindeAlle, List.all_nil, List.not_mem_nil, not_false_eq_true, implies_true, List.length_nil,
  List.range_zero, List.map_nil, imp_self, and_self]
  | cons b rest ih =>
    cases b
    · simp only [bindeAlle, Bool.false_eq_true, ↓reduceIte, List.all_cons, id_eq, Bool.false_and, List.mem_cons,
  reduceCtorEq, List.not_mem_nil, or_self, not_false_eq_true, implies_true, List.length_cons, false_implies, and_self]
    · obtain ⟨h1, h2, h3, h4, h5⟩ := ih (i + 1)
      simp only [bindeAlle, if_true, List.all_cons, id, Bool.true_and]
      refine ⟨h1, ?_, ?_, ?_, ?_⟩
      · simp only [List.mem_cons, reduceCtorEq, h2, or_self, not_false_eq_true]
      · simp only [List.mem_cons, reduceCtorEq, h3, or_self, not_false_eq_true]
      · intro w; simp only [List.mem_cons, reduceCtorEq, h4 w, or_self, not_false_eq_true]
      · intro h
        rw [h5 h, List.length_cons, List.range_succ_eq_map]
        simp only [Nat.add_assoc, Nat.add_comm 1, List.map_cons, Nat.add_zero, List.map_map, Function.comp_def,
  Nat.succ_eq_add_one]

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
    · unfold laden at h; simp only [hn, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h
    · rfl
  have ha : L.antwort = 0 := by
    by_cases hn : L.antwort = 0
    · exact hn
    · unfold laden at h; simp only [hok, not_true_eq_false, ↓reduceIte, ne_eq, hn, not_false_eq_true, List.append_assoc,
  Bool.false_eq_true] at h
  have hs : L.stopp = false := by
    cases hn : L.stopp
    · rfl
    · unfold laden at h; simp only [hok, not_true_eq_false, ↓reduceIte, ha, ne_eq, hn, List.append_assoc, Bool.false_eq_true] at h
  have hw : L.wurzeln.all id = true := by
    cases hn : L.wurzeln.all id
    · unfold laden at h; simp only [hok, not_true_eq_false, ↓reduceIte, ha, ne_eq, hs, Bool.false_eq_true, hn, List.append_assoc,
  List.cons_append, List.nil_append] at h
    · rfl
  refine ⟨hA1 ▸ hok, ha, hs, hw, ?_⟩
  unfold laden
  simp only [hok, ha, hs, hw, not_true_eq_false, ne_eq, if_false, if_true, Bool.false_eq_true]
  rw [hA5 hok]; simp only [Nat.zero_add, List.append_assoc, List.cons_append, List.nil_append]

/-- **The unit's init runs only after every arena is bound** -- a refused reservation returns
    before any lock or any of the unit's code. -/
theorem laden_init_erst_nach_bindung (L : Lage) (h : Schritt.init ∈ (laden L).1) :
    L.arenen.all id = true := by
  obtain ⟨hA1, hA2, -, -, -⟩ := bindeAlle_spec 0 L.arenen
  unfold laden at h
  by_cases hok : (bindeAlle 0 L.arenen).2 = true
  · exact hA1 ▸ hok
  · simp only [hok, Bool.false_eq_true, not_false_eq_true, ↓reduceIte] at h; exact absurd h hA2

/-- **The load never calls the unit's exit** -- on a refusal the unit was never loaded. -/
theorem laden_ruft_kein_exit (L : Lage) : Schritt.exit ∉ (laden L).1 := by
  obtain ⟨-, -, hA3, -, -⟩ := bindeAlle_spec 0 L.arenen
  unfold laden
  by_cases hok : (bindeAlle 0 L.arenen).2 = true
  · simp only [hok, not_true_eq_false, if_false]
    split
    · simp only [List.append_assoc, List.mem_append, hA3, List.mem_map, List.mem_range, reduceCtorEq, and_false,
  exists_const, List.mem_cons, List.not_mem_nil, or_self, not_false_eq_true]
    · split
      · simp only [List.append_assoc, List.mem_append, hA3, List.mem_map, List.mem_range, reduceCtorEq, and_false,
  exists_const, List.mem_cons, List.not_mem_nil, or_self, not_false_eq_true]
      · split <;> simp only [List.append_assoc, List.cons_append, List.nil_append, List.mem_append, hA3, List.mem_map,
  List.mem_range, reduceCtorEq, and_false, exists_const, List.mem_cons, or_self, not_false_eq_true]
  · simp only [hok, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, hA3]

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
      · simp only [hs, ↓reduceIte, List.append_assoc, List.mem_append, hA4, List.mem_map, List.mem_range,
  reduceCtorEq, and_false, exists_const, List.mem_cons, List.not_mem_nil, or_self] at h
    · simp only [ne_eq, ha, not_false_eq_true, ↓reduceIte, List.append_assoc, List.mem_append, hA4, List.mem_map,
  List.mem_range, reduceCtorEq, and_false, exists_const, List.mem_cons, List.not_mem_nil, or_self] at h
  · simp only [hok, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, hA4] at h

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
        · simp only [hw, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append, Bool.true_eq_false] at hv
        · simp only [hw, Bool.false_eq_true, if_false] at h ⊢
          have hS : Schritt.start w ∉ (List.range L.sperren).map Schritt.sperre := by simp only [List.mem_map, List.mem_range, reduceCtorEq, and_false, exists_const, not_false_eq_true]
          have hk : w < L.wurzeln.length := by
            simp only [List.mem_append, List.mem_singleton] at h
            rcases h with (((h | h) | h) | h) | h
            · exact absurd h (hA4 w)
            · exact absurd h hS
            · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
            · simpa using h
            · simp only [List.mem_map, List.mem_range, reduceCtorEq, and_false, exists_const] at h
          simp only [List.mem_append, List.mem_map, List.mem_range]
          exact Or.inr ⟨w, hk, rfl⟩
      · simp only [hs, ↓reduceIte, List.append_assoc, List.mem_append, hA4, List.mem_map, List.mem_range,
  reduceCtorEq, and_false, exists_const, List.mem_cons, List.not_mem_nil, or_self] at h
    · simp only [ne_eq, ha, not_false_eq_true, ↓reduceIte, List.append_assoc, List.mem_append, hA4, List.mem_map,
  List.mem_range, reduceCtorEq, and_false, exists_const, List.mem_cons, List.not_mem_nil, or_self] at h
  · simp only [hok, Bool.false_eq_true, not_false_eq_true, ↓reduceIte, hA4] at h

/-- **The unload waits for every root before the unit's exit**, and calls the exit once. -/
theorem entladen_wartet_vor_exit (n w : Nat) (hw : w < n) :
    ∃ vor nach, entladen n = vor ++ [Schritt.exit] ++ nach ∧ Schritt.warte w ∈ vor ∧
      nach = [] := by
  refine ⟨(List.range n).map Schritt.warte, [], by simp only [entladen, List.append_nil], ?_, rfl⟩
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

/-! ## 3. `faden.modul` -- the roots as kernel threads, joined by a word

  The driver (`treiber.rs::erzeuge_kmod`, C-free lane C2 slice 3) owns one 32-bit join word per
  root, a zeroed static. Before the start it stores 1; it hands the designator of a wrapper to
  the binding's `gabbro_kern_faden_start` (an `entry fn`, `N575`-`N577`); the wrapper runs the
  root and THEN stores 0 (release). A start that fails stores the 0 itself. The wait re-reads
  the word (acquire) and sleeps through the binding until it reads 0. -/

/-- What happens to one root's join word, in the order it happens. -/
inductive FEreignis where
  | eins            -- the driver stores 1, before the start
  | startGut        -- the binding answered 0: a thread will run the wrapper
  | startFehl       -- the binding answered an errno: nothing runs
  | lauf            -- a step of the root, on its thread
  | ende            -- the wrapper's store of 0, after the root returned
  | null            -- the driver's store of 0 after a failed start
  deriving DecidableEq, Repr

/-- The word after a prefix of events, from whatever it held (`w0`). -/
def fwort (w0 : Nat) : List FEreignis → Nat
  | [] => w0
  | .eins :: r => fwort 1 r
  | .ende :: r => fwort 0 r
  | .null :: r => fwort 0 r
  | _ :: r => fwort w0 r

/-- **The two traces the template and the binding's contract allow.** A good start: 1, the
    start, the root's steps, then the wrapper's 0. A failed start: 1, the refusal, the driver's
    0 -- and no step of the root. -/
def fSpur : Bool → Nat → List FEreignis
  | true, k => .eins :: .startGut :: (List.replicate k .lauf ++ [.ende])
  | false, _ => [.eins, .startFehl, .null]

theorem fwort_replicate (w0 k : Nat) (r : List FEreignis) :
    fwort w0 (List.replicate k .lauf ++ r) = fwort w0 r := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.cons_append, fwort]; exact ih

theorem ftake_vor_dem_ende (k m : Nat) (r : List FEreignis) (h : m ≤ k) :
    (List.replicate k FEreignis.lauf ++ r).take m = List.replicate m FEreignis.lauf := by
  induction k generalizing m with
  | zero => simp only [Nat.le_zero_eq] at h; subst h; rfl
  | succ k ih =>
    cases m with
    | zero => rfl
    | succ m =>
      simp only [List.replicate_succ, List.cons_append, List.take_succ_cons]
      rw [ih m (by omega)]

theorem ftake_alles (k m : Nat) (h : k < m) :
    (List.replicate k FEreignis.lauf ++ [FEreignis.ende]).take m =
      List.replicate k FEreignis.lauf ++ [FEreignis.ende] := by
  apply List.take_of_length_le
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil, Nat.zero_add]; omega

/-- **Soundness of the join (`faden_modul_warte_korrekt`).** The wait begins after the start
    returned -- a prefix holding the store of 1 and the start's answer (`n ≥ 2`) -- and returns
    only on reading 0. Then EITHER the root's whole run is in what it saw, its last step and the
    wrapper's 0 included (a good start), OR the start failed and no step of the root exists.
    Whatever the root's length and wherever the waiter looks. -/
theorem faden_modul_warte_korrekt (gut : Bool) (k w0 n : Nat) (hn : 2 ≤ n)
    (h0 : fwort w0 ((fSpur gut k).take n) = 0) :
    (gut = true ∧ (fSpur gut k).take n = fSpur gut k) ∨
      (gut = false ∧ FEreignis.lauf ∉ fSpur gut k) := by
  cases gut with
  | false => right; exact ⟨rfl, by simp only [fSpur, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, not_false_eq_true]⟩
  | true =>
    left
    refine ⟨rfl, ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    simp only [fSpur, List.take_succ_cons] at h0 ⊢
    by_cases hm : m ≤ k
    · exfalso
      simp only [fwort] at h0
      rw [ftake_vor_dem_ende k m _ hm] at h0
      have e := fwort_replicate 1 m []
      simp only [List.append_nil] at e
      rw [e] at h0
      simp only [fwort, Nat.succ_ne_self] at h0
    · rw [ftake_alles k m (by omega)]

/-- The store of 1 is not decoration: the word is a ZEROED static, so without it a waiter that
    looks right after a good start reads the old 0 and returns before the root ran a step --
    the unload would then call the unit's exit beside a running root. -/
theorem faden_modul_ohne_eins :
    fwort 0 ([FEreignis.startGut, .lauf, .ende].take 1) = 0 ∧
    FEreignis.lauf ∉ [FEreignis.startGut, .lauf, .ende].take 1 := by decide

/-- And the wrapper's ORDER is not decoration: a wrapper that stored 0 before running the root
    lets a waiter return while the root still has steps to run. -/
theorem faden_modul_null_zuerst :
    fwort 1 ([FEreignis.eins, .startGut, .ende, .lauf].take 3) = 0 ∧
    [FEreignis.eins, .startGut, .ende, .lauf].take 3 ≠ [FEreignis.eins, .startGut, .ende, .lauf] :=
  by decide

end ModulLaufzeit
end Gabbro.Grammatik
