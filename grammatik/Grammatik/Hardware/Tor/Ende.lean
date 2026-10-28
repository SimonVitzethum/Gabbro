/-
  File:      Grammatik/Hardware/Tor/Ende.lean
  Subject:   L3 -- THE PROCESS-EXIT GATE (`proc main exit G`), and the ordering behind L4's thread
             start/join and stack release.  PLAN-HARDWARE.md sections 16.4, 16.5.

  The compiler wrote `_start` itself: call `main`, then `exit_group` with a Linux number
  (`emit_start`, audit item A5). The proposal: the PROGRAM declares the process entry and the gate
  that ends the process,

      proc main exit G;          // `main : fn() -> i32` (or `-> u8`), `G` a gate declared `-> never`

  where a gate declared `-> never` is an ordinary gate that does not return (the language has `Ty.never` and the stop kind `nieZurueck`: the process, with every thread, is over). Machine G is untouched: the `StartEndeG` leg of the goal
  already says every declared start RETURNS; what happens after the return is the runtime's, and the
  new form names it as one gate call whose contract is the program's named assumption.

  The model: a task's observable run is a list of events, a step of the body or the end event with
  the exit code. `startSpur` is what the generated entry does with a run of `main`:
    * `main` returns `c`  -> its steps, then ONE `ende c`, then nothing (`start_*` theorems);
    * `main` never returns -> its steps and no `ende` (the stub never invents an exit).
  Planted defects: a stub that falls off the end (no exit gate call) and one that keeps going after the
  gate returns are each NOT `EndeGut`.

  Second part (L4): the thread-start/join ORDER. The spawn gate's contract (a named assumption, the
  proved shape of `SchablonenFaden.lean`'s `faden_warte_korrekt`) is: the environment clears the join
  word AFTER the child's last step; the parent's `await` returns only after the clear; the stack is
  released (pool `drop`) only after the `await`. `JoinGut` derives from those orders that no child
  step follows the stack release (`kein_kind_nach_gib`).

  No `sorry`, no `native_decide`, no new axiom.
-/

namespace Gabbro.Grammatik.Tor

/-! ## 1. Process exit -/

/-- An event of a task: a step of the body, or the end gate call with the exit code. -/
inductive Ev (S : Type) where
  | schritt (s : S)
  | ende (code : Int)
  deriving DecidableEq, Repr

variable {S : Type}

/-- The end event is the LAST event, and there is at most one: nothing follows the gate. -/
def EndeGut (tr : List (Ev S)) : Prop :=
  ∀ (i j : Nat) (c : Int), tr[i]? = some (Ev.ende c) → i < j → tr[j]? = none

/-- What the generated entry does with a run of `main`: `none` is a `main` that never returns. -/
def startSpur (lauf : List S) : Option Int → List (Ev S)
  | none => lauf.map .schritt
  | some c => lauf.map .schritt ++ [.ende c]

/-- A returning `main` ends in exactly one end event, with `main`'s own result as the code. -/
theorem start_code (lauf : List S) (c : Int) :
    (startSpur lauf (some c)).getLast? = some (Ev.ende c) := by
  simp only [startSpur, List.getLast?_append, List.getLast?_singleton, List.getLast?_map, Option.some_or]

/-- A present element lies inside the list. -/
theorem lt_of_get {α : Type} {tr : List α} {i : Nat} {x : α} (h : tr[i]? = some x) :
    i < tr.length := by
  cases Nat.lt_or_ge i tr.length with
  | inl hl => exact hl
  | inr hn =>
      rw [List.getElem?_eq_none hn] at h
      simp only [reduceCtorEq] at h

/-- Nothing follows the end event. -/
theorem start_ende_gut (lauf : List S) (c : Option Int) : EndeGut (startSpur lauf c) := by
  intro i j d hi hij
  cases c with
  | none =>
      simp only [startSpur] at hi
      simp only [List.getElem?_map, Option.map_eq_some_iff, reduceCtorEq, and_false, exists_false] at hi
  | some c =>
      simp only [startSpur] at hi ⊢
      have hlen : (lauf.map Ev.schritt ++ [Ev.ende c]).length = lauf.length + 1 := by simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, Nat.zero_add,
  Nat.add_left_cancel_iff]
      have hi' := lt_of_get hi
      have hge : lauf.length ≤ i := by
        cases Nat.lt_or_ge i lauf.length with
        | inl hl =>
            rw [List.getElem?_append_left (by simpa using hl)] at hi
            simp only [List.getElem?_map, List.getElem?_eq_getElem hl, Option.map_some, Option.some.injEq,
  reduceCtorEq] at hi
        | inr hg => exact hg
      exact List.getElem?_eq_none (by omega)


/-- A `main` that never returns makes no end event: the stub never invents an exit. -/
theorem start_ohne_rueckkehr (lauf : List S) : ∀ e ∈ startSpur lauf none, ∃ s, e = .schritt s := by
  intro e he
  simp only [startSpur, List.mem_map] at he
  obtain ⟨s, -, rfl⟩ := he
  exact ⟨s, rfl⟩

/-- Defect: a stub that falls off the end of `main` (no gate call) leaves the exit code undelivered. -/
def startOhneExit (lauf : List S) (_c : Int) : List (Ev S) := lauf.map .schritt

theorem ohne_exit_kein_ende (lauf : List S) (c : Int) :
    (startOhneExit lauf c).getLast? ≠ some (Ev.ende c) := by
  intro h
  simp only [startOhneExit] at h
  have := List.mem_of_getLast? h
  simp only [List.mem_map, reduceCtorEq, and_false, exists_false] at this

/-- Defect: a stub that keeps stepping after the gate returned. -/
def startMitNachlauf (lauf : List S) (c : Int) (s : S) : List (Ev S) :=
  lauf.map .schritt ++ [.ende c, .schritt s]

theorem nachlauf_nicht_ende_gut (lauf : List S) (c : Int) (s : S) :
    ¬ EndeGut (startMitNachlauf lauf c s) := by
  intro h
  have h1 : (startMitNachlauf lauf c s)[lauf.length]? = some (Ev.ende c) := by
    simp only [startMitNachlauf, List.length_append, List.length_map, List.length_cons, List.length_nil,
  Nat.zero_add, Nat.reduceAdd, Nat.lt_add_right_iff_pos, Nat.zero_lt_succ, getElem?_pos, Std.le_refl,
  List.getElem_append_right, Nat.sub_self, List.getElem_cons_zero]
  have h2 := h lauf.length (lauf.length + 1) c h1 (by omega)
  simp only [startMitNachlauf, List.length_append, List.length_map, List.length_cons, List.length_nil,
  Nat.zero_add, Nat.reduceAdd, Nat.lt_add_one, getElem?_pos, Nat.le_add_right, List.getElem_append_right,
  Nat.add_sub_cancel_left, List.getElem_cons_succ, List.getElem_cons_zero, reduceCtorEq] at h2

/-- Witness: a three-step `main` returning 7. -/
theorem start_zeuge :
    startSpur [1, 2, 3] (some 7) = [.schritt 1, .schritt 2, .schritt 3, .ende 7] ∧
    EndeGut (startSpur [1, 2, 3] (some 7)) ∧
    (startSpur [1, 2, 3] (some 7)).getLast? = some (Ev.ende 7) :=
  ⟨rfl, start_ende_gut _ _, start_code _ _⟩

/-! ## 2. Thread end, join, stack release (L4) -/

/-- The events of one spawned thread and its parent, in the one global order. -/
inductive TEr (S : Type) where
  | kind (s : S)      -- a step of the child
  | endet             -- the child's last step is over (its exit gate was called)
  | loescht           -- the environment clears the join word
  | wartet            -- the parent's `await` on the join word returns
  | gib               -- the parent releases the stack (pool `drop`)
  deriving DecidableEq, Repr

/-- **The join order** the spawn gate's contract and the generated wait promise: the stack is released
    only after the `await` returned, which returned only after the clear, which came after the end; and
    the child takes no step after its end. -/
structure JoinGut (tr : List (TEr S)) : Prop where
  gibNach : ∀ i : Nat, tr[i]? = some TEr.gib → ∃ j < i, tr[j]? = some TEr.wartet
  wartetNach : ∀ i : Nat, tr[i]? = some TEr.wartet → ∃ j < i, tr[j]? = some TEr.loescht
  loeschtNach : ∀ i : Nat, tr[i]? = some TEr.loescht → ∃ j < i, tr[j]? = some TEr.endet
  kindNie : ∀ j : Nat, tr[j]? = some TEr.endet → ∀ i : Nat, j < i → ∀ s, tr[i]? ≠ some (TEr.kind s)

/-- **No child step follows the stack release.** -/
theorem kein_kind_nach_gib {tr : List (TEr S)} (h : JoinGut tr) :
    ∀ i : Nat, tr[i]? = some TEr.gib → ∀ k : Nat, i < k → ∀ s, tr[k]? ≠ some (TEr.kind s) := by
  intro i hi k hik s
  obtain ⟨j1, hj1, hw⟩ := h.gibNach i hi
  obtain ⟨j2, hj2, hl⟩ := h.wartetNach j1 hw
  obtain ⟨j3, hj3, he⟩ := h.loeschtNach j2 hl
  exact h.kindNie j3 he k (by omega) s

/-- A wait that returned BEFORE the clear (the defect the join word exists to prevent) breaks the
    order: a release right after such a wait can overlap a running child. -/
theorem join_defekt : ¬ JoinGut ([.kind 0, .wartet, .gib, .loescht, .endet] : List (TEr Nat)) := by
  intro h
  obtain ⟨j, hj, he⟩ := h.wartetNach 1 rfl
  simp only [Nat.lt_one_iff] at hj
  subst hj
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.zero_lt_succ, getElem?_pos,
  List.getElem_cons_zero, Option.some.injEq, reduceCtorEq] at he

/-- Witness: the proper order of a child that takes two steps. -/
theorem join_zeuge : JoinGut ([.kind 0, .kind 1, .endet, .loescht, .wartet, .gib] : List (TEr Nat)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    have hl := lt_of_get hi
    simp only [List.length_cons, List.length_nil] at hl
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | (simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Option.some.injEq, reduceCtorEq, Nat.reduceLT, List.getElem_cons_succ] at hi; done) | exact ⟨4, by decide, rfl⟩
  · intro i hi
    have hl := lt_of_get hi
    simp only [List.length_cons, List.length_nil] at hl
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | (simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Option.some.injEq, reduceCtorEq, Nat.reduceLT, List.getElem_cons_succ, Nat.lt_add_one] at hi; done) | exact ⟨3, by decide, rfl⟩
  · intro i hi
    have hl := lt_of_get hi
    simp only [List.length_cons, List.length_nil] at hl
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | (simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Option.some.injEq, reduceCtorEq, Nat.reduceLT, List.getElem_cons_succ, Nat.lt_add_one] at hi; done) | exact ⟨2, by decide, rfl⟩
  · intro j hj i hji s hi
    have hl := lt_of_get hj
    have hl2 := lt_of_get hi
    simp only [List.length_cons, List.length_nil] at hl hl2
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.zero_lt_succ, getElem?_pos, List.getElem_cons_zero, Option.some.injEq, reduceCtorEq, Nat.reduceLT, List.getElem_cons_succ, TEr.kind.injEq, Nat.not_lt_zero, Nat.lt_one_iff, Nat.lt_add_one] at hj hi hji

end Gabbro.Grammatik.Tor
