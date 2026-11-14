/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Geist.lean
  Subject:   THE ABSTRACT TICKET LOCK SIMULATES THE MODEL'S TICKET LOCK. The model's lock (Code/Conc/LockRel.lean)
             keeps the ghost state `Tkt`: `s` tickets served, `n` handed out, `who i` the owner of ticket `i`,
             `inside` whether the holder of ticket `s` entered; it moves by `Tkt.take`, `Tkt.enter`, `Tkt.leave`, the
             ghost moves of `take_step`, `spin_enter_step` and `release_step`. `Passt t a` says that the abstract
             lock `a` (Faeden/Abstrakt.lean, threads `Nat`) is what `t` shows: the holder is the owner of ticket `s`
             while inside, the queue is the owners of the outstanding tickets after it, in ticket order. Then each
             abstract step is the model's ghost move of the SAME thread, with exactly the preconditions those three
             lemmas ask for, and `Tkt.Ok` is kept:
             * `passt_zieht` -- a draw `Zieht u` is `Tkt.take u`, with `u` owning no outstanding ticket (`take_step`'s
               `hnq`); fewer than `2 ^ wbits` tickets are outstanding (its `hroom`) when the queue after the draw is
               shorter than `2 ^ wbits - 1`;
             * `passt_tritt` -- an enter `Tritt u` is `Tkt.enter`, with `u` owning the served ticket `s < n` and
               nobody inside (`spin_enter_step`'s `hq`, `ha`);
             * `passt_gibt` -- a give `Gibt u` is `Tkt.leave`, with `u` owning ticket `s` and inside (`release_step`'s
               `hin`, `hwho`).
-/
module
public import Stage0.Senke.Sperre.Faeden.Abstrakt
public import Grammatik.Code.Conc.LockRel
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

open Gabbro.Code (Conf)
open Gabbro.Code.Lower (Tkt take_ok enter_ok leave_ok)

/-! ## 1. What a ghost state shows -/

/-- The first waiting ticket: the served one, or the one after it while its holder is inside. -/
def tErst (t : Tkt) : Nat := t.s + t.inside.toNat

/-- The holder: the owner of the served ticket while it is inside. -/
def tHalter (t : Tkt) : Option Nat := if t.inside = true then t.who t.s else none

/-- The waiting threads: the owners of the outstanding tickets from `tErst`, in ticket order. -/
def tWarte (t : Tkt) : List Nat := (List.range' (tErst t) (t.n - tErst t)).filterMap t.who

/-- **The abstract lock of a ghost state.** -/
def tBild (t : Tkt) : Abs Nat := ⟨tHalter t, tWarte t⟩

section

variable [Conf]

/-- **The abstract lock `a` is what the well-formed ghost state `t` shows**, with one owner per outstanding ticket. -/
structure Passt (t : Tkt) (a : Abs Nat) : Prop where
  ok : t.Ok
  halter : a.holder = tHalter t
  warte : a.queue = tWarte t
  laenge : t.n = tErst t + a.queue.length

theorem Passt.bild {t : Tkt} {a : Abs Nat} (P : Passt t a) : tBild t = a := by
  obtain ⟨h, q⟩ := a
  have e1 : h = tHalter t := P.halter
  have e2 : q = tWarte t := P.warte
  subst e1 e2
  rfl

end

/-! ## 2. The ghost moves of the model's lock, by one thread -/

/-- `take_step`: `u` owns no outstanding ticket and takes the next one. -/
def TZieht (u : Nat) (t t' : Tkt) : Prop := (∀ i, t.s ≤ i → i < t.n → t.who i ≠ some u) ∧ t' = t.take u

/-- `spin_enter_step`: nobody inside, `u` owns the served ticket, and enters. -/
def TTritt (u : Nat) (t t' : Tkt) : Prop := t.inside = false ∧ t.s < t.n ∧ t.who t.s = some u ∧ t' = t.enter

/-- `release_step`: `u` owns the served ticket, is inside, and releases. -/
def TGibt (u : Nat) (t t' : Tkt) : Prop := t.inside = true ∧ t.who t.s = some u ∧ t' = t.leave

/-- At most one move of `r`. -/
def OptT (r : Tkt → Tkt → Prop) (t t' : Tkt) : Prop := t = t' ∨ r t t'

/-- **What one step of machine G by `u` does to the ghost of one lock**: a release, a take, an enter, each
    optional, in this order (the ghost side of `Weg`). -/
def TWeg (u : Nat) (t d : Tkt) : Prop :=
  ∃ b c, OptT (TGibt u) t b ∧ OptT (TZieht u) b c ∧ OptT (TTritt u) c d

/-! ## 3. Small facts -/

theorem take_s (t : Tkt) (u : Nat) : (t.take u).s = t.s := rfl
theorem take_n (t : Tkt) (u : Nat) : (t.take u).n = t.n + 1 := rfl
theorem take_inside (t : Tkt) (u : Nat) : (t.take u).inside = t.inside := rfl
theorem take_who_ne {t : Tkt} {u i : Nat} (h : i ≠ t.n) : (t.take u).who i = t.who i := by
  unfold Tkt.take
  exact if_neg h
theorem take_who_n (t : Tkt) (u : Nat) : (t.take u).who t.n = some u := by
  unfold Tkt.take
  exact if_pos rfl
theorem erst_take (t : Tkt) (u : Nat) : tErst (t.take u) = tErst t := rfl

theorem enter_n (t : Tkt) : t.enter.n = t.n := rfl
theorem enter_inside (t : Tkt) : t.enter.inside = true := rfl
theorem enter_who (t : Tkt) : t.enter.who = t.who := rfl
theorem enter_s (t : Tkt) : t.enter.s = t.s := rfl

theorem leave_n (t : Tkt) : t.leave.n = t.n := rfl
theorem leave_inside (t : Tkt) : t.leave.inside = false := rfl
theorem leave_who (t : Tkt) : t.leave.who = t.who := rfl
theorem leave_s (t : Tkt) : t.leave.s = t.s + 1 := rfl

theorem erst_wahr {t : Tkt} (h : t.inside = true) : tErst t = t.s + 1 := by
  simp only [tErst, h, Bool.toNat_true]

theorem erst_falsch {t : Tkt} (h : t.inside = false) : tErst t = t.s := by
  simp only [tErst, h, Bool.toNat_false, Nat.add_zero]

theorem erst_ge (t : Tkt) : t.s ≤ tErst t := Nat.le_add_right _ _

theorem erst_le (t : Tkt) : tErst t ≤ t.s + 1 := by
  cases h : t.inside <;> simp only [tErst, h, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- Two owner functions that agree on a range of tickets give the same owners. -/
theorem fm_congr {f g : Nat → Option Nat} : ∀ (k lo : Nat), (∀ i, lo ≤ i → i < lo + k → f i = g i) →
    (List.range' lo k).filterMap f = (List.range' lo k).filterMap g
  | 0, _, _ => rfl
  | k + 1, lo, h => by
    rw [List.range'_succ, List.filterMap_cons, List.filterMap_cons, h lo (Nat.le_refl lo) (by omega),
      fm_congr k (lo + 1) (fun i h1 h2 => h i (by omega) (by omega))]

/-! ## 4. Each abstract step is the ghost move of the same thread -/

section

variable [Conf]

/-- **A draw is `Tkt.take`.** -/
theorem passt_zieht {t : Tkt} {a b : Abs Nat} {u : Nat} (P : Passt t a) (h : Zieht u a b)
    (hb : b.queue.length + 1 < 2 ^ Conf.wbits) : Passt (t.take u) b ∧ TZieht u t (t.take u) := by
  obtain ⟨hu, hh, rfl⟩ := h
  have hel : tErst t ≤ t.n := by have := P.laenge; omega
  have hnq : ∀ i, t.s ≤ i → i < t.n → t.who i ≠ some u := by
    intro i h1 h2 hw
    by_cases hi : t.inside = true ∧ i = t.s
    · apply hh
      rw [P.halter, tHalter, if_pos hi.1, ← hi.2, hw]
    · have hei : tErst t ≤ i := by
        cases hin : t.inside
        · rw [erst_falsch hin]; exact h1
        · rw [erst_wahr hin]
          have : i ≠ t.s := fun e => hi ⟨hin, e⟩
          omega
      apply hu
      rw [P.warte, tWarte, List.mem_filterMap]
      exact ⟨i, List.mem_range'_1.2 ⟨hei, by omega⟩, hw⟩
  have hb' : a.queue.length + 1 + 1 < 2 ^ Conf.wbits := by simpa using hb
  have hroom : t.n + 1 - t.s < 2 ^ Conf.wbits := by
    have h1 := P.laenge
    have h2 := erst_le t
    have h3 := erst_ge t
    omega
  refine ⟨⟨take_ok P.ok u hnq hroom, ?_, ?_, ?_⟩, hnq, rfl⟩
  · show a.holder = tHalter (t.take u)
    rw [P.halter]
    unfold tHalter
    rw [take_inside, take_s]
    by_cases hin : t.inside = true
    · rw [if_pos hin, if_pos hin, take_who_ne (t := t) (u := u) (i := t.s) (by have := P.ok.held hin; omega)]
    · rw [if_neg hin, if_neg hin]
  · show a.queue ++ [u] = tWarte (t.take u)
    rw [P.warte]
    unfold tWarte
    rw [erst_take, take_n, show t.n + 1 - tErst t = (t.n - tErst t) + 1 by omega, List.range'_1_concat,
      List.filterMap_append, show tErst t + (t.n - tErst t) = t.n by omega,
      fm_congr (f := (t.take u).who) (g := t.who) (t.n - tErst t) (tErst t)
        (fun i _ h2 => take_who_ne (t := t) (u := u) (i := i) (by omega)),
      List.filterMap_cons_some (take_who_n t u), List.filterMap_nil]
  · show t.n + 1 = tErst t + (a.queue ++ [u]).length
    have h1 := P.laenge
    have h2 : (a.queue ++ [u]).length = a.queue.length + 1 := by simp
    omega

/-- **An enter is `Tkt.enter`.** -/
theorem passt_tritt {t : Tkt} {a b : Abs Nat} {u : Nat} (P : Passt t a) (h : Tritt u a b) :
    Passt t.enter b ∧ TTritt u t t.enter := by
  obtain ⟨ha, hq, rfl⟩ := h
  have hin : t.inside = false := by
    cases hin : t.inside
    · rfl
    · exfalso
      obtain ⟨v, hv⟩ := P.ok.owned t.s (Nat.le_refl _) (P.ok.held hin)
      have e := P.halter
      rw [ha, tHalter, if_pos hin, hv] at e
      cases e
  have he := erst_falsch hin
  obtain ⟨r, hr⟩ := List.head?_eq_some_iff.1 hq
  have hlen := P.laenge
  rw [hr, he, List.length_cons] at hlen
  have hk : t.n - t.s = r.length + 1 := by omega
  have hw := P.warte
  obtain ⟨v, hv⟩ := P.ok.owned t.s (Nat.le_refl _) (by omega)
  rw [hr, tWarte, he, hk, List.range'_succ, List.filterMap_cons_some hv] at hw
  obtain ⟨hvu, hrest⟩ := List.cons.inj hw
  rw [← hvu] at hv
  have e1 : tErst t.enter = t.s + 1 := erst_wahr (enter_inside t)
  refine ⟨⟨enter_ok P.ok (by omega), ?_, ?_, ?_⟩, hin, by omega, hv, rfl⟩
  · show some u = tHalter t.enter
    unfold tHalter
    rw [if_pos (enter_inside t), enter_who, enter_s, hv]
  · show a.queue.tail = tWarte t.enter
    unfold tWarte
    rw [e1, enter_n, enter_who, show t.n - (t.s + 1) = r.length by omega, hr, List.tail_cons]
    exact hrest
  · show t.n = tErst t.enter + a.queue.tail.length
    rw [e1, hr, List.tail_cons]
    omega

/-- **A give is `Tkt.leave`.** -/
theorem passt_gibt {t : Tkt} {a b : Abs Nat} {u : Nat} (P : Passt t a) (h : Gibt u a b) :
    Passt t.leave b ∧ TGibt u t t.leave := by
  obtain ⟨ha, rfl⟩ := h
  have e := P.halter
  rw [ha] at e
  have hin : t.inside = true := by
    cases hin : t.inside
    · rw [tHalter, if_neg (show ¬ (t.inside = true) by simp [hin])] at e
      cases e
    · rfl
  have hw : t.who t.s = some u := by
    rw [tHalter, if_pos hin] at e
    exact e.symm
  have e1 : tErst t.leave = tErst t := (erst_falsch (leave_inside t)).trans (erst_wahr hin).symm
  refine ⟨⟨leave_ok P.ok hin, ?_, ?_, ?_⟩, hin, hw, rfl⟩
  · show none = tHalter t.leave
    unfold tHalter
    rw [if_neg (show ¬ (t.leave.inside = true) by simp [leave_inside])]
  · show a.queue = tWarte t.leave
    unfold tWarte
    rw [e1, leave_n, leave_who]
    exact P.warte
  · show t.n = tErst t.leave + a.queue.length
    rw [e1]
    exact P.laenge

end

end Gabbro.Stage0.Senke.Faeden
