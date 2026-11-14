/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Kette.lean
  Subject:   THE QUIET SITUATION IS IMPOSSIBLE under weak fairness (`Ruhe.falsch`). In it `serving` stays `s`, the
             head `h` holds ticket `s` and never the lock, nobody wakes, the waiter word stays `W0`. Walk `h` along
             its code: at the serving test it would enter; FUTEX_WAIT with its older serving value returns at once
             (the futex compares the low 32 bits, and `serving` is fewer than 2^31 tickets ahead); a fresh `cas` on
             the waiter word succeeds and changes the word; blocked, it was counted, so some pending waker reads a
             nonzero waiter word and makes a FUTEX_WAKE (no lost wake-up, `Inv.nolost`). Each place ends in a
             contradiction within at most four fair steps of `h` or of a waker.
-/
module
public import Stage0.Senke.Sperre.Faeden.Stau
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

variable {N : Nat}

/-- The low 32 bits of a serving value fewer than 2^31 tickets back differ from those of the ticket. -/
theorem alt_ne (hN : N ≤ 2147483647) {w : Wort} {s s0 : Nat} (hw : Wartet N w s s0) :
    s % 4294967296 ≠ s0 % 4294967296 := by
  obtain ⟨_, h2, h3⟩ := hw
  omega

variable {R : Lauf N} {m s W0 : Nat} {h : Fin N}

theorem Ruhe.W0_lt (hN : N ≤ 2147483647) (Q : Ruhe R m s h W0) : W0 < 18446744073709551616 := by
  have h1 := Q.wait m (Nat.le_refl m)
  have h2 := (Q.inv m).wait
  have h3 := List.countP_le_length (p := fun u => ((R.z m).pc u).gezaehlt) (l := (R.z m).q)
  have h4 := (Q.inv m).laenge
  omega

theorem Ruhe.wartet (Q : Ruhe R m s h W0) {j : Nat} {o : Ort} (hp : (R.z j).pc h = o) : OrtOK N (R.z j).w o := by
  have hx := (Q.inv j).ort h
  rw [hp] at hx
  exact hx

/-! ## 1. Wakers -/

theorem Ruhe.kein_weck (hF : R.Fair) (Q : Ruhe R m s h W0) {j : Nat} (hj : m ≤ j) (g : Fin N) :
    (R.z j).pc g ≠ .weck := by
  intro hp
  obtain ⟨j', hj', ha, hp'⟩ := R.kommt hF (o := .weck) rfl hp
  exact Q.weck j' (Nat.le_trans hj hj') g ha hp'

theorem Ruhe.kein_gibW (hF : R.Fair) (Q : Ruhe R m s h W0) (hW0 : W0 ≠ 0) {j : Nat} (hj : m ≤ j)
    (g : Fin N) : (R.z j).pc g ≠ .gibW := by
  intro hp
  obtain ⟨j', hj', ha, hp'⟩ := R.kommt hF (o := .gibW) rfl hp
  rcases (R.schritt j' g ha).von_gibW hp' with ⟨e, _⟩ | ⟨_, e⟩
  · exact hW0 (by rw [← Q.wait j' (Nat.le_trans hj hj'), e])
  · exact Q.kein_weck hF (Nat.le_trans hj (Nat.le_succ_of_le hj')) g e

theorem Ruhe.nicht_blockiert (hN : N ≤ 2147483647) (hF : R.Fair) (Q : Ruhe R m s h W0) {j : Nat}
    (hj : m ≤ j) {s0 : Nat} (hp : (R.z j).pc h = .blockiert s s0) : False := by
  have hw : Wartet N (R.z j).w s s0 := Q.wartet hp
  rcases (Q.inv j).nolost h s s0 hp with e | ⟨g, hg⟩
  · rw [Q.serv j hj] at e
    exact alt_ne hN hw e
  · have hW0 : W0 ≠ 0 := by
      rw [← Q.wait j hj, (Q.inv j).wait]
      have hm : h ∈ (R.z j).q := ((Q.inv j).mem h).2 (by simp [Q.tk j hj])
      exact Nat.pos_iff_ne_zero.1 (List.countP_pos_iff.2 ⟨h, hm, by simp [hp, Ort.gezaehlt]⟩)
    rcases weckt_ort hg with e | e
    · exact Q.kein_gibW hF hW0 hj g e
    · exact Q.kein_weck hF hj g e

/-! ## 2. The places of the head -/

theorem Ruhe.nicht_ladeS (hF : R.Fair) (Q : Ruhe R m s h W0) {j : Nat} (hj : m ≤ j)
    (hp : (R.z j).pc h = .ladeS s) : False := by
  obtain ⟨j', hj', ha, hp'⟩ := R.kommt hF (o := .ladeS s) rfl hp
  rcases (R.schritt j' h ha).von_ladeS hp' with e | ⟨e, _⟩
  · have hx := Q.nie (j' + 1) (Nat.le_trans hj (Nat.le_succ_of_le hj'))
    rw [e] at hx
    simp [Ort.haelt] at hx
  · exact e (by rw [Q.serv j' (Nat.le_trans hj hj')])

theorem Ruhe.nicht_decC0 (hN : N ≤ 2147483647) (hF : R.Fair) (Q : Ruhe R m s h W0) {j : Nat} (hj : m ≤ j)
    {s0 : Nat} (hp : (R.z j).pc h = .decC s s0 W0) : False := by
  obtain ⟨j', hj', ha, hp'⟩ := R.kommt hF (o := .decC s s0 W0) rfl hp
  have hw1 := Q.wait j' (Nat.le_trans hj hj')
  have hw2 := Q.wait (j' + 1) (Nat.le_trans hj (Nat.le_succ_of_le hj'))
  have hlt := Q.W0_lt hN
  rcases (R.schritt j' h ha).von_decC hp' with ⟨_, e⟩ | ⟨e, _⟩
  · rw [hw2] at e
    try rw [wrapDec_eq] at e
    omega
  · exact e hw1

theorem Ruhe.nicht_decL (hN : N ≤ 2147483647) (hF : R.Fair) (Q : Ruhe R m s h W0) {j : Nat} (hj : m ≤ j)
    {s0 : Nat} (hp : (R.z j).pc h = .decL s s0) : False := by
  obtain ⟨j', hj', ha, hp'⟩ := R.kommt hF (o := .decL s s0) rfl hp
  have e := (R.schritt j' h ha).von_decL hp'
  rw [Q.wait j' (Nat.le_trans hj hj')] at e
  exact Q.nicht_decC0 hN hF (Nat.le_trans hj (Nat.le_succ_of_le hj')) e

theorem Ruhe.nicht_decC (hN : N ≤ 2147483647) (hF : R.Fair) (Q : Ruhe R m s h W0) {j : Nat} (hj : m ≤ j)
    {s0 lw : Nat} (hp : (R.z j).pc h = .decC s s0 lw) : False := by
  obtain ⟨j', hj', ha, hp'⟩ := R.kommt hF (o := .decC s s0 lw) rfl hp
  have hw1 := Q.wait j' (Nat.le_trans hj hj')
  have hw2 := Q.wait (j' + 1) (Nat.le_trans hj (Nat.le_succ_of_le hj'))
  have hlt := Q.W0_lt hN
  rcases (R.schritt j' h ha).von_decC hp' with ⟨e1, e⟩ | ⟨_, e⟩
  · rw [hw2] at e
    try rw [wrapDec_eq] at e
    rw [hw1] at e1
    omega
  · exact Q.nicht_decL hN hF (Nat.le_trans hj (Nat.le_succ_of_le hj')) e

theorem Ruhe.nicht_futexW (hN : N ≤ 2147483647) (hF : R.Fair) (Q : Ruhe R m s h W0) {j : Nat} (hj : m ≤ j)
    {s0 : Nat} (hp : (R.z j).pc h = .futexW s s0) : False := by
  obtain ⟨j', hj', ha, hp'⟩ := R.kommt hF (o := .futexW s s0) rfl hp
  have hw : Wartet N (R.z j').w s s0 := Q.wartet hp'
  rcases (R.schritt j' h ha).von_futexW hp' with e | e
  · rw [Q.serv j' (Nat.le_trans hj hj')] at e
    exact alt_ne hN hw e
  · exact Q.nicht_decL hN hF (Nat.le_trans hj (Nat.le_succ_of_le hj')) e

theorem Ruhe.nicht_incC0 (hN : N ≤ 2147483647) (hF : R.Fair) (Q : Ruhe R m s h W0) {j : Nat} (hj : m ≤ j)
    {s0 : Nat} (hp : (R.z j).pc h = .incC s s0 W0) : False := by
  obtain ⟨j', hj', ha, hp'⟩ := R.kommt hF (o := .incC s s0 W0) rfl hp
  have hw1 := Q.wait j' (Nat.le_trans hj hj')
  have hw2 := Q.wait (j' + 1) (Nat.le_trans hj (Nat.le_succ_of_le hj'))
  have hlt := Q.W0_lt hN
  rcases (R.schritt j' h ha).von_incC hp' with ⟨_, e⟩ | ⟨e, _⟩
  · rw [hw2] at e
    try rw [wrapDec_eq] at e
    omega
  · exact e hw1

theorem Ruhe.nicht_incL (hN : N ≤ 2147483647) (hF : R.Fair) (Q : Ruhe R m s h W0) {j : Nat} (hj : m ≤ j)
    {s0 : Nat} (hp : (R.z j).pc h = .incL s s0) : False := by
  obtain ⟨j', hj', ha, hp'⟩ := R.kommt hF (o := .incL s s0) rfl hp
  have e := (R.schritt j' h ha).von_incL hp'
  rw [Q.wait j' (Nat.le_trans hj hj')] at e
  exact Q.nicht_incC0 hN hF (Nat.le_trans hj (Nat.le_succ_of_le hj')) e

theorem Ruhe.nicht_incC (hN : N ≤ 2147483647) (hF : R.Fair) (Q : Ruhe R m s h W0) {j : Nat} (hj : m ≤ j)
    {s0 lw : Nat} (hp : (R.z j).pc h = .incC s s0 lw) : False := by
  obtain ⟨j', hj', ha, hp'⟩ := R.kommt hF (o := .incC s s0 lw) rfl hp
  have hw1 := Q.wait j' (Nat.le_trans hj hj')
  have hw2 := Q.wait (j' + 1) (Nat.le_trans hj (Nat.le_succ_of_le hj'))
  have hlt := Q.W0_lt hN
  rcases (R.schritt j' h ha).von_incC hp' with ⟨e1, e⟩ | ⟨_, e⟩
  · rw [hw2] at e
    try rw [wrapDec_eq] at e
    rw [hw1] at e1
    omega
  · exact Q.nicht_incL hN hF (Nat.le_trans hj (Nat.le_succ_of_le hj')) e

/-- **The quiet situation is impossible.** -/
theorem Ruhe.falsch (hN : N ≤ 2147483647) (hF : R.Fair) (Q : Ruhe R m s h W0) : False := by
  have ht := Q.tk m (Nat.le_refl m)
  have hh := Q.nie m (Nat.le_refl m)
  have hm := Nat.le_refl m
  cases hp : (R.z m).pc h with
  | frei =>
    rw [hp] at ht
    simp [Ort.ticket] at ht
  | ladeN =>
    rw [hp] at ht
    simp [Ort.ticket] at ht
  | casN l =>
    rw [hp] at ht
    simp [Ort.ticket] at ht
  | ladeS k =>
    rw [hp] at ht
    simp only [Ort.ticket, Option.some.injEq] at ht
    rw [ht] at hp
    exact Q.nicht_ladeS hF hm hp
  | incL k s0 =>
    rw [hp] at ht
    simp only [Ort.ticket, Option.some.injEq] at ht
    rw [ht] at hp
    exact Q.nicht_incL hN hF hm hp
  | incC k s0 lw =>
    rw [hp] at ht
    simp only [Ort.ticket, Option.some.injEq] at ht
    rw [ht] at hp
    exact Q.nicht_incC hN hF hm hp
  | futexW k s0 =>
    rw [hp] at ht
    simp only [Ort.ticket, Option.some.injEq] at ht
    rw [ht] at hp
    exact Q.nicht_futexW hN hF hm hp
  | blockiert k s0 =>
    rw [hp] at ht
    simp only [Ort.ticket, Option.some.injEq] at ht
    rw [ht] at hp
    exact Q.nicht_blockiert hN hF hm hp
  | decL k s0 =>
    rw [hp] at ht
    simp only [Ort.ticket, Option.some.injEq] at ht
    rw [ht] at hp
    exact Q.nicht_decL hN hF hm hp
  | decC k s0 lw =>
    rw [hp] at ht
    simp only [Ort.ticket, Option.some.injEq] at ht
    rw [ht] at hp
    exact Q.nicht_decC hN hF hm hp
  | drin k =>
    rw [hp] at hh
    simp [Ort.haelt] at hh
  | gibL k =>
    rw [hp] at hh
    simp [Ort.haelt] at hh
  | gibC k ls =>
    rw [hp] at hh
    simp [Ort.haelt] at hh
  | gibW =>
    rw [hp] at ht
    simp [Ort.ticket] at ht
  | weck =>
    rw [hp] at ht
    simp [Ort.ticket] at ht

end Gabbro.Stage0.Senke.Faeden
