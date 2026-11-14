/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Stau.lean
  Subject:   THE STUCK SITUATION the liveness proof refutes (`Stau`): from step `m` on the serving counter stays `s`,
             the thread `h` holds ticket `s` (so it heads the queue) and never holds the lock, and no blocked thread
             is scheduled (no spurious return). Then nobody enters (`Stau.ohneTritt`), from some step on nobody makes
             a FUTEX_WAKE (`Stau.ohneWeck`, potential `chi`), and from some later step on the waiter word stays
             (`Stau.wartFest`, potential `psi`): `Stau.ruhe` reaches the quiet situation `Ruhe` that
             Faeden/Kette.lean refutes.
-/
module
public import Stage0.Senke.Sperre.Faeden.Potential
public import Stage0.Senke.Sperre.Faeden.Fair
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

variable {N : Nat}

/-- **Stuck from step `m` on**: `serving` stays `s`, `h` holds ticket `s` and never the lock, no spurious
    return. -/
structure Stau (R : Lauf N) (m s : Nat) (h : Fin N) : Prop where
  inv : ∀ j, Inv N (R.z j)
  serv : ∀ j, m ≤ j → (R.z j).w.serv = s
  tk : ∀ j, m ≤ j → ((R.z j).pc h).ticket = some s
  nie : ∀ j, m ≤ j → ((R.z j).pc h).haelt = false
  ruhig : ∀ j, m ≤ j → ∀ v, R.akt j = some v → ((R.z j).pc v).schlaeft = false

/-- **Quiet from step `m` on**: stuck, no FUTEX_WAKE is made, the waiter word stays `W0`. -/
structure Ruhe (R : Lauf N) (m s : Nat) (h : Fin N) (W0 : Nat) : Prop extends Stau R m s h where
  weck : ∀ j, m ≤ j → ∀ v, R.akt j = some v → (R.z j).pc v ≠ .weck
  wait : ∀ j, m ≤ j → (R.z j).w.wait = W0

variable {R : Lauf N} {m s : Nat} {h : Fin N}

theorem Stau.spaeter (S : Stau R m s h) {m' : Nat} (hm : m ≤ m') : Stau R m' s h where
  inv := S.inv
  serv := fun j hj => S.serv j (Nat.le_trans hm hj)
  tk := fun j hj => S.tk j (Nat.le_trans hm hj)
  nie := fun j hj => S.nie j (Nat.le_trans hm hj)
  ruhig := fun j hj => S.ruhig j (Nat.le_trans hm hj)

/-- The thread with ticket `serving` heads the queue. -/
theorem Stau.kopf (S : Stau R m s h) {j : Nat} (hj : m ≤ j) : (R.z j).q.head? = some h := by
  obtain ⟨i, hi, hki, _⟩ := (S.inv j).platz (S.tk j hj)
  rw [S.serv j hj] at hki
  have hi0 : i = 0 := by omega
  rw [hi0] at hi
  rw [List.head?_eq_getElem?]
  exact hi

/-- **Nobody enters**: only the head could, and the head never holds the lock. -/
theorem Stau.ohneTritt (hN : N ≤ 2147483647) (S : Stau R m s h) {j : Nat} (hj : m ≤ j) {v : Fin N}
    (ha : R.akt j = some v) (h1 : ((R.z (j + 1)).pc v).haelt = true) : ((R.z j).pc v).haelt = true := by
  cases h0 : ((R.z j).pc v).haelt with
  | true => rfl
  | false =>
    exfalso
    obtain ⟨k, hk, e⟩ := (R.schritt j v ha).wird_haelt h0 h1
    have hv := (S.inv j).tritt hN hk e
    rw [S.kopf hj] at hv
    have hvh : h = v := Option.some.inj hv
    rw [← hvh, S.nie (j + 1) (Nat.le_succ_of_le hj)] at h1
    exact absurd h1 (by decide)

/-! ## 1. Finitely many WAKEs -/

theorem Stau.chi_lauf (S : Stau R m s h) {j : Nat} (hj : m ≤ j) (u : Fin N) :
    ((R.z (j + 1)).pc u).chi ≤ ((R.z j).pc u).chi ∧
      (R.akt j = some u → (R.z j).pc u = .weck → ((R.z (j + 1)).pc u).chi < ((R.z j).pc u).chi) := by
  cases hk : R.akt j with
  | none =>
    rw [R.stotter j hk]
    exact ⟨Nat.le_refl _, fun e => by cases e⟩
  | some t =>
    have hc := (R.schritt j t hk).chi (u := u) (S.inv j)
      (by rw [S.serv (j + 1) (Nat.le_succ_of_le hj), S.serv j hj])
    exact ⟨hc.1, fun e hw => hc.2 (Option.some.inj e) hw⟩

theorem Stau.ohneWeck (S : Stau R m s h) :
    ∃ m1, m ≤ m1 ∧ ∀ j, m1 ≤ j → ∀ v, R.akt j = some v → (R.z j).pc v ≠ .weck := by
  have hu : ∀ u : Fin N, ∃ mu, ∀ j, mu ≤ j → R.akt j = some u → (R.z j).pc u ≠ .weck := by
    intro u
    obtain ⟨mu, _, hr⟩ := endlich_pot (fun j => ((R.z j).pc u).chi)
      (fun j => R.akt j = some u ∧ (R.z j).pc u = .weck) _ m (Nat.le_refl _)
      (fun j hj => (S.chi_lauf hj u).1) (fun j hj hE => (S.chi_lauf hj u).2 hE.1 hE.2)
    exact ⟨mu, fun j hj ha hw => hr j hj ⟨ha, hw⟩⟩
  obtain ⟨m1, hm1⟩ := schliesslich (fun u j => R.akt j = some u → (R.z j).pc u ≠ .weck) hu
  exact ⟨max m m1, Nat.le_max_left m m1,
    fun j hj v ha => hm1 v j (Nat.le_trans (Nat.le_max_right m m1) hj) ha⟩

/-! ## 2. Finitely many changes of the waiter word -/

theorem Stau.psi_lauf (hN : N ≤ 2147483647) (S : Stau R m s h)
    (hW : ∀ j, m ≤ j → ∀ v, R.akt j = some v → (R.z j).pc v ≠ .weck) {j : Nat} (hj : m ≤ j) (u : Fin N) :
    ((R.z (j + 1)).pc u).psi s ≤ ((R.z j).pc u).psi s ∧
      (R.akt j = some u → (R.z (j + 1)).w.wait ≠ (R.z j).w.wait →
        ((R.z (j + 1)).pc u).psi s < ((R.z j).pc u).psi s) := by
  cases hk : R.akt j with
  | none =>
    rw [R.stotter j hk]
    exact ⟨Nat.le_refl _, fun e => by cases e⟩
  | some t =>
    have hc := (R.schritt j t hk).psi (u := u) s (S.serv j hj) (S.serv (j + 1) (Nat.le_succ_of_le hj))
      (S.ruhig j hj t hk) (hW j hj t hk) (S.ohneTritt hN hj hk)
    exact ⟨hc.1, fun e hw => hc.2 (Option.some.inj e) hw⟩

theorem Stau.wartFest (hN : N ≤ 2147483647) (S : Stau R m s h)
    (hW : ∀ j, m ≤ j → ∀ v, R.akt j = some v → (R.z j).pc v ≠ .weck) :
    ∃ m2, m ≤ m2 ∧ ∀ j, m2 ≤ j → (R.z (j + 1)).w.wait = (R.z j).w.wait := by
  have hu : ∀ u : Fin N, ∃ mu, ∀ j, mu ≤ j → R.akt j = some u → (R.z (j + 1)).w.wait = (R.z j).w.wait := by
    intro u
    obtain ⟨mu, _, hr⟩ := endlich_pot (fun j => ((R.z j).pc u).psi s)
      (fun j => R.akt j = some u ∧ (R.z (j + 1)).w.wait ≠ (R.z j).w.wait) _ m (Nat.le_refl _)
      (fun j hj => (S.psi_lauf hN hW hj u).1) (fun j hj hE => (S.psi_lauf hN hW hj u).2 hE.1 hE.2)
    exact ⟨mu, fun j hj ha => Classical.byContradiction (fun hne => hr j hj ⟨ha, hne⟩)⟩
  obtain ⟨m2, hm2⟩ := schliesslich
    (fun u j => R.akt j = some u → (R.z (j + 1)).w.wait = (R.z j).w.wait) hu
  refine ⟨max m m2, Nat.le_max_left m m2, fun j hj => ?_⟩
  cases hk : R.akt j with
  | none => rw [R.stotter j hk]
  | some v => exact hm2 v j (Nat.le_trans (Nat.le_max_right m m2) hj) hk

/-- **From the stuck situation to the quiet one.** -/
theorem Stau.ruhe (hN : N ≤ 2147483647) (S : Stau R m s h) :
    ∃ m2 W0, m ≤ m2 ∧ Ruhe R m2 s h W0 := by
  obtain ⟨m1, hm1, hW⟩ := S.ohneWeck
  obtain ⟨m2, hm2, hF⟩ := (S.spaeter hm1).wartFest hN hW
  have hwait : ∀ j, m2 ≤ j → (R.z j).w.wait = (R.z m2).w.wait :=
    bleibt (fun j => (R.z j).w.wait = (R.z m2).w.wait) m2 rfl
      (fun j hj hw => (hF j hj).trans hw)
  exact ⟨m2, (R.z m2).w.wait, Nat.le_trans hm1 hm2,
    { toStau := S.spaeter (Nat.le_trans hm1 hm2)
      weck := fun j hj => hW j (Nat.le_trans hm2 hj)
      wait := hwait }⟩

end Gabbro.Stage0.Senke.Faeden
