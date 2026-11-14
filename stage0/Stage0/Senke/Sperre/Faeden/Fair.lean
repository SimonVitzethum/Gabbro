/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Fair.lean
  Subject:   Tools over the runs of the emitted lock (`Lauf`, Faeden/Maschine.lean): a property carried from step to
             step, one scheduler step as a step or a stutter, the serving counter along a run, the FAIR STEP (a
             thread that is not blocked and stays where it is takes a step there, by weak fairness), a potential that
             never grows and drops at certain steps (finitely many of them), and the eventual bound over all threads.
             `Lauf.ScheinbarEndlich` is the named futex fairness premise of the liveness statement: FUTEX_WAIT returns
             spuriously only finitely often.
-/
module
public import Stage0.Senke.Sperre.Faeden.Rahmen
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

variable {N : Nat}

/-- **Futex fairness** (a named premise): from some scheduler step on no thread blocked in FUTEX_WAIT is
    scheduled, so FUTEX_WAIT returns spuriously (signals, spurious wake-ups) only finitely often. Blocked threads
    are never required to step (`Lauf.Fair`); this only bounds how often they may. -/
def Lauf.ScheinbarEndlich (R : Lauf N) : Prop :=
  ∃ m, ∀ j, m ≤ j → ∀ v, R.akt j = some v → ((R.z j).pc v).schlaeft = false

/-- A property of the scheduler steps from `n` on, carried from each step to the next. -/
theorem bleibt (P : Nat → Prop) (n : Nat) (h0 : P n) (hs : ∀ j, n ≤ j → P j → P (j + 1)) :
    ∀ j, n ≤ j → P j := by
  intro j hj
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  clear hj
  induction d with
  | zero => exact h0
  | succ d ih => exact hs (n + d) (Nat.le_add_right n d) ih

/-- One scheduler step is a step of the emitted lock or a stutter. -/
theorem Lauf.fall (R : Lauf N) (P : Zustand N → Zustand N → Prop) (hrefl : ∀ σ, P σ σ)
    (hs : ∀ σ σ' t, Schritt σ t σ' → P σ σ') (j : Nat) : P (R.z j) (R.z (j + 1)) := by
  cases hk : R.akt j with
  | none =>
    rw [R.stotter j hk]
    exact hrefl _
  | some t => exact hs _ _ t (R.schritt j t hk)

/-- The serving counter never decreases along a run. -/
theorem Lauf.serv_mono (R : Lauf N) {m j : Nat} (h : m ≤ j) : (R.z m).w.serv ≤ (R.z j).w.serv :=
  bleibt (fun j => (R.z m).w.serv ≤ (R.z j).w.serv) m (Nat.le_refl _)
    (fun j _ hj => Nat.le_trans hj
      (R.fall (fun σ σ' => σ.w.serv ≤ σ'.w.serv) (fun _ => Nat.le_refl _) (fun _ _ _ hs => hs.serv_le) j))
    j h

/-- A thread that is not scheduled stays, or is woken by a FUTEX_WAKE. -/
theorem Lauf.fremd (R : Lauf N) (j : Nat) {t : Fin N} (ha : R.akt j ≠ some t) :
    (R.z (j + 1)).pc t = (R.z j).pc t ∨ (R.z (j + 1)).pc t = ((R.z j).pc t).geweckt := by
  cases hk : R.akt j with
  | none => exact Or.inl (by rw [R.stotter j hk])
  | some v =>
    have hv : t ≠ v := fun e => ha (by rw [hk, e])
    exact (R.schritt j v hk).andere hv

/-- **The fair step**: a property that makes `t` ready and that every step of another thread keeps holds at a
    step at which `t` is scheduled. -/
theorem Lauf.trifft (R : Lauf N) (hF : R.Fair) (t : Fin N) (P : Zustand N → Prop) (n : Nat)
    (hP : P (R.z n)) (hB : ∀ σ, P σ → Bereit σ t)
    (hK : ∀ j, n ≤ j → R.akt j ≠ some t → P (R.z j) → P (R.z (j + 1))) :
    ∃ j, n ≤ j ∧ R.akt j = some t ∧ P (R.z j) := by
  by_contra hc
  have hall : ∀ j, n ≤ j → P (R.z j) :=
    bleibt (fun j => P (R.z j)) n hP (fun j hj hPj => hK j hj (fun ha => hc ⟨j, hj, ha, hPj⟩) hPj)
  obtain ⟨j, hj, ha⟩ := hF t n (fun j hj => hB _ (hall j hj))
  exact hc ⟨j, hj, ha, hall j hj⟩

/-- **A thread at a place where it is not blocked takes its step there.** -/
theorem Lauf.kommt (R : Lauf N) (hF : R.Fair) {t : Fin N} {o : Ort} (ho : o.schlaeft = false) {n : Nat}
    (hp : (R.z n).pc t = o) : ∃ j, n ≤ j ∧ R.akt j = some t ∧ (R.z j).pc t = o :=
  R.trifft hF t (fun σ => σ.pc t = o) n hp
    (fun σ hσ => by
      show (σ.pc t).schlaeft = false
      rw [hσ]
      exact ho)
    (fun j _ ha hpj => by
      rcases R.fremd j ha with e | e
      · rw [e]
        exact hpj
      · rw [e, hpj]
        exact geweckt_fest ho)

/-! ## Finitely many steps of a kind -/

theorem antiton (f : Nat → Nat) (m : Nat) (h : ∀ j, m ≤ j → f (j + 1) ≤ f j) : ∀ j, m ≤ j → f j ≤ f m :=
  bleibt (fun j => f j ≤ f m) m (Nat.le_refl _) (fun j hj hf => Nat.le_trans (h j hj) hf)

/-- **A potential that never grows from `m` on and drops at every step of kind `E`**: from some step on no step
    is of kind `E`. -/
theorem endlich_pot (f : Nat → Nat) (E : Nat → Prop) : ∀ (v m : Nat), f m ≤ v →
    (∀ j, m ≤ j → f (j + 1) ≤ f j) → (∀ j, m ≤ j → E j → f (j + 1) < f j) →
    ∃ m', m ≤ m' ∧ ∀ j, m' ≤ j → ¬ E j
  | 0, m, hv, hmono, hE =>
    ⟨m, Nat.le_refl m, fun j hj hEj => by
      have h1 := hE j hj hEj
      have h2 := antiton f m hmono j hj
      omega⟩
  | v + 1, m, hv, hmono, hE => by
    by_cases hx : ∃ j, m ≤ j ∧ E j
    · obtain ⟨j, hj, hEj⟩ := hx
      have h1 := hE j hj hEj
      have h2 := antiton f m hmono j hj
      obtain ⟨m', hm', hr⟩ := endlich_pot f E v (j + 1) (by omega)
        (fun i hi => hmono i (by omega)) (fun i hi => hE i (by omega))
      exact ⟨m', by omega, hr⟩
    · exact ⟨m, Nat.le_refl m, fun j hj hEj => hx ⟨j, hj, hEj⟩⟩

/-- An eventual property of each element of a list holds eventually for all of them. -/
theorem schliesslich_liste {α : Type} (P : α → Nat → Prop) (h : ∀ u, ∃ m, ∀ j, m ≤ j → P u j) :
    ∀ l : List α, ∃ m, ∀ u ∈ l, ∀ j, m ≤ j → P u j
  | [] => ⟨0, fun u hu => absurd hu List.not_mem_nil⟩
  | x :: l => by
    obtain ⟨m1, h1⟩ := h x
    obtain ⟨m2, h2⟩ := schliesslich_liste P h l
    refine ⟨max m1 m2, fun u hu j hj => ?_⟩
    rcases List.mem_cons.1 hu with e | e
    · rw [e]
      exact h1 j (Nat.le_trans (Nat.le_max_left m1 m2) hj)
    · exact h2 u e j (Nat.le_trans (Nat.le_max_right m1 m2) hj)

/-- An eventual property of every thread holds eventually for all threads at once. -/
theorem schliesslich (P : Fin N → Nat → Prop) (h : ∀ u, ∃ m, ∀ j, m ≤ j → P u j) :
    ∃ m, ∀ u j, m ≤ j → P u j := by
  obtain ⟨m, hm⟩ := schliesslich_liste P h (List.finRange N)
  exact ⟨m, fun u j hj => hm u (List.mem_finRange u) j hj⟩

end Gabbro.Stage0.Senke.Faeden
