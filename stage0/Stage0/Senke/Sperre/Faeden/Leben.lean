/-
  File:      stage0/Stage0/Senke/Sperre/Faeden/Leben.lean
  Subject:   THE CROSS-THREAD LOCK THEOREM, liveness half: `GabbroZielLeben`'s conclusion, in its shape, for the
             EMITTED lock (the instance of the model statement itself is Faeden/Transfer.lean).
             On every run of the emitted lock (Faeden/Maschine.lean) from a state meeting the invariant (the start
             does, `Inv.start`), with at most 2147483647 threads, on which
             * the scheduler is weakly fair over the threads not blocked in FUTEX_WAIT (`Lauf.Fair`; a blocked
               thread is never required to step), and
             * FUTEX_WAIT returns spuriously only finitely often (`Lauf.ScheinbarEndlich`, the named futex
               fairness premise),
             a thread waiting with its ticket takes the lock, or some thread holds the lock from some step on for
             ever (`Lauf.leben`; stated over the abstract lock: `Lauf.leben_warte`). The proof: while it waits,
             `serving` stays at most its ticket; from every step on `serving` grows (`Lauf.waechst`), because
             otherwise the head of the queue either holds the lock for ever or is stuck (`Stau`), and the stuck
             situation reaches the quiet one (`Stau.ruhe`), which is impossible (`Ruhe.falsch`).
             NOT claimed: that a thread before its draw ever draws -- the draw is a `cas` loop on `next`, lock-free
             but not wait-free, so other threads that keep drawing can make it fail for ever under a fair scheduler.
             The model's `locks L` step corresponds to the successful draw.
-/
module
public import Stage0.Senke.Sperre.Faeden.Kette
public import Stage0.Senke.Sperre.Faeden.Fifo
@[expose] public section

namespace Gabbro.Stage0.Senke.Faeden

variable {N : Nat}

/-- Holding the lock is kept over a scheduler step that leaves `serving`. -/
theorem Lauf.haelt_weiter (R : Lauf N) (hI : ∀ j, Inv N (R.z j)) {u : Fin N} {j : Nat}
    (hh : ((R.z j).pc u).haelt = true) (hs : (R.z (j + 1)).w.serv = (R.z j).w.serv) :
    ((R.z (j + 1)).pc u).haelt = true :=
  R.fall (fun σ σ' => Inv N σ → (σ.pc u).haelt = true → σ'.w.serv = σ.w.serv → (σ'.pc u).haelt = true)
    (fun _ _ hh _ => hh) (fun _ _ _ hs hI hh he => hs.haelt_bleibt hI hh he) j (hI j) hh hs

/-- A ticket is kept over a scheduler step that leaves `serving`. -/
theorem Lauf.ticket_weiter (R : Lauf N) (hI : ∀ j, Inv N (R.z j)) {u : Fin N} {j k : Nat}
    (hk : ((R.z j).pc u).ticket = some k) (hs : (R.z (j + 1)).w.serv = (R.z j).w.serv) :
    ((R.z (j + 1)).pc u).ticket = some k :=
  R.fall (fun σ σ' => Inv N σ → (σ.pc u).ticket = some k → σ'.w.serv = σ.w.serv → (σ'.pc u).ticket = some k)
    (fun _ _ hk _ => hk) (fun _ _ _ hs hI hk he => hs.ticket_bleibt hI hk he) j (hI j) hk hs

/-- **`serving` grows**: while some thread holds a ticket, no thread holds the lock for ever and FUTEX_WAIT no
    longer returns spuriously, `serving` grows from every step on. -/
theorem Lauf.waechst (hN : N ≤ 2147483647) (R : Lauf N) (hI : ∀ j, Inv N (R.z j)) (hF : R.Fair) {ms : Nat}
    (hS : ∀ j, ms ≤ j → ∀ v, R.akt j = some v → ((R.z j).pc v).schlaeft = false)
    (hH : ¬ ∃ u m, ∀ j, m ≤ j → ((R.z j).pc u).haelt = true) {m : Nat} {t : Fin N} {k : Nat}
    (ht : ((R.z m).pc t).ticket = some k) : ∃ j, m ≤ j ∧ (R.z m).w.serv < (R.z j).w.serv := by
  by_contra hc
  have hkonst : ∀ j, m ≤ j → (R.z j).w.serv = (R.z m).w.serv := fun j hj => by
    have h1 := R.serv_mono hj
    have h2 : ¬ (R.z m).w.serv < (R.z j).w.serv := fun hl => hc ⟨j, hj, hl⟩
    omega
  have hm : t ∈ (R.z m).q := ((hI m).mem t).2 (by simp [ht])
  obtain ⟨h, r, hq⟩ : ∃ h r, (R.z m).q = h :: r := by
    cases hq : (R.z m).q with
    | nil =>
      rw [hq] at hm
      exact absurd hm List.not_mem_nil
    | cons h r => exact ⟨h, r, rfl⟩
  have htk : ((R.z m).pc h).ticket = some (R.z m).w.serv := by
    have hx := (hI m).tk 0 h (by simp [hq])
    rw [Nat.add_zero] at hx
    exact hx
  have htk' : ∀ j, m ≤ j → ((R.z j).pc h).ticket = some (R.z m).w.serv :=
    bleibt (fun j => ((R.z j).pc h).ticket = some (R.z m).w.serv) m htk (fun j hj hx =>
      R.ticket_weiter hI hx ((hkonst (j + 1) (Nat.le_succ_of_le hj)).trans (hkonst j hj).symm))
  by_cases hA : ∃ j, m ≤ j ∧ ((R.z j).pc h).haelt = true
  · obtain ⟨j, hj, hhj⟩ := hA
    exact hH ⟨h, j, bleibt (fun j => ((R.z j).pc h).haelt = true) j hhj (fun j' hj' hx =>
      R.haelt_weiter hI hx ((hkonst (j' + 1) (by omega)).trans (hkonst j' (by omega)).symm))⟩
  · have hnie : ∀ j, m ≤ j → ((R.z j).pc h).haelt = false := fun j hj => by
      cases hx : ((R.z j).pc h).haelt with
      | false => rfl
      | true => exact (hA ⟨j, hj, hx⟩).elim
    have S : Stau R (max m ms) (R.z m).w.serv h :=
      { inv := hI
        serv := fun j hj => hkonst j (Nat.le_trans (Nat.le_max_left m ms) hj)
        tk := fun j hj => htk' j (Nat.le_trans (Nat.le_max_left m ms) hj)
        nie := fun j hj => hnie j (Nat.le_trans (Nat.le_max_left m ms) hj)
        ruhig := fun j hj => hS j (Nat.le_trans (Nat.le_max_right m ms) hj) }
    obtain ⟨m2, W0, _, Q⟩ := S.ruhe hN
    exact Q.falsch hN hF

/-- **LIVENESS OF THE EMITTED LOCK**: on every weakly fair run with finitely many spurious returns of
    FUTEX_WAIT, a thread waiting with ticket `k` enters the lock with it, or some thread holds the lock from some
    step on for ever. -/
theorem Lauf.leben (hN : N ≤ 2147483647) (R : Lauf N) (h0 : Inv N (R.z 0)) (hF : R.Fair)
    (hS : R.ScheinbarEndlich) (n : Nat) (t : Fin N) (k : Nat) (hw : WartetMit k ((R.z n).pc t)) :
    (∃ j, n ≤ j ∧ (R.z j).pc t = .drin k) ∨ ∃ u m, ∀ j, m ≤ j → ((R.z j).pc u).haelt = true := by
  have hI := Inv.lauf hN R h0
  obtain ⟨ms, hms⟩ := hS
  by_cases hH : ∃ u m, ∀ j, m ≤ j → ((R.z j).pc u).haelt = true
  · exact Or.inr hH
  by_cases hD : ∃ j, n ≤ j ∧ (R.z j).pc t = .drin k
  · exact Or.inl hD
  exfalso
  have hW : ∀ j, n ≤ j → WartetMit k ((R.z j).pc t) :=
    bleibt (fun j => WartetMit k ((R.z j).pc t)) n hw (fun j hj hx => by
      rcases R.fall (fun σ σ' => WartetMit k (σ.pc t) → WartetMit k (σ'.pc t) ∨ σ'.pc t = .drin k)
        (fun _ hx => Or.inl hx) (fun _ _ _ hs hx => hs.wartetMit hx) j hx with e | e
      · exact e
      · exact (hD ⟨j + 1, Nat.le_succ_of_le hj, e⟩).elim)
  have hle : ∀ j, n ≤ j → (R.z j).w.serv ≤ k := fun j hj => by
    obtain ⟨i, _, hki, _⟩ := (hI j).platz (hW j hj).1
    omega
  have hit : ∀ d, ∃ j, n ≤ j ∧ (R.z n).w.serv + d ≤ (R.z j).w.serv := by
    intro d
    induction d with
    | zero => exact ⟨n, Nat.le_refl n, Nat.le_refl _⟩
    | succ d ih =>
      obtain ⟨j, hj, hd⟩ := ih
      obtain ⟨j', hj', hlt⟩ := R.waechst hN hI hF hms hH (hW j hj).1
      exact ⟨j', Nat.le_trans hj hj', by omega⟩
  obtain ⟨j, hj, hd⟩ := hit (k + 1)
  have hx := hle j hj
  omega

/-- **Liveness over the abstract lock** (the shape of `GabbroZielLeben`): a thread waiting at the emitted lock
    becomes its holder, or some thread holds it from some step on for ever. -/
theorem Lauf.leben_warte (hN : N ≤ 2147483647) (R : Lauf N) (h0 : Inv N (R.z 0)) (hF : R.Fair)
    (hS : R.ScheinbarEndlich) (n : Nat) (t : Fin N) (ht : t ∈ R.warte n) :
    (∃ j, n ≤ j ∧ R.halter j = some t) ∨ ∃ u m, ∀ j, m ≤ j → R.halter j = some u := by
  obtain ⟨hs, hh⟩ := (R.glied hN h0 n t).1 ht
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hs
  rcases R.leben hN h0 hF hS n t k ⟨hk, hh⟩ with ⟨j, hj, e⟩ | ⟨u, m, hu⟩
  · refine Or.inl ⟨j, hj, (R.halter_iff hN h0 j t).2 ?_⟩
    simp [e, Ort.haelt]
  · exact Or.inr ⟨u, m, fun j hj => (R.halter_iff hN h0 j u).2 (hu j hj)⟩

end Gabbro.Stage0.Senke.Faeden
