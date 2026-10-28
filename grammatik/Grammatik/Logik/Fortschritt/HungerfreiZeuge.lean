/-
  File:      Grammatik/Logik/Fortschritt/HungerfreiZeuge.lean
  Subject:   WITNESS OF STARVATION FREEDOM (2026-10-22): a fair run of the ticket lock with contention, on which every
             hypothesis of `hungerfrei` holds.

  The run is the one of the waiting-bound witness (LebendigkeitZeuge.lean, two threads on the fixture `mP`): thread 0
  stands at `locks` at steps 3-5, thread 1 at steps 5-15; at step 5 BOTH wait. The queue of the lock is read off that
  table: `[0]`, then `[0, 1]` at step 5, then `[1]` (`hzQ`). Thread 0, ahead, takes the lock at step 5; thread 1
  takes it at step 15. The run is a `FifoLauf` (`hz_lauf`) and fair (window 4, hence weakly), and `hungerfrei` gives
  for thread 1, waiting at step 5, that it takes the lock or someone holds it for ever (`hz_hungerfrei`).
-/
import Grammatik.Logik.Fortschritt.Hungerfrei
import Grammatik.Logik.Fortschritt.LebendigkeitZeuge

namespace Gabbro.Grammatik

/-- The queue of the lock, read off the table of who stands at `locks`. -/
def hzQ (j : Nat) (_ : Unit) : List Faden := (if lA0 j then [0] else []) ++ (if lA1 j then [1] else [])

theorem hzQ_spaet (j : Nat) (hj : 16 ≤ j) : hzQ j () = [] := by
  have h0 : lA0 j = false := by simp only [lA0]; exact decide_eq_false (by omega)
  have h1 : lA1 j = false := by simp only [lA1]; exact decide_eq_false (by omega)
  simp only [hzQ, h0, Bool.false_eq_true, ↓reduceIte, h1, List.append_nil]

/-- The queue keeps its order, up to step 16 (after it the queue is empty), by evaluation. -/
theorem hz_ordnung_klein : ∀ n, n ≤ 16 →
    (hzQ n ()).filter (fun u => decide (u ∈ hzQ (n + 1) ())) <+: hzQ (n + 1) () := by
  decide

/-- **The run is a run of the ticket lock, fair, with two threads waiting at once.** -/
theorem hz_lauf : ∃ R : FifoLauf mP mO 0,
    R.M 0 = RufStartG mP mSp mInit ∧ Fair mP mO 0 R.toPlanLauf ∧
    AnSperre (R.M 5) 0 () ∧ AnSperre (R.M 5) 1 () ∧ R.akt 5 = some 0 ∧ R.akt 15 = some 1 ∧
    (∀ n, KeinLogikHaltG mO 0 (R.M n)) := by
  obtain ⟨R, h0, hakt, hLZ, -, -, -, hL, -, -, -, hAn⟩ := lZeuge
  refine ⟨{ R with
    q := hzQ
    glied := fun n L u => by
      cases L
      rw [hAn]
      cases ha : lA0 n <;> cases hb : lA1 n <;> simp only [hzQ, ha, Bool.false_eq_true, ↓reduceIte, hb, List.append_nil, List.not_mem_nil, and_false, or_self, List.nil_append, List.mem_cons, or_false, and_true, false_or, List.cons_append]
    eindeutig := fun n L => by
      cases ha : lA0 n <;> cases hb : lA1 n <;> simp only [hzQ, ha, Bool.false_eq_true, ↓reduceIte, hb, List.append_nil, List.nodup_nil, List.nil_append, List.nodup_cons, List.not_mem_nil, not_false_eq_true, and_self, List.cons_append, List.mem_cons, Nat.zero_ne_one, or_self]
    kopf := fun n u L hk hA => by
      cases L
      rw [hakt] at hk
      rcases (hAn n u).mp hA with ⟨rfl, h⟩ | ⟨rfl, h⟩
      · simp only [hzQ, h, ↓reduceIte, List.cons_append, List.nil_append, List.head?_cons]
      · have h0' : lA0 n = false := by
          rcases lAkt_some hk with ⟨e, _⟩ | ⟨_, hn⟩
          · cases e
          · simp only [lA1, decide_eq_true_eq] at h
            simp only [lA0]; exact decide_eq_false (by omega)
        simp only [hzQ, h0', Bool.false_eq_true, ↓reduceIte, h, List.nil_append, List.head?_cons]
    ordnung := fun n L => by
      cases L
      by_cases hn : n ≤ 16
      · exact hz_ordnung_klein n hn
      · rw [hzQ_spaet n (by omega), hzQ_spaet (n + 1) (by omega)]
        exact List.prefix_refl _ }, h0, fair_of_fairF hLZ.2, ?_, ?_, ?_, ?_, hL⟩
  · exact (hAn 5 0).mpr (Or.inl ⟨rfl, by decide⟩)
  · exact (hAn 5 1).mpr (Or.inr ⟨rfl, by decide⟩)
  · show R.akt 5 = some 0; rw [hakt]; decide
  · show R.akt 15 = some 1; rw [hakt]; decide

/-- **`hungerfrei` on the witness**, every hypothesis discharged from the fixture's facts. -/
theorem hz_hungerfrei : ∃ R : FifoLauf mP mO 0, R.M 0 = RufStartG mP mSp mInit ∧ AnSperre (R.M 5) 1 () ∧
    ((∃ j, 5 ≤ j ∧ R.akt j = some 1 ∧ AnSperre (R.M j) 1 ()) ∨
      ∃ u m, ∀ j, m ≤ j → () ∈ offen ((R.M j).faeden u).spur) := by
  obtain ⟨R, h0, hF, -, hA5, -, -, hL⟩ := hz_lauf
  have hND := startSpur_nodup_leer mInit mInit_leer
  have hr : ∀ n, RufErreichbarG mP mO 0 (RufStartG mP mSp mInit) (R.M n) :=
    R.toPlanLauf.erreichbar (by rw [h0]; exact .start)
  have hB : ∀ n t, BereichG (R.M n) t := fun n =>
    bereichG_mehrfaden mP mO 0 (axWahr mD) mSI mFs mSp mInit mK mO_gut mO_lokal
      (axVertragO_wahr mO) axEnsLokal_wahr mSI_ok mFs_voll mP_fragmentG mAbg mWurzel mP_fuss
      (mP_koerper_alle 0) mP_start mSI_start mInit_exklusiv (R.M n) (hr n)
  refine ⟨R, h0, hA5, hungerfrei R mO_gut
    (fun n t => ⟨_, rangInvG_erreichbar mO_gut mP_stufen mSp mInit hND (hr n) t⟩)
    (fun n => exklusivG mO_gut mSp mInit (startExklusiv_ohne_haelt mInit mInit_leer) (hr n))
    (fun n => fortschrittG_aus mO_gut mP_stufen mSp mInit hND (hr n) (hL n) (hB n)
      (fun g x hx => absurd hx (by cases g <;> exact List.not_mem_nil)))
    hF hA5⟩

end Gabbro.Grammatik
