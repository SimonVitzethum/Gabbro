/-
  File:      Grammatik/Logik/Fortschritt/Hungerfrei.lean
  Subject:   THE TICKET LOCK IN THE MODEL AND STARVATION FREEDOM (2026-10-22, review of gabbro_ziel, point 1).

  Machine G takes a lock at a `locks L` head whenever no other thread holds it (`dannLocks`, `RufFreiG`): which of
  several waiting threads gets it is the scheduler's choice, so a waiting thread may be overtaken forever. The
  language's lock is a TICKET lock (Code/Conc/Lock.lean: `fetch_add` on `next`, spin on `serving`): first come,
  first served. Here that order is part of the run.

  * `FifoLauf` (PlanLauf.lean) -- a scheduled run of machine G (`PlanLauf`, Lebendigkeit.lean) with ONE QUEUE PER LOCK: the queue
    holds exactly the threads standing at `locks L` (`glied`), each once (`eindeutig`); a thread that takes `L` is
    the head of its queue (`kopf`); and the threads that stay keep their order ahead of every newcomer
    (`ordnung`: the survivors are a prefix of the next queue). The runs of the ticket lock are exactly these.
  * `fifoSperre_aus` -- the runtime assumption `FifoSperre` of Lebendigkeit.lean is a THEOREM about such a run:
    nobody overtakes a waiting thread. So the waiting bound `wartezeit_kern` holds on every `FifoLauf` with one
    assumption fewer.
  * `Fair` -- weak fairness: a thread that can step at every scheduler step from some point on takes a step.
  * `hungerfrei` -- **STARVATION FREEDOM**: on a fair `FifoLauf` on which every machine meets the progress leg,
    lock exclusivity and the rank invariant (all three given by the goal theorem at every reached machine), a
    thread standing at `locks L` takes `L`, or some thread holds `L` from some step on forever. The second case is
    the program's own: a critical section that never ends (or ends in a named stop). Nothing else can make a
    thread wait for ever: no overtaking (FIFO), no lost wake-up (the head of the queue at a free lock can always
    step, by progress), no unfair scheduler (fairness).
-/
import Grammatik.Logik.Fortschritt.Lebendigkeit
import Grammatik.Logik.Fortschritt.PlanLauf
import Grammatik.Zielsatz.Eigenschaften.Masken

namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Lists: the threads ahead of `t` -/

section Listen

/-- The threads ahead of `t` in a queue. -/
def vorne (l : List Faden) (t : Faden) : List Faden := l.takeWhile (fun u => decide (u ≠ t))

theorem vorne_filter (p : Faden → Bool) (t : Faden) (hp : p t = true) :
    ∀ l : List Faden, vorne (l.filter p) t = (vorne l t).filter p
  | [] => rfl
  | u :: l => by
      have ih := vorne_filter p t hp l
      unfold vorne at ih ⊢
      by_cases hu : u = t
      · subst hu; simp only [ne_eq, decide_not, hp, List.filter_cons_of_pos, decide_true, Bool.not_true, Bool.false_eq_true,
  not_false_eq_true, List.takeWhile_cons_of_neg, List.filter_nil]
      · have hd : decide (u ≠ t) = true := by simp only [ne_eq, hu, not_false_eq_true, decide_true]
        cases hpu : p u
        · rw [List.filter_cons_of_neg (by simp only [hpu, Bool.false_eq_true, not_false_eq_true]), List.takeWhile_cons_of_pos (p := fun x => decide (x ≠ t)) (a := u) hd,
            List.filter_cons_of_neg (by simp only [hpu, Bool.false_eq_true, not_false_eq_true])]
          exact ih
        · rw [List.filter_cons_of_pos hpu, List.takeWhile_cons_of_pos (p := fun x => decide (x ≠ t)) (a := u) hd, List.takeWhile_cons_of_pos (p := fun x => decide (x ≠ t)) (a := u) hd,
            List.filter_cons_of_pos hpu, ih]

theorem vorne_praefix {F G : List Faden} {t : Faden} (ht : t ∈ F) (h : F <+: G) : vorne G t = vorne F t := by
  obtain ⟨r, rfl⟩ := h
  induction F with
  | nil => exact absurd ht List.not_mem_nil
  | cons u F ih =>
      by_cases hu : u = t
      · subst hu; simp only [vorne, ne_eq, decide_not, List.cons_append, decide_true, Bool.not_true, Bool.false_eq_true,
  not_false_eq_true, List.takeWhile_cons_of_neg]
      · have ht' : t ∈ F := by
          rcases List.mem_cons.mp ht with h | h
          · exact absurd h.symm hu
          · exact h
        simp only [vorne, List.cons_append, List.takeWhile_cons, ne_eq, hu, not_false_eq_true, decide_true,
          ↓reduceIte, List.cons.injEq, true_and] at ih ⊢
        exact ih ht'

theorem mem_vorne {t u : Faden} : ∀ {l : List Faden}, u ∈ vorne l t → u ∈ l ∧ u ≠ t
  | [], h => by simp only [vorne, ne_eq, decide_not, List.takeWhile_nil, List.not_mem_nil] at h
  | x :: l, h => by
      unfold vorne at h
      by_cases hx : x = t
      · subst hx; simp only [ne_eq, decide_not, decide_true, Bool.not_true, Bool.false_eq_true, not_false_eq_true,
  List.takeWhile_cons_of_neg, List.not_mem_nil] at h
      · simp only [List.takeWhile_cons, ne_eq, hx, not_false_eq_true, decide_true, ↓reduceIte,
          List.mem_cons] at h
        rcases h with rfl | h
        · exact ⟨List.mem_cons_self, hx⟩
        · obtain ⟨h1, h2⟩ := mem_vorne (l := l) h
          exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- The head of a queue that is not `t` is ahead of `t`. -/
theorem kopf_vorne {l : List Faden} {h t : Faden} (hk : l.head? = some h) (hne : h ≠ t) : h ∈ vorne l t := by
  cases l with
  | nil => cases hk
  | cons u l =>
      simp only [List.head?_cons, Option.some.injEq] at hk
      subst hk
      simp only [vorne, ne_eq, decide_not, hne, decide_false, Bool.not_false, List.takeWhile_cons_of_pos,
  List.mem_cons, true_or]

/-- `t` is the head exactly when nobody is ahead. -/
theorem vorne_leer {l : List Faden} {t : Faden} (ht : t ∈ l) (h : vorne l t = []) : l.head? = some t := by
  cases l with
  | nil => exact absurd ht List.not_mem_nil
  | cons u l =>
      by_cases hu : u = t
      · subst hu; rfl
      · simp only [vorne, ne_eq, decide_not, hu, decide_false, Bool.not_false, List.takeWhile_cons_of_pos,
  reduceCtorEq] at h

end Listen

section Fifo

variable {P : Programm D} {O : Orakel D} {passes : Nat} (R : FifoLauf P O passes)

open Classical in
/-- **Nobody ahead of `t` joins**: the threads ahead of `t` one step later were ahead of it before. -/
theorem FifoLauf.vorne_schritt {n : Nat} {L : D.Lock} {t : Faden} (h0 : t ∈ R.q n L) (h1 : t ∈ R.q (n + 1) L) :
    vorne (R.q (n + 1) L) t = (vorne (R.q n L) t).filter (fun u => decide (u ∈ R.q (n + 1) L)) := by
  have hF : t ∈ (R.q n L).filter (fun u => decide (u ∈ R.q (n + 1) L)) := List.mem_filter.mpr ⟨h0, by simpa using h1⟩
  rw [vorne_praefix hF (R.ordnung n L), vorne_filter _ t (by simpa using h1)]

open Classical in
theorem FifoLauf.vorne_le {n : Nat} {L : D.Lock} {t : Faden} (h0 : t ∈ R.q n L) (h1 : t ∈ R.q (n + 1) L) :
    (vorne (R.q (n + 1) L) t).length ≤ (vorne (R.q n L) t).length := by
  rw [R.vorne_schritt h0 h1]
  exact List.length_filter_le _ _

open Classical in
/-- **Someone ahead of `t` left: `t` moves up.** -/
theorem FifoLauf.vorne_lt {n : Nat} {L : D.Lock} {t h : Faden} (h0 : t ∈ R.q n L) (h1 : t ∈ R.q (n + 1) L)
    (hv : h ∈ vorne (R.q n L) t) (hh : h ∉ R.q (n + 1) L) :
    (vorne (R.q (n + 1) L) t).length < (vorne (R.q n L) t).length := by
  rw [R.vorne_schritt h0 h1]
  exact List.length_filter_lt_length_iff_exists.mpr ⟨h, hv, by simpa using hh⟩

/-- A thread that does not act keeps its state. -/
theorem FifoLauf.an_gleich {n : Nat} {u : Faden} {L : D.Lock} (ha : R.akt n ≠ some u)
    (hA : AnSperre (R.M n) u L) : AnSperre (R.M (n + 1)) u L :=
  anSperre_gleich (R.toPlanLauf.fremd n u ha) hA

/-- **A thread leaves the queue of `L` only by taking `L`.** -/
theorem FifoLauf.verlaesst {n : Nat} {L : D.Lock} {t : Faden} (h0 : t ∈ R.q n L) (h1 : t ∉ R.q (n + 1) L) :
    R.akt n = some t ∧ AnSperre (R.M n) t L := by
  have hA := (R.glied n L t).mp h0
  refine ⟨?_, hA⟩
  apply Classical.byContradiction
  intro ha
  exact h1 ((R.glied (n + 1) L t).mpr (R.an_gleich ha hA))

/-- **`t` stays in the queue with nobody new ahead, or it took the lock.** -/
theorem FifoLauf.bleibt {L : D.Lock} {t : Faden} {a : Nat} (ha : t ∈ R.q a L) :
    ∀ d, (t ∈ R.q (a + d) L ∧ (vorne (R.q (a + d) L) t).length ≤ (vorne (R.q a L) t).length) ∨
      ∃ j, a ≤ j ∧ j < a + d ∧ R.akt j = some t ∧ AnSperre (R.M j) t L
  | 0 => Or.inl ⟨ha, Nat.le_refl _⟩
  | d + 1 => by
      rcases FifoLauf.bleibt ha d with ⟨hd, hle⟩ | ⟨j, h1, h2, h3⟩
      · by_cases hn : t ∈ R.q (a + d + 1) L
        · exact Or.inl ⟨hn, Nat.le_trans (R.vorne_le hd hn) hle⟩
        · obtain ⟨e1, e2⟩ := R.verlaesst hd hn
          exact Or.inr ⟨a + d, by omega, by omega, e1, e2⟩
      · exact Or.inr ⟨j, h1, by omega, h3⟩

/-- **The ticket lock overtakes nobody**: the runtime assumption `FifoSperre` of Lebendigkeit.lean holds on every
    run of the ticket lock. The thread that takes `L` heads the queue, so it was ahead of every other waiting thread,
    and a thread ahead was ahead at every earlier step (nobody joins in front). -/
theorem fifoSperre_aus : FifoSperre R.toPlanLauf := by
  intro t u L a n htu hT hakt hAu j hja hjn
  have hv : ∀ d, d ≤ n - a → u ∈ vorne (R.q (n - d) L) t := by
    intro d
    induction d with
    | zero =>
        intro _
        simpa using kopf_vorne (R.kopf n u L hakt hAu) (Ne.symm htu)
    | succ d ih =>
        intro hd
        have h1 := ih (by omega)
        have hm0 : t ∈ R.q (n - (d + 1)) L := (R.glied _ L t).mpr (hT _ (by omega) (by omega))
        have e : n - d = n - (d + 1) + 1 := by omega
        have hm1 : t ∈ R.q (n - (d + 1) + 1) L := (R.glied _ L t).mpr (hT _ (by omega) (by omega))
        rw [e, R.vorne_schritt hm0 hm1] at h1
        exact (List.mem_filter.mp h1).1
  have h := hv (n - j) (by omega)
  rw [show n - (n - j) = j by omega] at h
  exact (R.glied j L u).mp (mem_vorne h).1

/-- **Bounded fairness is weak fairness**: a window `F` in which a continuously ready thread acts. -/
theorem fair_of_fairF {R : PlanLauf P O passes} {F : Nat} (h : FairF R F) : Fair P O passes R := fun t n hb => by
  obtain ⟨j, h1, -, h3⟩ := h t n (fun j hj _ => hb j hj)
  exact ⟨j, h1, h3⟩

end Fifo

/-! ## 3. Starvation freedom -/

section Hunger

variable {P : Programm D} {O : Orakel D} {passes : Nat} (R : FifoLauf P O passes)
  (hO : GutO O)
  (hRang : ∀ n t, ∃ w, RangInvG w ((R.M n).faeden t))
  (hEx : ∀ n (f g : Faden), f ≠ g → ∀ L : D.Lock,
    L ∈ offen ((R.M n).faeden f).spur → L ∉ offen ((R.M n).faeden g).spur)
  (hFort : ∀ n, Zielsatz.FortschrittG P O passes (R.M n))
  (hFair : Fair P O passes R.toPlanLauf)

/-- A head block at a named stop is no `locks` statement. -/
theorem kopfHalt_keineSperre {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {σ : World D}
    {ρ : Env D Γ} {k : Zielsatz.HaltArt} {b : Block D V l Γ Λ Λ'} (h : Zielsatz.KopfHalt O passes σ ρ k b) :
    b.sperreVon = none := by
  cases b with
  | cons s _ =>
      cases k <;> simp only [Zielsatz.KopfHalt] at h
      exact Stmt.blatt_sperreVon s h.1
  | _ => simp only [Block.sperreVon]

/-- A residue at a named stop stands at no lock. -/
theorem restHalt_keineSperre {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {σ : World D} {ρ : Env D Γ}
    {k : Zielsatz.HaltArt} {r : GRest D V l Γ Λ} (h : Zielsatz.RestHalt O passes σ ρ k r) : r.kopfSperre = none := by
  cases r with
  | dann b _ =>
      simp only [GRest.kopfSperre]
      cases k <;> exact kopfHalt_keineSperre (by simpa only [Zielsatz.RestHalt] using h)
  | _ => rfl

include hFort in
/-- **The head at a free lock can step** (progress: it is not finished, waits for no held lock, and stands at no
    named stop). -/
theorem frei_bereit {n : Nat} {t : Faden} {L : D.Lock} (hA : AnSperre (R.M n) t L)
    (hfrei : ∀ u, L ∉ offen ((R.M n).faeden u).spur) : Bereit P O passes (R.M n) t := by
  have hk := anSperre_kopf hA
  have halt : ∀ k, ¬ Zielsatz.HaltBenannt O passes (R.M n) k t := fun k hH => by
    have := restHalt_keineSperre (halt_kopf hH)
    rw [hk] at this
    cases this
  rcases hFort n t with hF | hW | hH | hH | hH | hH | hs
  · exact absurd hF (Zielsatz.anSperre_nicht_fertig hA)
  · obtain ⟨u, -, hu⟩ := hW.2 L hA
    exact absurd hu (hfrei u)
  · exact absurd hH (halt _)
  · exact absurd hH (halt _)
  · exact absurd hH (halt _)
  · exact absurd hH (halt _)
  · exact hs

include hO hRang hFort hFair in
/-- **The head of the queue at a free lock takes it.** -/
theorem kopf_nimmt {n : Nat} {h : Faden} {L : D.Lock} (hk : (R.q n L).head? = some h)
    (hfrei : ∀ u, L ∉ offen ((R.M n).faeden u).spur) :
    ∃ j, n ≤ j ∧ R.akt j = some h ∧ AnSperre (R.M j) h L := by
  apply Classical.byContradiction
  intro hno0
  have hno : ∀ j, n ≤ j → R.akt j = some h → ¬ AnSperre (R.M j) h L :=
    fun j h1 h2 h3 => hno0 ⟨j, h1, h2, h3⟩
  -- from `n` on: `h` stands at `locks L` at the head of the queue, and `L` is free
  have inv : ∀ d, AnSperre (R.M (n + d)) h L ∧ (R.q (n + d) L).head? = some h ∧
      ∀ u, L ∉ offen ((R.M (n + d)).faeden u).spur := by
    intro d
    induction d with
    | zero =>
        exact ⟨(R.glied n L h).mp (List.mem_of_mem_head? hk), hk, hfrei⟩
    | succ d ih =>
        obtain ⟨hA, hkd, hfd⟩ := ih
        have hna : R.akt (n + d) ≠ some h := fun e => hno (n + d) (by omega) e hA
        have hA' := R.an_gleich hna hA
        have hm' : h ∈ R.q (n + d + 1) L := (R.glied _ L h).mpr hA'
        refine ⟨hA', ?_, ?_⟩
        · have hle := R.vorne_le (List.mem_of_mem_head? hkd) hm'
          have h0 : vorne (R.q (n + d) L) h = [] := by
            cases hq : R.q (n + d) L with
            | nil => rw [hq] at hkd; cases hkd
            | cons x xs =>
                rw [hq] at hkd
                simp only [List.head?_cons, Option.some.injEq] at hkd
                subst hkd
                simp only [vorne, ne_eq, decide_not, decide_true, Bool.not_true, Bool.false_eq_true, not_false_eq_true,
  List.takeWhile_cons_of_neg]
          rw [h0] at hle
          exact vorne_leer hm' (List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hle))
        · intro u hu
          by_cases hau : R.akt (n + d) = some u
          · have hfu := hfd u
            have hAu : AnSperre (R.M (n + d)) u L :=
              nimmt_an_sperre hO (R.schritt (n + d) u hau) hfu hu
            have := R.kopf (n + d) u L hau hAu
            rw [hkd] at this
            have huh : h = u := Option.some.inj this
            subst huh
            exact hna hau
          · rw [show n + (d + 1) = n + d + 1 by omega, R.toPlanLauf.fremd (n + d) u hau] at hu
            exact hfd u hu
  obtain ⟨j, hj, hjs⟩ := hFair h n (fun j hj => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
    exact frei_bereit R hFort (inv d).1 (inv d).2.2)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  exact hno (n + d) hj hjs (inv d).1

include hEx in
/-- **A held lock is held for ever by its holder, or it becomes free.** -/
theorem gehalten_oder_frei {n : Nat} {L : D.Lock} :
    (∃ u m, ∀ j, m ≤ j → L ∈ offen ((R.M j).faeden u).spur) ∨
      ∃ m, n ≤ m ∧ ∀ u, L ∉ offen ((R.M m).faeden u).spur := by
  by_cases hf : ∀ u, L ∉ offen ((R.M n).faeden u).spur
  · exact Or.inr ⟨n, Nat.le_refl n, hf⟩
  obtain ⟨u, hu⟩ : ∃ u, L ∈ offen ((R.M n).faeden u).spur :=
    Classical.byContradiction fun hc => hf fun u hu => hc ⟨u, hu⟩
  by_cases hfor : ∀ j, n ≤ j → L ∈ offen ((R.M j).faeden u).spur
  · exact Or.inl ⟨u, n, hfor⟩
  have hfor : ∃ j, n ≤ j ∧ L ∉ offen ((R.M j).faeden u).spur :=
    Classical.byContradiction fun hc => hfor fun j hj => Classical.byContradiction fun hn => hc ⟨j, hj, hn⟩
  -- step by step from `n`: `u` still holds `L`, or `L` was free at some step in between
  have stufe : ∀ d, L ∈ offen ((R.M (n + d)).faeden u).spur ∨
      ∃ m, n ≤ m ∧ ∀ v, L ∉ offen ((R.M m).faeden v).spur := by
    intro d
    induction d with
    | zero => exact Or.inl hu
    | succ d ih =>
        rcases ih with hprev | hfrei
        · by_cases hnow : L ∈ offen ((R.M (n + (d + 1))).faeden u).spur
          · exact Or.inl hnow
          · refine Or.inr ⟨n + (d + 1), by omega, fun v hv => ?_⟩
            by_cases hvu : v = u
            · subst hvu; exact hnow hv
            · -- `u` acted (it lost the lock), so `v` did not, and `v` held `L` beside `u` before
              have hua : R.akt (n + d) = some u := by
                apply Classical.byContradiction
                intro ha
                rw [show n + (d + 1) = n + d + 1 by omega, R.toPlanLauf.fremd (n + d) u ha] at hnow
                exact hnow hprev
              have hva : R.akt (n + d) ≠ some v := fun e => hvu (Option.some.inj (e.symm.trans hua))
              rw [show n + (d + 1) = n + d + 1 by omega, R.toPlanLauf.fremd (n + d) v hva] at hv
              exact hEx (n + d) u v (Ne.symm hvu) L hprev hv
        · exact Or.inr hfrei
  obtain ⟨j, hj, hjn⟩ := hfor
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  rcases stufe d with h | h
  · exact absurd h hjn
  · exact Or.inr h

include hO hRang hEx hFort hFair in
/-- **STARVATION FREEDOM.** A thread standing at `locks L` on a fair run of the ticket lock takes `L`, or some
    thread holds `L` from some step on for ever. -/
theorem hungerfrei {n : Nat} {t : Faden} {L : D.Lock} (hA : AnSperre (R.M n) t L) :
    (∃ j, n ≤ j ∧ R.akt j = some t ∧ AnSperre (R.M j) t L) ∨
      ∃ u m, ∀ j, m ≤ j → L ∈ offen ((R.M j).faeden u).spur := by
  -- strong induction on the number of threads ahead of `t`
  suffices H : ∀ k n, t ∈ R.q n L → (vorne (R.q n L) t).length ≤ k →
      (∃ j, n ≤ j ∧ R.akt j = some t ∧ AnSperre (R.M j) t L) ∨
        ∃ u m, ∀ j, m ≤ j → L ∈ offen ((R.M j).faeden u).spur from
    H _ n ((R.glied n L t).mpr hA) (Nat.le_refl _)
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro n ht hk
  rcases gehalten_oder_frei R hEx (n := n) (L := L) with hfor | ⟨m, hnm, hfrei⟩
  · exact Or.inr hfor
  -- at `m` the lock is free; `t` is still waiting there with nobody new ahead, or it took the lock
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rcases R.bleibt ht d with ⟨htm, hle⟩ | ⟨j, h1, -, h3, h4⟩
  · -- the head of the queue at `m` takes the lock
    obtain ⟨h, hkh⟩ : ∃ h, (R.q (n + d) L).head? = some h := by
      cases hq : R.q (n + d) L with
      | nil => rw [hq] at htm; exact absurd htm List.not_mem_nil
      | cons x xs => exact ⟨x, rfl⟩
    obtain ⟨j, hj, hja, hjA⟩ := kopf_nimmt R hO hRang hFort hFair hkh hfrei
    by_cases hht : h = t
    · subst hht; exact Or.inl ⟨j, by omega, hja, hjA⟩
    -- `t` waits up to `j`, and one step later `h` is gone from ahead of it
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hj
    rcases R.bleibt htm e with ⟨htj, hle2⟩ | ⟨j', h1, -, h3, h4⟩
    · have htj1 : t ∈ R.q (n + d + e + 1) L := by
        have hna : R.akt (n + d + e) ≠ some t := fun e' => hht (Option.some.inj (hja.symm.trans e'))
        exact (R.glied _ L t).mpr (R.an_gleich hna ((R.glied _ L t).mp htj))
      -- `h` took `L`: it holds `L` now and stands at no `locks L`
      have hhn : h ∉ R.q (n + d + e + 1) L := by
        intro hm
        have hA1 := (R.glied _ L h).mp hm
        obtain ⟨w, hw⟩ := hRang (n + d + e + 1) h
        have hfr := (sperre_rang hw hA1).1
        have e2 := (sperre_schritt hjA (R.schritt _ h hja)).2
        rw [e2] at hfr
        simp only [offen, List.mem_cons, true_or, not_true_eq_false] at hfr
      -- `h` was ahead of `t` at `j`: it heads the queue there, as it did at `m`
      have hvj : h ∈ vorne (R.q (n + d + e) L) t :=
        kopf_vorne (R.kopf _ h L hja hjA) hht
      have hlt := R.vorne_lt htj htj1 hvj hhn
      rcases ih _ (by omega) (n + d + e + 1) htj1 (Nat.le_refl _) with ⟨j2, hj2, hj2a, hj2A⟩ | hf
      · exact Or.inl ⟨j2, by omega, hj2a, hj2A⟩
      · exact Or.inr hf
    · exact Or.inl ⟨j', by omega, h3, h4⟩
  · exact Or.inl ⟨j, h1, h3, h4⟩

end Hunger

end Gabbro.Grammatik
