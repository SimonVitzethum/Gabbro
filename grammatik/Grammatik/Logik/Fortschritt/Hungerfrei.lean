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
module
public import Grammatik.Logik.Fortschritt.HungerfreiBasis
import all Grammatik.Logik.Fortschritt.HungerfreiBasis
public import Grammatik.Logik.Fortschritt.Lebendigkeit
public import Grammatik.Logik.Fortschritt.PlanLauf
public import Grammatik.Zielsatz.Eigenschaften.Masken
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

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
      cases s with
      | axiomCallElse => rfl
      | _ =>
          cases k <;> simp only [Zielsatz.KopfHalt] at h
          exact Stmt.blatt_sperreVon _ h.1
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
