module

public import Grammatik.Nebenlaeufigkeit.Rennfreiheit.RennfreiG

@[expose] public section



namespace Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Trace deltas of one step -/

/-- The trace delta of an ACCESS step: the new trace is `X ++ s`, every
    access event of `X` is old or good, consistency is kept, `X` takes no
    lock, and the held locks are unchanged. -/
def ZugriffsDelta (s s' : List (Ereignis D)) : Prop :=
  ∃ X : List (Ereignis D), s' = X ++ s ∧
    (∀ e ∈ X, e.istZugriff = true → e ∈ s ∨ e.gut) ∧
    (Konsistent s → Konsistent s') ∧ (∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ X) ∧
    offen s' = offen s

/-- The trace delta of a LOCK step: the new trace is `X ++ s` with no access
    event in `X`, consistency kept. -/
def SperrDelta (s s' : List (Ereignis D)) : Prop :=
  ∃ X : List (Ereignis D), s' = X ++ s ∧ (∀ e ∈ X, e.istZugriff = false) ∧
    (Konsistent s → Konsistent s')

theorem zugriffsDelta_refl (s : List (Ereignis D)) : ZugriffsDelta s s :=
  ⟨[], rfl, fun _ he => absurd he List.not_mem_nil, id,
    fun _ _ h => absurd h List.not_mem_nil, rfl⟩

theorem zugriffsDelta_brav {σ σ' : World D} (hB : Brav σ σ') (neu : List (Ereignis D))
    (hneu : σ'.spur = neu ++ σ.spur) (hk : ∀ (L : D.Lock) (h : List D.Lock), Ereignis.nimmt L h ∉ neu) :
    ZugriffsDelta σ.spur σ'.spur :=
  ⟨neu, hneu, fun e he _ => hB.2.1 e (by rw [hneu]; exact List.mem_append_left _ he), hB.2.2, hk,
    hB.1⟩

theorem leseEv_zugriff (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob)) :
    NurZugriff (leseEv σ Λ os) := by
  intro e he
  simp only [leseEv, List.mem_map] at he
  obtain ⟨o, _, rfl⟩ := he
  cases o <;> rfl

theorem zugriffsDelta_lese (σ : World D) (Λ : List (Res D)) (os : List (D.Tab ⊕ D.Glob))
    (ho : ∀ o ∈ os, OrtDarf Λ o) (hh : HeldIn Λ σ.haelt) :
    ZugriffsDelta σ.spur (σ.lese Λ os).spur :=
  zugriffsDelta_brav (gut_lese (W := fun _ => true) (G := fun _ => true) σ Λ os ho hh).2
    (leseEv σ Λ os) rfl (kein_nimmt (leseEv_zugriff σ Λ os))

/-- A question to the outside is an access-like delta: one `fremd` event, no lock. -/
theorem zugriffsDelta_fragt (σ : World D) (q : D.Ax ⊕ D.Reg ⊕ D.Glob) :
    ZugriffsDelta σ.spur (σ.fragt q).spur :=
  zugriffsDelta_brav (gut_fragt (W := fun _ => true) (G := fun _ => true) σ q).2 [.fremd q] rfl
    (fun L h hm => by simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hm)

/-- A question to the outside, then the reads of the form. -/
theorem zugriffsDelta_fragt_lese (σ : World D) (q : D.Ax ⊕ D.Reg ⊕ D.Glob) (Λ : List (Res D))
    (os : List (D.Tab ⊕ D.Glob)) (ho : ∀ o ∈ os, OrtDarf Λ o) (hh : HeldIn Λ σ.haelt) :
    ZugriffsDelta σ.spur ((σ.fragt q).lese Λ os).spur :=
  zugriffsDelta_brav ((gut_fragt (W := fun _ => true) (G := fun _ => true) σ q).trans
      (gut_lese (σ.fragt q) Λ os ho hh)).2
    (leseEv (σ.fragt q) Λ os ++ [.fremd q]) (by rw [List.append_assoc]; rfl)
    (fun L h hm => by
      rcases List.mem_append.mp hm with hm | hm
      · exact kein_nimmt (leseEv_zugriff _ _ _) L h hm
      · simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at hm)

theorem sperrDelta_nimmt (s : List (Ereignis D)) (L : D.Lock) :
    SperrDelta s (Ereignis.nimmt L (offen s) :: s) :=
  ⟨[Ereignis.nimmt L (offen s)], rfl, fun e he => by
    rw [List.mem_singleton] at he; subst he; rfl, fun hk => konsistent_cons rfl hk⟩

theorem sperrDelta_gibt (s : List (Ereignis D)) (L : D.Lock) :
    SperrDelta s (Ereignis.gibt L :: s) :=
  ⟨[Ereignis.gibt L], rfl, fun e he => by
    rw [List.mem_singleton] at he; subst he; rfl, fun hk => konsistent_cons trivial hk⟩

/-- The static holdings of a residue give the held set of the thread world. -/
theorem heldIn_weltVon {M : RufMaschineG D} {f : Faden} {Λ : List (Res D)}
    (h : HeldIn Λ (offen (M.faeden f).spur)) : HeldIn Λ (M.weltVon f).haelt :=
  h

/-! ## 2. Every step moves the acting thread's trace by one of the two deltas -/

section Delta

variable {P : Programm D} {O : Orakel D} {passes : Nat}

/-- **The trace delta of one step.** Every step of thread `f` either is an
    access step (`ZugriffsDelta`: no lock taken, held locks unchanged, new
    access events good) or a lock step (`SperrDelta`: only lock events, and
    shared memory unchanged). The lock steps are exactly `dannLocks`,
    `freiGib` and the two `frei` peels. -/
end Delta
end Gabbro.Grammatik
