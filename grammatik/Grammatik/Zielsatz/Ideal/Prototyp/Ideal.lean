/-
  File:      Grammatik/Zielsatz/Ideal/Prototyp/Ideal.lean
  Subject:   PROTOTYPE of S7: the ideal meaning `I` of the fragment (`dokumente/PERFECT-MODEL.md` §3.4), with
             `I.Bestimmt` and `I.Fortschritt`.

  `I` has no position inside a unit: one step of `I` is one WHOLE unit of one context -- a lock section (acquire,
  body, release with the view transfer of the lock), a masked section, one atomic operation, `lend`, `takeBack`,
  a local assignment, or one whole run of the interrupt handler. A step carries the answers to the outside
  questions its unit asked (in order) and the choice `w` of its atomic operation. There is no lock owner and no
  mask in an `I` state: between two units no lock is held and no mask is set. The device's writes to a lent
  buffer are not steps of `I`: the buffer's content returns as the answer of `takeBack` (§4: answer as owned
  value, arbitrary-change rely).
  * `I.Bestimmt` (`iStep_bestimmt`): a step is determined by the state, the context, the answers and the choice.
  * `I.Fortschritt` (`iStep_fortschritt`, `iStep_irq`): in every reachable state every thread with a unit left
    has a step, and the handler always has one. No `I` state is blocked at all: with lock sections as
    indivisible units, no lock is ever held between two steps (see the report of the prototype).
-/
module

public import Grammatik.Zielsatz.Ideal.Prototyp.Impl

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Ideal.Prototyp

/-- A thread of `I`: no position inside a unit. -/
structure ITh where
  prog : List Seg
  regs : Regs
  view : View
  lent : Nat → Bool

/-- The state of `I`: no lock owner, no mask. -/
structure IS where
  th : Fin 2 → ITh
  mem : Mem
  lview : Nat → View
  am : AMem

/-- The initial state of `I`. -/
def IS.init (P : Prog) : IS where
  th t := ⟨P.thread t, fun _ => 0, fun _ => 0, fun _ => false⟩
  mem _ := 0
  lview _ := fun _ => 0
  am := AMem.init

/-- Replace thread `t`. -/
def IS.setTh (i : IS) (t : Fin 2) (x : ITh) : IS := { i with th := upd i.th t x }

/-- One step of `I`: one whole unit of one context, with the answers of its questions and its choice `w`. -/
inductive IStep (P : Prog) : IS → Ctx → List Int → Nat → IS → Prop
  | lock {i t k body ps as w ρ' m'} : (i.th t).prog = .lock k body :: ps →
      execOps body as ((i.th t).regs, i.mem) = some (ρ', m') →
      IStep P i (.thr t) as w
        { (i.setTh t ⟨ps, ρ', vjoin (i.th t).view (i.lview k), (i.th t).lent⟩) with
            mem := m', lview := upd i.lview k (vjoin (i.th t).view (i.lview k)) }
  | masked {i body ps as w ρ' m'} : (i.th 0).prog = .masked body :: ps →
      execOps body as ((i.th 0).regs, i.mem) = some (ρ', m') →
      IStep P i (.thr 0) as w { (i.setTh 0 ⟨ps, ρ', (i.th 0).view, (i.th 0).lent⟩) with mem := m' }
  | atom {i t o op ps w ρ' V' A'} : (i.th t).prog = .atom o op :: ps →
      AStep o op (i.th t).regs (i.th t).view i.am w ρ' V' A' →
      IStep P i (.thr t) [] w { (i.setTh t ⟨ps, ρ', V', (i.th t).lent⟩) with am := A' }
  | lend {i t x ps w} : (i.th t).prog = .lend x :: ps →
      IStep P i (.thr t) [] w (i.setTh t { i.th t with prog := ps, lent := upd (i.th t).lent x true })
  | take {i t x ps v w} : (i.th t).prog = .takeBack x :: ps →
      IStep P i (.thr t) [v] w
        { (i.setTh t { i.th t with prog := ps, lent := upd (i.th t).lent x false }) with mem := upd i.mem x v }
  | set {i t r e ps w} : (i.th t).prog = .set r e :: ps →
      IStep P i (.thr t) [] w
        (i.setTh t { i.th t with prog := ps, regs := upd (i.th t).regs r (e.eval (i.th t).regs) })
  | handler {i as w ρ' m'} : execOps P.handler as ((fun _ => 0), i.mem) = some (ρ', m') →
      IStep P i .irq as w { i with mem := m' }

/-- Finite runs of `I` with their trace of contexts and answer lists. -/
inductive IStar (P : Prog) : IS → List (Ctx × List Int) → IS → Prop
  | refl (i : IS) : IStar P i [] i
  | tail {i i' i'' tr c as w} : IStar P i tr i' → IStep P i' c as w i'' → IStar P i (tr ++ [(c, as)]) i''

/-- No masked unit (only thread 0 shares a core with the handler). -/
def OhneMask (us : List Seg) : Prop := ∀ u ∈ us, ∀ b, u ≠ .masked b

/-- The invariant of reachable `I` states: the atomic memory invariants, and thread 1 masks nothing. -/
def IInv (i : IS) : Prop :=
  TsEind i.am ∧ Gedeckt i.am i.am.scv ∧ (∀ t, Gedeckt i.am (i.th t).view) ∧ (∀ k, Gedeckt i.am (i.lview k)) ∧
    OhneMask (i.th 1).prog

theorem ohneMask_tail {u : Seg} {us : List Seg} (h : OhneMask (u :: us)) : OhneMask us :=
  fun x hx => h x (List.mem_cons_of_mem u hx)

theorem iInv_init (P : Prog) (h : OhneMask (P.thread 1)) : IInv (IS.init P) :=
  ⟨tsEind_init, gedeckt_init _ (fun _ => rfl), fun _ => gedeckt_init _ (fun _ => rfl),
    fun _ => gedeckt_init _ (fun _ => rfl), h⟩

theorem setTh_th_ne {i : IS} {t u : Fin 2} {x : ITh} (h : u ≠ t) : (i.setTh t x).th u = i.th u := upd_ne _ _ h

/-- Thread 1 keeps no masked unit when thread `t` drops the head of its program. -/
theorem ohneMask_setTh {i : IS} {t : Fin 2} {x : ITh} {u : Seg} (h : OhneMask (i.th 1).prog)
    (hp : (i.th t).prog = u :: x.prog) : OhneMask ((i.setTh t x).th 1).prog := by
  by_cases ht : (1 : Fin 2) = t
  · subst ht
    simp only [IS.setTh, upd_same]
    rw [hp] at h
    exact ohneMask_tail h
  · rw [setTh_th_ne ht]; exact h

/-- Covered thread views stay covered when one thread gets a covered view. -/
theorem gedeckt_setTh {A : AMem} {i : IS} {t : Fin 2} {x : ITh} (hV : ∀ u, Gedeckt A (i.th u).view)
    (hx : Gedeckt A x.view) : ∀ u, Gedeckt A ((i.setTh t x).th u).view := by
  intro u
  by_cases hu : u = t
  · subst hu; simp only [IS.setTh, upd_same]; exact hx
  · simp only [IS.setTh, upd_ne _ _ hu]; exact hV u

/-- Covered lock views stay covered when one lock gets a covered view. -/
theorem gedeckt_upd_all {A : AMem} {L : Nat → View} {k : Nat} {V : View} (hL : ∀ k, Gedeckt A (L k))
    (hx : Gedeckt A V) : ∀ k', Gedeckt A (upd L k V k') := by
  intro k'
  by_cases hk : k' = k
  · subst hk; simp only [upd_same]; exact hx
  · simp only [upd_ne _ _ hk]; exact hL k'

/-- Every step of `I` keeps the invariant. -/
theorem iInv_step {P : Prog} {i i' : IS} {c : Ctx} {as : List Int} {w : Nat} (hI : IInv i)
    (h : IStep P i c as w i') : IInv i' := by
  obtain ⟨hT, hS, hV, hL, hM⟩ := hI
  cases h with
  | lock hp _ =>
      exact ⟨hT, hS, gedeckt_setTh hV (gedeckt_join (hV _) (hL _)),
        gedeckt_upd_all hL (gedeckt_join (hV _) (hL _)), ohneMask_setTh hM hp⟩
  | masked hp _ =>
      exact ⟨hT, hS, gedeckt_setTh hV (hV 0), hL, by rw [setTh_th_ne (by decide)]; exact hM⟩
  | atom hp ha =>
      obtain ⟨hT', hS', hV', hW⟩ := aStep_inv ha hT hS (hV _)
      exact ⟨hT', hS', gedeckt_setTh (fun u => hW _ (hV u)) hV', fun k => hW _ (hL k), ohneMask_setTh hM hp⟩
  | lend hp => exact ⟨hT, hS, gedeckt_setTh hV (hV _), hL, ohneMask_setTh hM hp⟩
  | take hp => exact ⟨hT, hS, gedeckt_setTh hV (hV _), hL, ohneMask_setTh hM hp⟩
  | set hp => exact ⟨hT, hS, gedeckt_setTh hV (hV _), hL, ohneMask_setTh hM hp⟩
  | handler _ => exact ⟨hT, hS, hV, hL, hM⟩

theorem iInv_star {P : Prog} {i i' : IS} {tr : List (Ctx × List Int)} (hI : IInv i) (h : IStar P i tr i') :
    IInv i' := by
  induction h with
  | refl => exact hI
  | tail _ hs ih => exact iInv_step ih hs

/-! ## `I.Bestimmt` -/

/-- **`I.Bestimmt` of the fragment.** In a state with unique timestamps, the context, the answers and the choice
    determine the step: the only named choice points are the scheduler (which context), the outside answers and
    the timestamp of an atomic operation. -/
theorem iStep_bestimmt {P : Prog} {i i₁ i₂ : IS} {c : Ctx} {as : List Int} {w : Nat} (hT : TsEind i.am)
    (h₁ : IStep P i c as w i₁) (h₂ : IStep P i c as w i₂) : i₁ = i₂ := by
  cases h₁ <;> cases h₂ <;> simp_all
  rename_i _ ha _ ha'
  obtain ⟨rfl, rfl, rfl⟩ := aStep_bestimmt hT ha ha'
  simp

/-! ## `I.Fortschritt` -/

/-- Every body has answers under which it runs to its end. -/
theorem execOps_ex : ∀ (ops : List Op) (st : Regs × Mem), ∃ as st', execOps ops as st = some st'
  | [], st => ⟨[], st, rfl⟩
  | .dev r _ :: ops, (ρ, m) => by
      obtain ⟨as, st', h⟩ := execOps_ex ops (upd ρ r 0, m)
      exact ⟨0 :: as, st', by simpa [execOps] using h⟩
  | .set r e :: ops, (ρ, m) => by
      obtain ⟨as, st', h⟩ := execOps_ex ops (upd ρ r (e.eval ρ), m)
      exact ⟨as, st', by simpa [execOps] using h⟩
  | .load r x :: ops, (ρ, m) => by
      obtain ⟨as, st', h⟩ := execOps_ex ops (upd ρ r (m x), m)
      exact ⟨as, st', by simpa [execOps] using h⟩
  | .store x e :: ops, (ρ, m) => by
      obtain ⟨as, st', h⟩ := execOps_ex ops (ρ, upd m x (e.eval ρ))
      exact ⟨as, st', by simpa [execOps] using h⟩

/-- **`I.Fortschritt` of the fragment, threads.** In a state of the invariant, every thread with a unit left has
    a step: no thread of `I` is ever blocked (lock sections are indivisible, so no lock is held). -/
theorem iStep_fortschritt (P : Prog) {i : IS} (hI : IInv i) (t : Fin 2) (hne : (i.th t).prog ≠ []) :
    ∃ as w i', IStep P i (.thr t) as w i' := by
  obtain ⟨_, _, hV, _, hM⟩ := hI
  cases hp : (i.th t).prog with
  | nil => exact absurd hp hne
  | cons u ps =>
      cases u with
      | lock k body =>
          obtain ⟨as, ⟨ρ', m'⟩, he⟩ := execOps_ex body ((i.th t).regs, i.mem)
          exact ⟨as, 0, _, IStep.lock hp he⟩
      | masked body =>
          rcases t with ⟨_ | _ | n, hn⟩
          · obtain ⟨as, ⟨ρ', m'⟩, he⟩ := execOps_ex body ((i.th 0).regs, i.mem)
            exact ⟨as, 0, _, IStep.masked hp he⟩
          · exact absurd rfl (hM (.masked body) (by
              rw [show (1 : Fin 2) = ⟨1, hn⟩ from rfl, hp]; exact List.mem_cons_self) body)
          · omega
      | atom o op =>
          obtain ⟨w, ρ', V', A', ha⟩ := aStep_ex o op (i.th t).regs (i.th t).view i.am (hV t)
          exact ⟨[], w, _, IStep.atom hp ha⟩
      | lend x => exact ⟨[], 0, _, IStep.lend hp⟩
      | takeBack x => exact ⟨[0], 0, _, IStep.take (v := 0) hp⟩
      | set r e => exact ⟨[], 0, _, IStep.set hp⟩

/-- **`I.Fortschritt` of the fragment, handler.** The interrupt handler can always run as one unit. -/
theorem iStep_irq (P : Prog) (i : IS) : ∃ as w i', IStep P i .irq as w i' := by
  obtain ⟨as, ⟨ρ', m'⟩, he⟩ := execOps_ex P.handler ((fun _ => 0), i.mem)
  exact ⟨as, 0, _, IStep.handler he⟩

end Gabbro.Grammatik.Zielsatz.Ideal.Prototyp
