/-
  File:      Grammatik/Zielsatz/Masken.lean
  Subject:   SAME-CORE INTERRUPT PREEMPTION (fix lane F11, 2026-09-22, OFFEN O19):
             the leg `keinKernHalt` of `Ziel`, proved.

  The gap this closes (reviews G02 F1, G12 F1): an `entry … vector … via idt` dispatch root
  travels into the model as an ordinary start, and machine G interleaves threads freely. So
  in G a handler and the thread it interrupted are two independent threads, and the
  configuration `H102` refuses -- the handler spins on a lock its own core's thread holds --
  is no deadlock in G at all. `D.maskiert` (the exported `masks irqs`, lane 255) was read by
  nothing in `Zielsatz/`.

  What is proved here, and with which premises:
  * `handler_sperre_maskiert` -- THE PROGRAM SIDE (`H102`). If every lock the feature set of
    a thread's call graph admits is declared `masks irqs`, then at every machine of a run
    that thread stands only at masked locks. The carrier is the existing frame invariant
    (`MerkInvG`, FadenMerkmal.lean): the `sperre` field of `Merkmal` is exactly "which locks
    the bodies may take".
  * `kernHaltG_gilt` -- THE SENTENCE. Under a core schedule (`KernPlan`, Spec.lean: a handler
    enters only where no thread of its core holds a masked lock, and runs to completion
    before that thread continues) a handler never stands at a lock a thread of its core
    holds. Proof: the lock it stands at is masked (above); by "run to completion" no other
    thread of the core stepped since the handler's first step, so that thread held the lock
    already then; by "entry only when unmasked" the handler could not have entered. It needs
    NOTHING from the premise groups (a)-(d) -- like `speicherSicher` it holds for every
    program of G -- so `Ziel` gains a leg and no premise moves.
  * `maskenDisziplinB` -- the Bool of the program side over a member list, the counterpart of
    the Rust `H102` (`crates/gabbro-check/src/kontexte.rs`), with `merkAbg_maskM` turning it
    into the leg's hypothesis.

  NOT closed by this file (OFFEN O19, narrowed): `Einheit` does not say WHICH declared starts
  are handlers and G has no cores, so `kern`/`H` are arguments of the leg and not fields of
  the unit; the checker's Bool (a) therefore cannot carry `maskenDisziplinB`, and the C side
  realises no masking (the emitter writes no `cli`/`sti`).
-/
import Grammatik.Zielsatz.Spec

namespace Gabbro.Grammatik.Zielsatz

open Gabbro.Grammatik

variable {D : Deklaration}

/-! ## 1. Helpers over runs and lock heads -/

/-- The frame invariant along a run: what `merkInvG_erreichbar` does from `RufStartG`, from
    any start machine at which it holds. -/
theorem merkInvG_lauf {P : Programm D} {O : Orakel D} {passes : Nat} {M0 : RufMaschineG D}
    {ms : Nat → RufMaschineG D} {fs : Nat → Faden} {n : Nat}
    (hl : LaufG P O passes M0 ms fs n) {Z : D.Fn → Prop} {A : D.Fn → Merkmal D}
    (hA : MerkAbg P Z A) (t : Faden) (h0 : MerkInvG Z A (M0.faeden t)) :
    ∀ k, k ≤ n → MerkInvG Z A ((ms k).faeden t)
  | 0, _ => by rw [hl.1]; exact h0
  | k + 1, hk => by
      have hs := hl.2 k (by omega)
      have ih := merkInvG_lauf hl hA t h0 k (by omega)
      by_cases htu : t = fs k
      · subst htu
        exact merkInvG_schritt hA hs ih
      · rw [rufSchrittG_fremd hs t htu]
        exact ih

/-- Standing at a lock head is a property of the thread's own state. -/
theorem anSperre_gleich {M M' : RufMaschineG D} {t t' : Faden} {L : D.Lock}
    (he : M'.faeden t' = M.faeden t) (h : AnSperre M t L) : AnSperre M' t' L := by
  unfold AnSperre
  rw [he]
  exact h

/-- A thread standing at a lock head is not finished. -/
theorem anSperre_nicht_fertig {M : RufMaschineG D} {t : Faden} {L : D.Lock}
    (h : AnSperre M t L) : ¬ FertigG M t := by
  obtain ⟨l, Γ, Λ, Λ'', ρ, hr, body, rest, k, hhead⟩ := h
  intro hF
  have h2 := hF.2
  rw [hhead] at h2
  simp [GRest.anRueck, Block.istRueck, Stmt.istRueck] at h2

/-- A thread whose residue is the whole body (an `.ende` layer) stands at no lock head. -/
theorem anSperre_ende_falsch {M : RufMaschineG D} {t : Faden} {L : D.Lock}
    {l0 : Bool} {Γ0 : Ctx} {Λ0 : List (Res D)} {ρ0 : Env D Γ0}
    {b : Endblock D (vertragVon D (M.faeden t).kopf.f) l0 Γ0 Λ0}
    (hr : (M.faeden t).kopf.rest = ⟨l0, Γ0, Λ0, ρ0, .ende b⟩) : ¬ AnSperre M t L := by
  rintro ⟨l, Γ, Λ, Λ'', ρ, hrk, body, rest, k, hhead⟩
  have hE := hr.symm.trans hhead
  simp only [Sigma.mk.injEq] at hE
  obtain ⟨rfl, hE⟩ := hE
  have hE1 := eq_of_heq hE
  simp only [Sigma.mk.injEq] at hE1
  obtain ⟨rfl, hE1⟩ := hE1
  have hE2 := eq_of_heq hE1
  simp only [Sigma.mk.injEq] at hE2
  obtain ⟨rfl, hE2⟩ := hE2
  have hE3 := eq_of_heq hE2
  simp at hE3

/-- **No thread of a start machine stands at a lock head**: its residue is the whole body
    (`.ende`), not a `.dann` layer. -/
theorem anSperre_start_falsch (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (t : Faden) (L : D.Lock) :
    ¬ AnSperre (RufStartG P sp init) t L :=
  anSperre_ende_falsch (l0 := false) (ρ0 := (init t).2)
    (b := P.rumpf (init t).1) rfl

/-- The first index at which a run does something. -/
theorem erster_index (Q : Nat → Prop) (n : Nat) (h : ∃ i, i < n ∧ Q i) :
    ∃ i, i < n ∧ Q i ∧ ∀ k, k < i → ¬ Q k := by
  classical
  induction n with
  | zero => obtain ⟨i, hi, -⟩ := h; omega
  | succ m ih =>
      by_cases hm : ∃ i, i < m ∧ Q i
      · obtain ⟨i, hi, hq, hmin⟩ := ih hm
        exact ⟨i, by omega, hq, hmin⟩
      · obtain ⟨i, hi, hq⟩ := h
        have hm' : ∀ k, k < m → ¬ Q k := fun k hk hqk => hm ⟨k, hk, hqk⟩
        have him : i = m := by
          rcases Nat.lt_or_ge i m with h1 | h1
          · exact absurd hq (hm' i h1)
          · omega
        subst him
        exact ⟨i, by omega, hq, fun k hk => hm' k hk⟩

/-! ## 2. The program side: a handler stands only at masked locks -/

/-- The lock at a `locks` head is one the frame's feature set admits. -/
theorem sperre_merkmal {Z : D.Fn → Prop} {A : D.Fn → Merkmal D} {M : RufMaschineG D}
    {t : Faden} (h : MerkInvG Z A (M.faeden t)) {L : D.Lock} (hA : AnSperre M t L) :
    Z ((M.faeden t).kopf.f) ∧ (A (M.faeden t).kopf.f).sperre L = true := by
  obtain ⟨l, Γ, Λ, Λ'', ρ, hr, body, rest, k, hhead⟩ := hA
  have hk := h _ List.mem_cons_self
  refine ⟨hk.1, ?_⟩
  have hR := hk.2
  rw [hhead] at hR
  simp only [GRest.mR, mB, mS, Bool.and_eq_true] at hR
  exact hR.1.1.1

/-- **`H102` in the model**: if every lock the handler's features admit is declared
    `masks irqs`, then at every machine of a run from `M0` the handler stands only at masked
    locks. -/
theorem handler_sperre_maskiert {P : Programm D} {O : Orakel D} {passes : Nat}
    {M0 : RufMaschineG D} {ms : Nat → RufMaschineG D} {fs : Nat → Faden} {n : Nat}
    (hl : LaufG P O passes M0 ms fs n) {Z : D.Fn → Prop} {A : D.Fn → Merkmal D}
    (hA : MerkAbg P Z A) {g : Faden} (h0 : MerkInvG Z A (M0.faeden g))
    (hmask : ∀ (f : D.Fn) (L : D.Lock), Z f → (A f).sperre L = true → D.maskiert L = true)
    {k : Nat} (hk : k ≤ n) {L : D.Lock} (hs : AnSperre (ms k) g L) : D.maskiert L = true := by
  have hInv := merkInvG_lauf hl hA g h0 k hk
  have h := sperre_merkmal hInv hs
  exact hmask _ L h.1 h.2

/-! ## 3. The sentence: no same-core interrupt deadlock -/

/-- **THE LEG, PROVED, for every program of G.** A handler never stands at a lock a thread
    of its own core holds: the lock is masked (the program side, `H102`), so by "run to
    completion" that thread has not stepped since the handler entered, so it held the lock
    already at the handler's entry -- which "entry only when unmasked" forbids. -/
theorem kernHaltG_gilt (P : Programm D) (O : Orakel D) (passes : Nat)
    (M0 M : RufMaschineG D) : KernHaltG P O passes M0 M := by
  intro kern H Z A hAbg hInv0 hMask hM0 ms fs n hl hMn hKP g f L hHg hfg hkern hA hL
  subst hMn
  have hnf : ¬ FertigG (ms n) g := anSperre_nicht_fertig hA
  by_cases hstep : ∃ i, i < n ∧ fs i = g
  · obtain ⟨i, hin, hig, hmin⟩ := erster_index (fun i => fs i = g) n hstep
    -- the lock the handler stands at is masked
    have hmaskL : D.maskiert L = true :=
      handler_sperre_maskiert hl (hAbg g hHg) (hInv0 g hHg)
        (fun f' L' hZ hsp => hMask g hHg f' L' hZ hsp) (Nat.le_refl n) hA
    -- no step of `f` between the handler's first step and the end
    have hfn : ∀ k, i ≤ k → k < n → fs k ≠ f := by
      intro k hik hkn hk
      have h2 := hKP.2 g i n k hHg hig hmin hik hkn (Nat.le_refl n) hnf
        (by rw [hk]; exact hkern)
      rw [hk] at h2
      exact hfg h2
    -- so `f` holds the lock already at the handler's first step
    have hsub : LaufG P O passes (ms i) (fun k => ms (i + k)) (fun k => fs (i + k)) (n - i) :=
      ⟨rfl, fun k hk => by
        have h3 := hl.2 (i + k) (by omega)
        rw [Nat.add_assoc] at h3
        exact h3⟩
    have hconst := laufG_fremd hsub f (fun k hk => hfn (i + k) (by omega) (by omega))
      (n - i) (Nat.le_refl _)
    have e : i + (n - i) = n := by omega
    rw [e] at hconst
    have hLi : L ∈ offen ((ms i).faeden f).spur := by rw [← hconst]; exact hL
    -- the handler could not have entered there
    have hne : f ≠ fs i := by rw [hig]; exact hfg
    have := hKP.1 i hin (by rw [hig]; exact hHg) (by rw [hig]; exact hmin) f L hne
      (by rw [hig]; exact hkern) hLi
    rw [hmaskL] at this
    exact Bool.noConfusion this
  · have hnie : ∀ k, k < n → fs k ≠ g := fun k hk hq => hstep ⟨k, hk, hq⟩
    have he := laufG_fremd hl g hnie n (Nat.le_refl n)
    exact hM0 g L (anSperre_gleich he.symm hA)

/-! ## 4. The Bool of the program side (the counterpart of the Rust `H102`) -/

/-- The feature set "calls only into `Z`, and takes only locks that mask interrupts". -/
def maskM (fs : List D.Fn) (Z : D.Fn → Bool) : Merkmal D :=
  { rufM fs Z with sperre := fun L => D.maskiert L }

/-- **`H102` over a member list**: every function of the call graph of `w` takes only locks
    declared `masks irqs`. The Rust checker decides the same over the handler's call graph
    (`kontexte.rs`, `H102`). -/
def maskenDisziplinB [DecidableEq D.Fn] (P : Programm D) (fs : List D.Fn) (w : D.Fn) : Bool :=
  fs.all fun f => !(reachB P fs w f) || mE (maskM fs (reachB P fs w)) (P.rumpf f)

/-- The Bool gives the leg's static hypothesis. -/
theorem merkAbg_maskM [DecidableEq D.Fn] {P : Programm D} {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) {w : D.Fn} (hAbgK : AbgK P fs (reachB P fs w))
    (h : maskenDisziplinB P fs w = true) :
    MerkAbg P (fun f => reachB P fs w f = true) (fun _ => maskM fs (reachB P fs w)) := by
  intro f hf
  refine ⟨?_, fun g hg => rufZiel_rufM hvoll hg⟩
  have h1 := (List.all_eq_true.mp h) f (hvoll f)
  simp only [hf, Bool.not_true, Bool.false_or] at h1
  exact h1

/-- The masking hypothesis of the leg holds for `maskM` by construction. -/
theorem maskM_sperre {fs : List D.Fn} {Z : D.Fn → Bool} (f : D.Fn) (L : D.Lock)
    (h : (maskM (D := D) fs Z).sperre L = true) : D.maskiert L = true := h

#print axioms Gabbro.Grammatik.Zielsatz.merkInvG_lauf
#print axioms Gabbro.Grammatik.Zielsatz.anSperre_gleich
#print axioms Gabbro.Grammatik.Zielsatz.anSperre_nicht_fertig
#print axioms Gabbro.Grammatik.Zielsatz.anSperre_ende_falsch
#print axioms Gabbro.Grammatik.Zielsatz.anSperre_start_falsch
#print axioms Gabbro.Grammatik.Zielsatz.sperre_merkmal
#print axioms Gabbro.Grammatik.Zielsatz.handler_sperre_maskiert
#print axioms Gabbro.Grammatik.Zielsatz.kernHaltG_gilt
#print axioms Gabbro.Grammatik.Zielsatz.merkAbg_maskM

end Gabbro.Grammatik.Zielsatz
