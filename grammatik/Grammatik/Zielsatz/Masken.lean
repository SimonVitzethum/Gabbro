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

  WHAT OPUS AGENT H CHANGED (2026-09-26, OFFEN O19). The program now says which functions are
  entered by hardware (`Programm.unterbricht`, the exported `entry … via idt`), (a) demands the
  discipline for them (`AkzeptiertSpec.masken`, the component `maskenB`, Akzeptiert.lean), and
  the leg of `Ziel` is `KernHaltE` (Spec.lean): the handler set is the unit's, not a hypothesis.
  `KernHaltG` -- the F11 form with the program side as hypotheses -- moved here from Spec.lean;
  `kernHaltG_gilt` is the engine, and `kernHaltE_aus` (section 4) discharges the leg from (a):
  the call graph `reachB P fs (init t).1` of each handler thread, the feature set `maskM`
  (closure from `AkzeptiertSpec.abg`, locks from `.masken`, joined by `mE_und`), the invariant
  at the start machine (`merkInvG_start`), no lock head there (`anSperre_start_falsch`).

  STILL NOT CLOSED (OFFEN O19, narrowed again): the C side realises no masking (the emitter
  writes no `cli`/`sti`), so `KernPlan` -- the named hardware schedule inside the leg -- has
  nothing to be related to by translation validation; the leg constrains the handler's FIRST
  entry (in G a handler thread runs once: no re-entry, no handler-on-handler preemption).
-/
import Grammatik.Zielsatz.Spec
import Grammatik.MitRuheStatisch

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

/-- **No same-core interrupt deadlock, with the program side as HYPOTHESES** (fix lane F11,
    2026-09-22, OFFEN O19; the leg of `Ziel` until Opus agent H, 2026-09-26, which replaced it by
    `KernHaltE`, Spec.lean, and moved this definition here). On a run
    from `M0` that a core schedule admits (`KernPlan`), a handler NEVER stands at a lock
    that a thread of its own core holds -- the deadlock `H102` refuses in Rust
    (`beispiele/gift/460`: a handler takes a lock the interrupted thread holds without
    `masks irqs`).

    The program side is a hypothesis of the leg, not of `GabbroZiel`: `Z t` is the call graph
    of thread `t` and `A t` its feature set (FadenMerkmal.lean), and for a HANDLER thread
    every lock its features admit is declared `masks irqs`. That IS `H102`
    (`maskenDisziplinB`, Zielsatz/Masken.lean, decides it over the member list); the
    `Einheit` does not say which roots are handlers, so the checker's Bool cannot carry it
    (OFFEN O19). `M0` is a start machine: no thread stands at a lock there
    (`anSperre_start_falsch`).

    Nothing in the leg constrains the program otherwise: it holds for EVERY program of G
    (`kernHaltG_gilt`), like `speicherSicher`. What it adds to `Ziel` is the reading of a
    schedule G itself does not know -- G interleaves freely, so in G the handler and the
    thread it interrupted are independent threads and the deadlock is none. -/
def KernHaltG (P : Programm D) (O : Orakel D) (passes : Nat) (M0 M : RufMaschineG D) : Prop :=
  ∀ (kern : Faden → Nat) (H : Faden → Prop) (Z : Faden → D.Fn → Prop)
    (A : Faden → D.Fn → Merkmal D),
    (∀ t, H t → MerkAbg P (Z t) (A t)) →
    (∀ t, H t → MerkInvG (Z t) (A t) (M0.faeden t)) →
    (∀ t, H t → ∀ (f : D.Fn) (L : D.Lock), Z t f → (A t f).sperre L = true →
      D.maskiert L = true) →
    (∀ (t : Faden) (L : D.Lock), ¬ AnSperre M0 t L) →
    ∀ (ms : Nat → RufMaschineG D) (fs : Nat → Faden) (n : Nat),
      LaufG P O passes M0 ms fs n → ms n = M → KernPlan kern H ms fs n →
      ∀ (g f : Faden) (L : D.Lock), H g → f ≠ g → kern f = kern g →
        AnSperre M g L → L ∉ offen ((M.faeden f).spur)


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

/-! ## 4. The program side from (a): the leg of `Ziel` (Opus agent H, 2026-09-26) -/

/-- The feature set "calls only into `Z`, and takes only locks that mask interrupts". -/
def maskM (fs : List D.Fn) (Z : D.Fn → Bool) : Merkmal D :=
  { rufM fs Z with sperre := fun L => D.maskiert L }

/-- The masking hypothesis of `KernHaltG` holds for `maskM` by construction. -/
theorem maskM_sperre {fs : List D.Fn} {Z : D.Fn → Bool} (_f : D.Fn) (L : D.Lock)
    (h : (maskM (D := D) fs Z).sperre L = true) : D.maskiert L = true := h

/-- **The closed call graph and the lock discipline give the leg's feature invariant**: a body
    admitted by `rufM` (the closure, `AkzeptiertSpec.abg`) and by `NurMaskiert` (the discipline,
    `AkzeptiertSpec.masken`) is admitted by `maskM` (`mE_und`, then `mE_mono`). -/
theorem mE_maskM {fs : List D.Fn} {Z : D.Fn → Bool} {V : Vertrag D} {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (e : Endblock D V l Γ Λ) (h1 : mE (rufM fs Z) e = true)
    (h2 : mE (NurMaskiert D) e = true) : mE (maskM fs Z) e = true :=
  mE_mono (A := mUnd (rufM fs Z) (NurMaskiert D))
    ⟨fun f hf => by simp only [mUnd, Bool.and_eq_true] at hf; exact hf.1,
     fun n hn => by simp only [mUnd, Bool.and_eq_true] at hn; exact hn.1,
     fun L hL => by simp only [mUnd, Bool.and_eq_true] at hL; exact hL.2⟩
    e (mE_und e h1 h2)

variable [DecidableEq D.Fn]

/-- The closure and the discipline of a handler root `w` give `MerkAbg` for `maskM`. -/
theorem merkAbg_maskM {P : Programm D} {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) {w : D.Fn} (hAbgK : AbgK P fs (reachB P fs w))
    (h : ∀ f, reachB P fs w f = true → mE (NurMaskiert D) (P.rumpf f) = true) :
    MerkAbg P (fun f => reachB P fs w f = true) (fun _ => maskM fs (reachB P fs w)) :=
  fun f hf => ⟨mE_maskM _ (hAbgK f hf) (h f hf), fun _ hg => rufZiel_rufM hvoll hg⟩

omit [DecidableEq D.Fn] in
/-- The start machine's thread runs its root with the whole body still to run. -/
theorem rufStartG_kopf_f (P : Programm D) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (t : Faden) :
    ((RufStartG P sp init).faeden t).kopf.f = (init t).1 := by
  show (match init t with
    | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
        Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
        [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)).kopf.f = _
  cases init t
  rfl

omit [DecidableEq D.Fn] in
/-- **The feature invariant at the start machine**: a thread's only frame is its root with the
    whole body, so a closed feature assignment containing the root holds there. -/
theorem merkInvG_start {P : Programm D} (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (t : Faden)
    {Z : D.Fn → Prop} {A : D.Fn → Merkmal D} (hA : MerkAbg P Z A) (hZ : Z (init t).1) :
    MerkInvG Z A ((RufStartG P sp init).faeden t) := by
  intro F hF
  have e : (RufStartG P sp init).faeden t =
      ⟨[], ⟨(init t).1, (init t).2, sp.welt [], ⟨false, D.params (init t).1,
        Signatur.anfang D (D.signatur (init t).1), (init t).2, .ende (P.rumpf (init t).1)⟩⟩,
        startSpur (init t).1, [RufEreignisF.eintritt (init t).1 (init t).2 (sp.welt [])]⟩ := by
    show (match init t with
      | ⟨g, rho⟩ => (⟨[], ⟨g, rho, sp.welt [], ⟨false, D.params g,
          Signatur.anfang D (D.signatur g), rho, .ende (P.rumpf g)⟩⟩, startSpur g,
          [RufEreignisF.eintritt g rho (sp.welt [])]⟩ : RufFadenG D)) = _
    cases init t
    rfl
  rw [e] at hF
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  subst hF
  exact ⟨hZ, (hA _ hZ).1⟩

/-- **THE LEG OF `Ziel`, from (a)** (Opus agent H, 2026-09-26). On a program that meets the
    closure (`AkzeptiertSpec.abg`) and the handler discipline (`AkzeptiertSpec.masken`), no
    handler of the program ever stands at a lock another thread of its core holds -- on every run
    from the start machine the core hardware admits. Instantiates `kernHaltG_gilt` with the
    handlers the unit declares (`HandlerVon`), the call graph `reachB P fs (init t).1` and the
    feature set `maskM` of each handler thread. -/
theorem kernHaltE_aus {P : Programm D} {O : Orakel D} {passes : Nat} {fs : List D.Fn}
    (hvoll : ∀ g : D.Fn, g ∈ fs) (hAbg : ∀ w, AbgK P fs (reachB P fs w))
    (hMask : MaskenDisziplin P fs) (sp : Speicher D)
    (init : Faden → Σ f : D.Fn, Env D (D.params f)) (M : RufMaschineG D) :
    KernHaltE P O passes (RufStartG P sp init) M := by
  intro kern ms fs' n hl hMn hKP g f L hHg hfg hkern hA
  have hH : ∀ t, HandlerVon P (RufStartG P sp init) t → P.unterbricht (init t).1 = true :=
    fun t ht => by unfold HandlerVon at ht; rw [rufStartG_kopf_f] at ht; exact ht
  exact kernHaltG_gilt P O passes (RufStartG P sp init) M kern (HandlerVon P (RufStartG P sp init))
    (fun t => fun f => reachB P fs (init t).1 f = true)
    (fun t => fun _ => maskM fs (reachB P fs (init t).1))
    (fun t ht => merkAbg_maskM hvoll (hAbg _) (hMask _ (hH t ht)))
    (fun t ht => merkInvG_start sp init t
      (merkAbg_maskM hvoll (hAbg _) (hMask _ (hH t ht))) (reachB_wurzel P fs _))
    (fun t _ f' L' _ h => maskM_sperre f' L' h)
    (fun t L' => anSperre_start_falsch P sp init t L')
    ms fs' n hl hMn hKP g f L hHg hfg hkern hA

omit [DecidableEq D.Fn] in
/-- **Embedding: a program with no handler.** The leg holds with nothing from (a): no thread is a
    handler (`HandlerVon` is empty), so the conclusion is vacuous -- as the old leg `KernHaltG`
    held for every program (`kernHaltG_gilt`). Units with no `entry … via idt` keep their
    conclusion. -/
theorem kernHaltE_ohne_handler {P : Programm D} {O : Orakel D} {passes : Nat}
    (h : ∀ f, P.unterbricht f = false) (M0 M : RufMaschineG D) : KernHaltE P O passes M0 M := by
  intro _ _ _ _ _ _ _ g _ _ hHg
  unfold HandlerVon at hHg
  rw [h] at hHg
  exact Bool.noConfusion hHg

#print axioms Gabbro.Grammatik.Zielsatz.merkInvG_lauf
#print axioms Gabbro.Grammatik.Zielsatz.anSperre_gleich
#print axioms Gabbro.Grammatik.Zielsatz.anSperre_nicht_fertig
#print axioms Gabbro.Grammatik.Zielsatz.anSperre_ende_falsch
#print axioms Gabbro.Grammatik.Zielsatz.anSperre_start_falsch
#print axioms Gabbro.Grammatik.Zielsatz.sperre_merkmal
#print axioms Gabbro.Grammatik.Zielsatz.handler_sperre_maskiert
#print axioms Gabbro.Grammatik.Zielsatz.kernHaltG_gilt
#print axioms Gabbro.Grammatik.Zielsatz.mE_maskM
#print axioms Gabbro.Grammatik.Zielsatz.merkAbg_maskM
#print axioms Gabbro.Grammatik.Zielsatz.rufStartG_kopf_f
#print axioms Gabbro.Grammatik.Zielsatz.merkInvG_start
#print axioms Gabbro.Grammatik.Zielsatz.kernHaltE_aus
#print axioms Gabbro.Grammatik.Zielsatz.kernHaltE_ohne_handler

end Gabbro.Grammatik.Zielsatz
