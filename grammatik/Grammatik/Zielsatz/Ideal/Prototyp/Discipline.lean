/-
  File:      Grammatik/Zielsatz/Ideal/Prototyp/Discipline.lean
  Subject:   PROTOTYPE of S7: the static discipline of the fragment (race freedom, lock discipline, mask
             discipline, the DMA typestate) and the generic REPLAY of a unit against its recorded answers.

  `Disc P` is the premise of the refinement theorem. It is the miniature of the race and lock legs of the real
  model: every plain access in a unit touches only the carriers its unit holds -- the locations of its lock, the
  locations of the mask (only thread 0 and the handler), and the owned locations of its thread that are not lent
  at that point of the program (the DMA typestate `lend`/`takeBack` is tracked along the program text).
  `Replay K body rest pa ρ₀ mI ρ mS` is the idea of `ZielInvSA` reduced to one unit: the implementation has run the
  prefix `done` of `body` (`body = done ++ rest`), and running `done` in the IDEAL memory `mI` from the unit's
  start registers `ρ₀` with the answers `pa` recorded so far gives the implementation's registers and agrees with
  the implementation's memory on the carriers `K` of the unit.
-/
module

public import Grammatik.Zielsatz.Ideal.Prototyp.Ideal

@[expose] public section

namespace Gabbro.Grammatik.Zielsatz.Ideal.Prototyp

/-- The carriers of a lock section of thread `t` holding lock `k` while the buffers `L` are lent. -/
def KLk (P : Prog) (t : Fin 2) (k : Nat) (L : Nat → Bool) (l : Nat) : Prop :=
  P.prot l = .lock k ∨ (P.prot l = .own t ∧ L l = false)

/-- The carriers of a masked section of thread `t` while the buffers `L` are lent. -/
def KMk (P : Prog) (t : Fin 2) (L : Nat → Bool) (l : Nat) : Prop :=
  P.prot l = .irq ∨ (P.prot l = .own t ∧ L l = false)

/-- The carriers of the handler. -/
def KIrq (P : Prog) (l : Nat) : Prop := P.prot l = .irq

/-- A plain operation touches only carriers in `K`. -/
def OpOk (K : Nat → Prop) : Op → Prop
  | .set _ _ => True
  | .load _ x => K x
  | .store x _ => K x
  | .dev _ _ => True

/-- A body touches only carriers in `K`. -/
def BodyOk (K : Nat → Prop) (ops : List Op) : Prop := ∀ op ∈ ops, OpOk K op

/-- The discipline of a thread program, with the DMA typestate `L` along the text. -/
def ProgOk (P : Prog) (t : Fin 2) : (Nat → Bool) → List Seg → Prop
  | _, [] => True
  | L, .lock k body :: us => BodyOk (KLk P t k L) body ∧ ProgOk P t L us
  | L, .masked body :: us => t = 0 ∧ BodyOk (KMk P t L) body ∧ ProgOk P t L us
  | L, .atom _ _ :: us => ProgOk P t L us
  | L, .lend x :: us => P.prot x = .own t ∧ ProgOk P t (upd L x true) us
  | L, .takeBack x :: us => P.prot x = .own t ∧ ProgOk P t (upd L x false) us
  | L, .set _ _ :: us => ProgOk P t L us

/-- **The premise: a race-free, lock- and mask-disciplined fragment program with the DMA typestate.** -/
def Disc (P : Prog) : Prop := (∀ t, ProgOk P t (fun _ => false) (P.thread t)) ∧ BodyOk (KIrq P) P.handler

/-! ## Frames: a body only reads and writes its carriers -/

/-- Two memories agree on `K`. -/
def Agree (K : Nat → Prop) (m m' : Mem) : Prop := ∀ l, K l → m l = m' l

theorem opStep_frame {K : Nat → Prop} {op : Op} {a : Option Int} {ρ ρ' : Regs} {m₁ m₁' m₂ : Mem}
    (hok : OpOk K op) (h : opStep op a (ρ, m₁) = some (ρ', m₁')) (hA : Agree K m₁ m₂) :
    ∃ m₂', opStep op a (ρ, m₂) = some (ρ', m₂') ∧ Agree K m₁' m₂' ∧ (∀ l, ¬ K l → m₂' l = m₂ l) ∧
      (∀ l, ¬ K l → m₁' l = m₁ l) := by
  cases op <;> cases a <;> simp only [opStep, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨m₂, rfl, hA, fun _ _ => rfl, fun _ _ => rfl⟩
  · obtain ⟨rfl, rfl⟩ := h
    refine ⟨m₂, ?_, hA, fun _ _ => rfl, fun _ _ => rfl⟩
    simp only [opStep, hA _ hok]
  · obtain ⟨rfl, rfl⟩ := h
    refine ⟨_, rfl, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩
    · simp only [upd_apply]; split
      · rfl
      · exact hA l hl
    · simp only [upd_apply]; split
      · next he => subst he; exact absurd hok hl
      · rfl
    · simp only [upd_apply]; split
      · next he => subst he; exact absurd hok hl
      · rfl
  · obtain ⟨rfl, rfl⟩ := h
    exact ⟨m₂, rfl, hA, fun _ _ => rfl, fun _ _ => rfl⟩

theorem execOps_frame {K : Nat → Prop} : ∀ (ops : List Op) (as : List Int) (ρ ρ' : Regs) (m₁ m₁' m₂ : Mem),
    BodyOk K ops → execOps ops as (ρ, m₁) = some (ρ', m₁') → Agree K m₁ m₂ →
    ∃ m₂', execOps ops as (ρ, m₂) = some (ρ', m₂') ∧ Agree K m₁' m₂' ∧ (∀ l, ¬ K l → m₂' l = m₂ l) ∧
      (∀ l, ¬ K l → m₁' l = m₁ l)
  | [], [], ρ, ρ', m₁, m₁', m₂, _, h, hA => by
      simp only [execOps, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨m₂, rfl, hA, fun _ _ => rfl, fun _ _ => rfl⟩
  | [], _ :: _, _, _, _, _, _, _, h, _ => by simp [execOps] at h
  | .dev _ _ :: _, [], _, _, _, _, _, _, h, _ => by simp [execOps] at h
  | .dev r _ :: ops, v :: as, ρ, ρ', m₁, m₁', m₂, hok, h, hA => by
      simp only [execOps] at h ⊢
      exact execOps_frame ops as _ ρ' m₁ m₁' m₂ (fun o ho => hok o (List.mem_cons_of_mem _ ho)) h hA
  | .set r e :: ops, as, ρ, ρ', m₁, m₁', m₂, hok, h, hA => by
      simp only [execOps] at h ⊢
      exact execOps_frame ops as _ ρ' m₁ m₁' m₂ (fun o ho => hok o (List.mem_cons_of_mem _ ho)) h hA
  | .load r x :: ops, as, ρ, ρ', m₁, m₁', m₂, hok, h, hA => by
      simp only [execOps] at h ⊢
      rw [← hA x (hok _ List.mem_cons_self)]
      exact execOps_frame ops as _ ρ' m₁ m₁' m₂ (fun o ho => hok o (List.mem_cons_of_mem _ ho)) h hA
  | .store x e :: ops, as, ρ, ρ', m₁, m₁', m₂, hok, h, hA => by
      simp only [execOps] at h ⊢
      have hx : K x := hok _ List.mem_cons_self
      have hA' : Agree K (upd m₁ x (e.eval ρ)) (upd m₂ x (e.eval ρ)) := fun l hl => by
        simp only [upd_apply]; split
        · rfl
        · exact hA l hl
      obtain ⟨m₂', h₁, h₂, h₃, h₄⟩ :=
        execOps_frame ops as ρ ρ' _ m₁' _ (fun o ho => hok o (List.mem_cons_of_mem _ ho)) h hA'
      have hne : ∀ l, ¬ K l → l ≠ x := fun l hl he => hl (he ▸ hx)
      exact ⟨m₂', h₁, h₂, fun l hl => (h₃ l hl).trans (upd_ne _ _ (hne l hl)),
        fun l hl => (h₄ l hl).trans (upd_ne _ _ (hne l hl))⟩

/-! ## The replay of one unit -/

/-- The implementation is inside a unit with carriers `K`: it ran the prefix `done` of `body`; running `done` in
    the ideal memory from the unit's start registers with the answers recorded so far gives its registers and its
    memory on `K`. -/
def Replay (K : Nat → Prop) (body rest : List Op) (pa : List Int) (ρ₀ : Regs) (mI : Mem) (ρ : Regs) (mS : Mem) :
    Prop :=
  ∃ done, body = done ++ rest ∧ ∃ m', execOps done pa (ρ₀, mI) = some (ρ, m') ∧ Agree K m' mS

/-- The start of a unit. -/
theorem replay_start {K : Nat → Prop} {body : List Op} {ρ : Regs} {mI mS : Mem} (hA : Agree K mI mS) :
    Replay K body body [] ρ mI ρ mS :=
  ⟨[], rfl, mI, by simp [execOps], hA⟩

/-- One operation of the unit in the implementation. -/
theorem replay_step {K : Nat → Prop} {body rest : List Op} {op : Op} {pa : List Int} {ρ₀ ρ ρ' : Regs}
    {mI mS mS' : Mem} {a : Option Int} (hR : Replay K body (op :: rest) pa ρ₀ mI ρ mS) (hok : OpOk K op)
    (h : opStep op a (ρ, mS) = some (ρ', mS')) :
    Replay K body rest (pa ++ a.toList) ρ₀ mI ρ' mS' ∧ ∀ l, ¬ K l → mS' l = mS l := by
  obtain ⟨done, hb, m', he, hA⟩ := hR
  obtain ⟨m'', h₁, h₂, _, h₄⟩ := opStep_frame hok h (fun l hl => (hA l hl).symm)
  refine ⟨⟨done ++ [op], by simp [hb], m'', execOps_snoc done pa _ _ _ op a he h₁,
    fun l hl => (h₂ l hl).symm⟩, h₄⟩

/-- The ideal memory changes outside the carriers. -/
theorem replay_frameI {K : Nat → Prop} {body rest : List Op} {pa : List Int} {ρ₀ ρ : Regs} {mI mI' mS : Mem}
    (hR : Replay K body rest pa ρ₀ mI ρ mS) (hok : BodyOk K body) (hA : Agree K mI mI') :
    Replay K body rest pa ρ₀ mI' ρ mS := by
  obtain ⟨done, hb, m', he, hA'⟩ := hR
  have hokd : BodyOk K done := fun o ho => hok o (by rw [hb]; exact List.mem_append_left _ ho)
  obtain ⟨m₂, h₁, h₂, _, _⟩ := execOps_frame done pa ρ₀ ρ mI m' mI' hokd he hA
  exact ⟨done, hb, m₂, h₁, fun l hl => (h₂ l hl).symm.trans (hA' l hl)⟩

/-- The implementation memory changes outside the carriers. -/
theorem replay_frameS {K : Nat → Prop} {body rest : List Op} {pa : List Int} {ρ₀ ρ : Regs} {mI mS mS' : Mem}
    (hR : Replay K body rest pa ρ₀ mI ρ mS) (hA : Agree K mS mS') : Replay K body rest pa ρ₀ mI ρ mS' := by
  obtain ⟨done, hb, m', he, hA'⟩ := hR
  exact ⟨done, hb, m', he, fun l hl => (hA' l hl).trans (hA l hl)⟩

/-- The carriers can be narrowed (used when the carrier set is stated with other but equal parameters). -/
theorem replay_mono {K K' : Nat → Prop} {body rest : List Op} {pa : List Int} {ρ₀ ρ : Regs} {mI mS : Mem}
    (hR : Replay K body rest pa ρ₀ mI ρ mS) (hK : ∀ l, K' l → K l) : Replay K' body rest pa ρ₀ mI ρ mS := by
  obtain ⟨done, hb, m', he, hA'⟩ := hR
  exact ⟨done, hb, m', he, fun l hl => hA' l (hK l hl)⟩

/-- The end of a unit: the whole body runs in the ideal memory, agrees with the implementation on the carriers
    and leaves every other location of the ideal memory unchanged. -/
theorem replay_done {K : Nat → Prop} {body : List Op} {pa : List Int} {ρ₀ ρ : Regs} {mI mS : Mem}
    (hR : Replay K body [] pa ρ₀ mI ρ mS) (hok : BodyOk K body) :
    ∃ m', execOps body pa (ρ₀, mI) = some (ρ, m') ∧ Agree K m' mS ∧ ∀ l, ¬ K l → m' l = mI l := by
  obtain ⟨done, hb, m', he, hA⟩ := hR
  simp only [List.append_nil] at hb
  subst hb
  obtain ⟨m₂, h₁, _, h₃, _⟩ := execOps_frame body pa ρ₀ ρ mI m' mI hok he (fun _ _ => rfl)
  rw [he] at h₁
  cases h₁
  exact ⟨m', he, hA, h₃⟩

end Gabbro.Grammatik.Zielsatz.Ideal.Prototyp
