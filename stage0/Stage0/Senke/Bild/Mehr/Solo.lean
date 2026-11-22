/-
  File:      stage0/Stage0/Senke/Bild/Mehr/Solo.lean
  Subject:   The solo run of one thread (multi-thread image theorem, package MT1). The machine of threads runs an
             instruction request by request (`Runner.Mach.Tr` with `actI`): a thread at `.next t` starts the
             instruction (its state becomes the request tree `step t`), then each request is answered on its own.
             `RunP` is a request tree answered by the memory part of the way; `SoloLauf tb mb r m` says that the
             thread's state `r` with the memory `m` is where its OWN memory-only run from the boundary `(tb, mb)`
             stands: whole instructions (`StarM`, the object of the single-thread chain), then part of the current
             one. The two steps of a thread answered by the memory keep it (`SoloLauf.priv`, `SoloLauf.ask`), and at
             an instruction boundary it is a `StarM` run (`SoloLauf.starM`), so `korrespondenz_lauf` applies.
-/
module
public import Stage0.Senke.Bild.Lauf
public import Stage0.Senke.Bild.Mehr.Lokal
public import Runner.Mach.Maschine
@[expose] public section

namespace Gabbro.Stage0.Senke.BildMehr

open Runner Runner.IR Gabbro.Stage0.Senke.BildLauf

set_option linter.unusedSectionVars false

variable [Kern]

/-- A request tree answered by the memory alone, part of the way: from `r` at `m` to the rest `r'` at `m'`. -/
inductive RunP : Res T → Mem → Res T → Mem → Prop
  | refl (r : Res T) (m : Mem) : RunP r m r m
  | ask {o : Op} {k : Ans → Res T} {m m' m'' : Mem} {a : Ans} {r : Res T} :
      memAns m o = some (a, m') → RunP (k a) m' r m'' → RunP (.ask o k) m r m''

/-- One more answered request at the end of a partial run. -/
theorem runP_snoc' {r r' : Res T} {m m1 : Mem} (h : RunP r m r' m1) :
    ∀ {o : Op} {k : Ans → Res T}, r' = .ask o k → ∀ {a : Ans} {m2 : Mem}, memAns m1 o = some (a, m2) →
      RunP r m (k a) m2 := by
  induction h with
  | refl r0 m0 =>
    intro o k e a m2 ho
    subst e
    exact .ask ho (.refl _ _)
  | ask hm _ ih =>
    intro o k e a m2 ho
    exact .ask hm (ih e ho)

theorem runP_snoc {r : Res T} {m m1 : Mem} {o : Op} {k : Ans → Res T} (h : RunP r m (.ask o k) m1) {a : Ans}
    {m2 : Mem} (ho : memAns m1 o = some (a, m2)) : RunP r m (k a) m2 :=
  runP_snoc' h rfl ho

/-- Every reachable point within a memory-only instruction can finish
    at the same next pointer and memory as the whole instruction. -/
theorem RunP.remaining {start current : Res T} {before now : Mem}
    (part : RunP start before current now) :
    ∀ {next : T} {after : Mem}, RunM start before next after → RunM current now next after := by
  induction part with
  | refl => exact fun whole => whole
  | ask answered _ ih =>
    intro next after whole
    cases whole with
    | ask same later =>
      rw [answered] at same
      simp only [Option.some.injEq, Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact ih later

/-- A partial execution of a proved memory-only instruction can wait
    only on a memory request, or be at the exact next instruction. -/
theorem RunP.control_of_runM {start current : Res T} {before now after : Mem} {next : T}
    (part : RunP start before current now) (whole : RunM start before next after) :
    (current = .next next ∧ now = after) ∨
      ∃ request resume, current = .ask request resume ∧ request.special = false := by
  cases part.remaining whole with
  | next => exact Or.inl ⟨rfl, rfl⟩
  | @ask request resume _ _ _ _ _ answered _ =>
    refine Or.inr ⟨request, resume, rfl, ?_⟩
    cases request with
    | rd => rfl
    | wr => rfl
    | cas => rfl
    | sys => cases answered
    | fp => cases answered

/-- A partial run that has reached the end of the tree is a memory-only step. -/
theorem runP_runM {r r' : Res T} {m m1 : Mem} (h : RunP r m r' m1) : ∀ {t : T}, r' = .next t → RunM r m t m1 := by
  induction h with
  | refl r0 m0 =>
    intro t e
    subst e
    exact .next
  | ask hm _ ih =>
    intro t e
    exact .ask hm (ih e)

/-- One more instruction at the end of a memory-only run. -/
theorem starM_snoc {n : Nat} {t t1 : T} {m m1 : Mem} (h : StarM n t m t1 m1) :
    ∀ {t2 : T} {m2 : Mem}, RunM (step t1) m1 t2 m2 → StarM (n + 1) t m t2 m2 := by
  induction h with
  | refl t0 m0 =>
    intro t2 m2 hs
    exact .next hs (.refl _ _)
  | next h1 _ ih =>
    intro t2 m2 hs
    exact .next h1 (ih hs)

/-- **The solo run of one thread**: from the boundary `(tb, mb)`, whole instructions answered by the memory alone,
    then the current instruction part of the way; `r` is the thread's state as the machine of threads holds it. -/
def SoloLauf (tb : T) (mb : Mem) (r : Res T) (m : Mem) : Prop :=
  ∃ (n : Nat) (t0 : T) (m0 : Mem), StarM n tb mb t0 m0 ∧ ((r = .next t0 ∧ m = m0) ∨ RunP (step t0) m0 r m)

theorem soloLauf_start (tb : T) (mb : Mem) : SoloLauf tb mb (.next tb) mb :=
  ⟨0, tb, mb, .refl _ _, Or.inl ⟨rfl, rfl⟩⟩

/-- **The thread starts an instruction** (`.next t` becomes `step t`, no memory touched). -/
theorem SoloLauf.priv {tb t : T} {mb m : Mem} (h : SoloLauf tb mb (.next t) m) : SoloLauf tb mb (step t) m := by
  obtain ⟨n, t0, m0, hs, h⟩ := h
  rcases h with ⟨e, rfl⟩ | hp
  · cases e
    exact ⟨n, _, _, hs, Or.inr (.refl _ _)⟩
  · exact ⟨n + 1, _, _, starM_snoc hs (runP_runM hp rfl), Or.inr (.refl _ _)⟩

/-- **The memory answers the thread's request.** -/
theorem SoloLauf.ask {tb : T} {mb m m' : Mem} {o : Op} {k : Ans → Res T} {a : Ans}
    (h : SoloLauf tb mb (.ask o k) m) (ho : memAns m o = some (a, m')) : SoloLauf tb mb (k a) m' := by
  obtain ⟨n, t0, m0, hs, h⟩ := h
  rcases h with ⟨e, -⟩ | hp
  · cases e
  · exact ⟨n, t0, m0, hs, Or.inr (runP_snoc hp ho)⟩

/-- **At an instruction boundary the solo run is a memory-only run** of whole instructions. -/
theorem SoloLauf.starM {tb t : T} {mb m : Mem} (h : SoloLauf tb mb (.next t) m) : ∃ n, StarM n tb mb t m := by
  obtain ⟨n, t0, m0, hs, h⟩ := h
  rcases h with ⟨e, rfl⟩ | hp
  · cases e
    exact ⟨n, hs⟩
  · exact ⟨n + 1, starM_snoc hs (runP_runM hp rfl)⟩

end Gabbro.Stage0.Senke.BildMehr
