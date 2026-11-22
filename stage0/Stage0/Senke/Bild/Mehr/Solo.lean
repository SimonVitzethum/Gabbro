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
public import Stage0.Senke.Bild.Mehr.Blind
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

/-- A reference can mask writes to shared read-only bytes. It agrees
    with the actual memory on the permissions that can affect it. -/
def MaskedAgreement (reads writes : W → Prop) (reference actual : Mem) : Prop :=
  (∀ byte, reads byte → reference.b byte = actual.b byte ∧ reference.rd byte = actual.rd byte) ∧
  (∀ byte, writes byte → reference.wr byte = actual.wr byte)

/-- A successful reference instruction in memory restricted to the
    declared regions determines every actual request of that instruction.
    Memory outside its write region is preserved. -/
theorem RunM.replay_on {r : Res T} {reference finish : Mem} {target : T}
    {reads writes : W → Prop}
    (ran : RunM r reference target finish) (tree : Blind r)
    (readable : ∀ byte, reference.rd byte = true → reads byte)
    (writable : ∀ byte, reference.wr byte = true → reads byte ∧ writes byte)
    {actual : Mem} (agrees : MaskedAgreement reads writes reference actual) :
    ∃ result, RunM r actual target result ∧ MaskedAgreement reads writes finish result ∧
      (∀ byte, ¬ writes byte → GleichAt result actual byte) ∧
      ∀ {current : Mem} {request : Op} {resume : Ans → Res T},
        RunP r actual (.ask request resume) current →
          (∀ byte, fussOp request byte → reads byte) ∧
          (schreibtOp request = true → ∀ byte, fussOp request byte → writes byte) := by
  induction ran generalizing actual with
  | next =>
    refine ⟨actual, .next, agrees, fun byte _ => GleichAt.refl _ byte, ?_⟩
    intro current request resume partialRun
    cases partialRun
  | @ask op k before middle after answer dest answered rest ih =>
    cases answer with
    | none =>
      rw [tree.missing] at rest
      cases rest
    | some words =>
      have confined := memAns_confined readable writable answered
      obtain ⟨advanced, sameAnswer, sameTouched⟩ :=
        memAns_replay (fun byte touched =>
          ⟨(agrees.1 byte (confined.1 byte touched)).1, (agrees.1 byte (confined.1 byte touched)).2,
            fun writesRequest => agrees.2 byte (confined.2 writesRequest byte touched)⟩) answered
      have referenceStable := memAns_nurIn answered
      have actualStable := memAns_nurIn sameAnswer
      have sameRegion : MaskedAgreement reads writes middle advanced := by
        refine ⟨?_, ?_⟩
        · intro byte included
          by_cases touched : fussOp op byte
          · exact sameTouched byte touched
          · have b := (referenceStable.gleichAt touched).1
            exact ⟨b.trans ((agrees.1 byte included).1.trans (actualStable.gleichAt touched).1.symm),
              (congrFun referenceStable.rd byte).trans
                ((agrees.1 byte included).2.trans (congrFun actualStable.rd byte).symm)⟩
        · intro byte included
          exact (congrFun referenceStable.wr byte).trans
            ((agrees.2 byte included).trans (congrFun actualStable.wr byte).symm)
      obtain ⟨result, replay, sameResult, otherBytes, pending⟩ := ih (tree.weiter _)
        (fun byte permission => readable byte (by simpa only [referenceStable.rd] using permission))
        (fun byte permission => writable byte (by simpa only [referenceStable.wr] using permission)) sameRegion
      refine ⟨result, .ask sameAnswer replay, sameResult, ?_, ?_⟩
      · intro byte outside
        exact (otherBytes byte outside).trans (memAns_aussen sameAnswer confined.2 byte outside)
      · intro current request resume partialRun
        cases partialRun with
        | refl => exact confined
        | ask wasAnswered leftover =>
          rw [sameAnswer] at wasAnswered
          simp only [Option.some.injEq, Prod.mk.injEq] at wasAnswered
          obtain ⟨rfl, rfl⟩ := wasAnswered
          exact pending leftover

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

private theorem RunM.permissions {r : Res T} {before after : Mem} {next : T}
    (run : RunM r before next after) : after.rd = before.rd ∧ after.wr = before.wr := by
  induction run with
  | next => exact ⟨rfl, rfl⟩
  | ask answered _ ih =>
    have stable := memAns_nurIn answered
    exact ⟨ih.1.trans stable.rd, ih.2.trans stable.wr⟩

private theorem RunP.permissions {r r' : Res T} {before after : Mem}
    (run : RunP r before r' after) : after.rd = before.rd ∧ after.wr = before.wr := by
  induction run with
  | refl => exact ⟨rfl, rfl⟩
  | ask answered _ ih =>
    have stable := memAns_nurIn answered
    exact ⟨ih.1.trans stable.rd, ih.2.trans stable.wr⟩

/-- The common memory permissions stay fixed through complete and
    partially executed instructions, independently of their number. -/
theorem SoloLauf.permissions {tb : T} {mb m : Mem} {r : Res T}
    (run : SoloLauf tb mb r m) : m.rd = mb.rd ∧ m.wr = mb.wr := by
  obtain ⟨_, _, _, complete, rest⟩ := run
  have stable {n : Nat} {start finish : T} {before after : Mem}
      (path : StarM n start before finish after) : after.rd = before.rd ∧ after.wr = before.wr := by
    induction path with
    | refl => exact ⟨rfl, rfl⟩
    | next ran _ ih =>
      obtain ⟨rd, wr⟩ := RunM.permissions ran
      exact ⟨ih.1.trans rd, ih.2.trans wr⟩
  obtain ⟨rd, wr⟩ := stable complete
  rcases rest with ⟨_, rfl⟩ | current
  · exact ⟨rd, wr⟩
  · exact ⟨current.permissions.1.trans rd, current.permissions.2.trans wr⟩

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
