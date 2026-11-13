/-
  File:      stage0/Stage0/Senke/Bild/Lauf.lean
  Subject:   Prefixes of an image run (image theorem, piece T1). The correctness theorems of Stage 0 are
             existential: from a state, SOME run reaches the outcome (`Star`). A run of the image answers system
             calls through the kernel relation and floating requests through the CPU relation, so it is not unique
             in general. A step whose request tree is answered by the memory alone (`RunM`) is unique
             (`RunM.det`). Hence a run of memory-only steps (`StarM`) that starts where an existential run starts
             either is still in front of that run's end or has passed it (`StarM.weiche`), and it never steps past
             a system call (`StarM.vor_halt`). This is what lets a big-step outcome speak about every prefix.
-/
module
public import Runner.IR.Seq
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Runner Runner.IR

variable [Kern]

/-- A request tree answered by the memory alone: no system call, no floating request. -/
inductive RunM : Res T → Mem → T → Mem → Prop
  | next {t : T} {m : Mem} : RunM (.next t) m t m
  | ask {o : Op} {k : Ans → Res T} {m m' m'' : Mem} {a : Ans} {t : T} :
      memAns m o = some (a, m') → RunM (k a) m' t m'' → RunM (.ask o k) m t m''

/-- A memory-only run is a run. -/
theorem RunM.run {r : Res T} {m m1 : Mem} {t : T} (h : RunM r m t m1) : Run r m t m1 := by
  induction h with
  | next => exact .next
  | ask ho _ ih => exact .ask ho ih

/-- **A memory-only step is the only step**: every run of the same request tree from the same memory ends in the
    same state and memory. -/
theorem RunM.det {r : Res T} {m m1 : Mem} {t : T} (h : RunM r m t m1) :
    ∀ {t' : T} {m2 : Mem}, Run r m t' m2 → t' = t ∧ m2 = m1 := by
  induction h with
  | next =>
    intro t' m2 h'
    cases h'
    exact ⟨rfl, rfl⟩
  | ask ho _ ih =>
    intro t' m2 h'
    cases h' with
    | ask ho' hk' =>
      rw [ho] at ho'
      simp only [Option.some.injEq, Prod.mk.injEq] at ho'
      obtain ⟨rfl, rfl⟩ := ho'
      exact ih hk'
    | sys _ _ => simp only [memAns, reduceCtorEq] at ho
    | fp _ _ => simp only [memAns, reduceCtorEq] at ho

/-- A memory-only step never reaches a system call. -/
theorem RunM.nicht_runTo {r : Res T} {m m1 : Mem} {t : T} (h : RunM r m t m1) :
    ∀ {q : Req}, RunTo r m q → False := by
  induction h with
  | next =>
    intro q hq
    cases hq
  | ask ho _ ih =>
    intro q hq
    cases hq with
    | sys => simp only [memAns, reduceCtorEq] at ho
    | ask ho' hk =>
      rw [ho] at ho'
      simp only [Option.some.injEq, Prod.mk.injEq] at ho'
      obtain ⟨rfl, rfl⟩ := ho'
      exact ih hk
    | fp _ _ => simp only [memAns, reduceCtorEq] at ho

/-- `n` instructions, each answered by the memory alone. -/
inductive StarM : Nat → T → Mem → T → Mem → Prop
  | refl (t : T) (m : Mem) : StarM 0 t m t m
  | next {n : Nat} {t t' t'' : T} {m m' m'' : Mem} :
      RunM (step t) m t' m' → StarM n t' m' t'' m'' → StarM (n + 1) t m t'' m''

theorem StarM.star {n : Nat} {t t' : T} {m m' : Mem} (h : StarM n t m t' m') : Star t m t' m' := by
  induction h with
  | refl => exact .refl _ _
  | next hs _ ih => exact .next hs.run ih

/-- **The fork**: a memory-only run of `n` steps from where some run starts is either still in front of that run's
    end (the end is reachable from it) or has passed the end (it continues the end by memory-only steps). -/
theorem StarM.weiche {n : Nat} {t t1 : T} {m m1 : Mem} (h : StarM n t m t1 m1) :
    ∀ {t2 : T} {m2 : Mem}, Star t m t2 m2 → Star t1 m1 t2 m2 ∨ ∃ k, StarM k t2 m2 t1 m1 := by
  induction h with
  | refl => intro t2 m2 h'; exact Or.inl h'
  | next hs hrest ih =>
    intro t2 m2 h'
    cases h' with
    | refl => exact Or.inr ⟨_, StarM.next hs hrest⟩
    | next hr hrest' =>
      obtain ⟨rfl, rfl⟩ := hs.det hr
      exact ih hrest'

/-- A memory-only run from a state that asks the kernel stays there. -/
theorem StarM.halt {n : Nat} {t t1 : T} {m m1 : Mem} {q : Req} (h : StarM n t m t1 m1) (hq : StopAt t m q) :
    t1 = t ∧ m1 = m := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | next hs _ => exact (hs.nicht_runTo hq).elim

/-- **A memory-only run never passes a stop**: from where a run reaches a system call, every memory-only prefix
    lies in front of it. -/
theorem StarM.vor_halt {n : Nat} {t t1 ts : T} {m m1 ms : Mem} {q : Req} (h : StarM n t m t1 m1)
    (hs : Star t m ts ms) (hq : StopAt ts ms q) : Star t1 m1 ts ms := by
  rcases h.weiche hs with h1 | ⟨k, hk⟩
  · exact h1
  · obtain ⟨rfl, rfl⟩ := hk.halt hq
    exact .refl _ _

end Gabbro.Stage0.Senke.BildLauf
