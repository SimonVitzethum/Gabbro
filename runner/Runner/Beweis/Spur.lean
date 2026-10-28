import Runner.Beweis.Schritt

/-! # `runner_ok`: every run of the runner is a run of `S0IR`

A run is observed by its exchanges with the kernel (request and answer) and how it ends so far: still running,
faulted, or -- on the x86-64 model only -- at a step the model does not describe.

* `XTr A x l e n`: the model, started in `x`, performs the exchanges `l` in `n` steps and ends in `e`, where every
  answer satisfies the assumption `A` on the kernel.
* `ITr s l e`: the IR, started in `s`, performs `l` and ends in `e`; the IR takes every answer.

`runner_ok`: from related states, every observation of the model under the assumption that the kernel keeps the
runner's code and table (`ImgInv`) is an observation of the IR, and the model never reaches an undescribed step. -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog

abbrev Ev := Req × Resp

inductive Ende
  | lauf
  | fault
  | unk
  deriving DecidableEq

inductive XTr (A : Mem → Resp → Prop) : X → List Ev → Ende → Nat → Prop
  | nil (x : X) : XTr A x [] .lauf 0
  | fault {x : X} : step x = .fault → XTr A x [] .fault 1
  | unk {x : X} : step x = .unk → XTr A x [] .unk 1
  | next {x y : X} {l : List Ev} {e : Ende} {n : Nat} : step x = .next y → XTr A y l e n → XTr A x l e (n + 1)
  | sys {x y : X} {q : Req} {k : Resp → Option X} {r : Resp} {l : List Ev} {e : Ende} {n : Nat} :
      step x = .sys q k → A x.mem r → k r = some y → XTr A y l e n → XTr A x ((q, r) :: l) e (n + 1)

inductive ITr : IR.S → List Ev → Ende → Prop
  | nil (s : IR.S) : ITr s [] .lauf
  | fault {s : IR.S} : IR.step s = .fault → ITr s [] .fault
  | next {s t : IR.S} {l : List Ev} {e : Ende} : IR.step s = .next t → ITr t l e → ITr s l e
  | sys {s t : IR.S} {q : Req} {k : Resp → Option IR.S} {r : Resp} {l : List Ev} {e : Ende} :
      IR.step s = .sys q k → k r = some t → ITr t l e → ITr s ((q, r) :: l) e
  /-- The answer leads to a fault: observed as running or as faulted. -/
  | sysNone {s : IR.S} {q : Req} {k : Resp → Option IR.S} {r : Resp} {e : Ende} :
      IR.step s = .sys q k → k r = none → e ≠ .unk → ITr s [(q, r)] e

/-! ## Walking a trace along deterministic steps -/

theorem tr_next {A : Mem → Resp → Prop} {x y : X} {l : List Ev} {e : Ende} {n : Nat} (hs : step x = .next y)
    (h : XTr A x l e n) : (l = [] ∧ e = .lauf) ∨ ∃ m, n = m + 1 ∧ XTr A y l e m := by
  cases h with
  | nil => exact .inl ⟨rfl, rfl⟩
  | fault h' => rw [hs] at h'; cases h'
  | unk h' => rw [hs] at h'; cases h'
  | next h' ht => rw [hs] at h'; cases h'; exact .inr ⟨_, rfl, ht⟩
  | sys h' => rw [hs] at h'; cases h'

theorem tr_star {A : Mem → Resp → Prop} {x z : X} (hs : Star x z) :
    ∀ {l : List Ev} {e : Ende} {n : Nat}, XTr A x l e n → (l = [] ∧ e = .lauf) ∨ ∃ m ≤ n, XTr A z l e m := by
  induction hs with
  | refl x => intro l e n h; exact .inr ⟨n, Nat.le_refl n, h⟩
  | step h1 _ ih =>
    intro l e n h
    rcases tr_next h1 h with h | ⟨m, rfl, hm⟩
    · exact .inl h
    · rcases ih hm with h | ⟨m', hle, hm'⟩
      · exact .inl h
      · exact .inr ⟨m', Nat.le_succ_of_le hle, hm'⟩

theorem tr_plus {A : Mem → Resp → Prop} {x z : X} (hs : Plus x z) {l : List Ev} {e : Ende} {n : Nat}
    (h : XTr A x l e n) : (l = [] ∧ e = .lauf) ∨ ∃ m < n, XTr A z l e m := by
  obtain ⟨y, h1, h2⟩ := hs
  rcases tr_next h1 h with h | ⟨m, rfl, hm⟩
  · exact .inl h
  · rcases tr_star h2 hm with h | ⟨m', hle, hm'⟩
    · exact .inl h
    · exact .inr ⟨m', Nat.lt_succ_of_le hle, hm'⟩

/-- A trace from a state that faults next is empty. -/
theorem tr_fault {A : Mem → Resp → Prop} {x : X} {l : List Ev} {e : Ende} {n : Nat} (hs : step x = .fault)
    (h : XTr A x l e n) : l = [] ∧ e ≠ .unk := by
  cases h with
  | nil => exact ⟨rfl, by decide⟩
  | fault => exact ⟨rfl, by decide⟩
  | unk h' => rw [hs] at h'; cases h'
  | next h' => rw [hs] at h'; cases h'
  | sys h' => rw [hs] at h'; cases h'

theorem tr_reach_fault {A : Mem → Resp → Prop} {x : X} {l : List Ev} {e : Ende} {n : Nat}
    (hr : Reach x .fault) (h : XTr A x l e n) : l = [] ∧ e ≠ .unk := by
  obtain ⟨w, hw, hs⟩ := hr
  rcases tr_star hw h with ⟨rfl, rfl⟩ | ⟨m, _, hm⟩
  · exact ⟨rfl, by decide⟩
  · exact tr_fault hs hm

/-! ## The theorem -/

/-- The kernel keeps the runner: the named assumption on every answer. -/
def KeepsRunner (L : Lay) (_ : Mem) (r : Resp) : Prop := ImgInv L r.mem

theorem runner_ok {L : Lay} : ∀ (n : Nat) {s : IR.S} {x : X} {l : List Ev} {e : Ende},
    R L s x → XTr (KeepsRunner L) x l e n → e ≠ .unk ∧ ITr s l e := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro s x l e hR h
  have hs := step_ok hR
  cases hst : IR.step s with
  | next s' =>
    rw [hst] at hs
    obtain ⟨z, hz, hRz⟩ := hs
    rcases tr_plus hz h with ⟨rfl, rfl⟩ | ⟨m, hm, hmz⟩
    · exact ⟨by decide, .nil s⟩
    · obtain ⟨he, hi⟩ := ih m hm hRz hmz
      exact ⟨he, .next hst hi⟩
  | fault =>
    rw [hst] at hs
    obtain ⟨rfl, he⟩ := tr_reach_fault hs h
    refine ⟨he, ?_⟩
    cases e with
    | lauf => exact .nil s
    | fault => exact .fault hst
    | unk => exact absurd rfl he
  | unk => rw [hst] at hs; exact hs.elim
  | sys q k =>
    rw [hst] at hs
    obtain ⟨w, k', hw, hsw, hk⟩ := hs
    rcases tr_star hw h with ⟨rfl, rfl⟩ | ⟨m, hm, hmw⟩
    · exact ⟨by decide, .nil s⟩
    · cases hmw with
      | nil => exact ⟨by decide, .nil s⟩
      | fault h' => rw [hsw] at h'; cases h'
      | unk h' => rw [hsw] at h'; cases h'
      | next h' => rw [hsw] at h'; cases h'
      | @sys _ y q' k'' r l' _ m' h' hA hky ht =>
        rw [hsw] at h'
        cases h'
        obtain ⟨z', hz', hm2⟩ := hk r hA
        rw [hz'] at hky
        cases hky
        cases hkr : k r with
        | none =>
          rw [hkr] at hm2
          obtain ⟨rfl, he⟩ := tr_reach_fault hm2 ht
          exact ⟨he, .sysNone hst hkr he⟩
        | some s'' =>
          rw [hkr] at hm2
          obtain ⟨w', hw', hRw⟩ := hm2
          rcases tr_star hw' ht with ⟨rfl, rfl⟩ | ⟨m'', hle, hm''⟩
          · exact ⟨by decide, .sys hst hkr (.nil s'')⟩
          · obtain ⟨he, hi⟩ := ih m'' (by omega) hRw hm''
            exact ⟨he, .sys hst hkr hi⟩

end Runner.Beweis
