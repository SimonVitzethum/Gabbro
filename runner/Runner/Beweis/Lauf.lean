import Runner.X86.DecEnc
import Runner.X86.Step

/-! # Straight-line code of the x86-64 model, on request trees

* `Bytes C a l`, `Code C a is`: the bytes `l`, the encoded instructions `is` lie at `a` in the runner's code `C`
  (which never changes, so these are facts about `C`, not about a state).
* `step_code`: where `Code` holds at `rip`, the model executes the instruction placed there (`decode_enc`).
* `runL is x`: the request tree of executing `is` one after the other; `runL_rip`: every state it ends in lies
  after the list when no instruction transfers control. -/

namespace Runner.Beweis
open Runner.X86

def Bytes (C : W → B) (a : W) (l : List B) : Prop :=
  ∀ j (h : j < l.length), C (a + BitVec.ofNat 64 j) = l[j]

def Code (C : W → B) : W → List Ins → Prop
  | _, [] => True
  | a, i :: is => i.ok = true ∧ Bytes C a (enc i) ∧ Code C (a + BitVec.ofNat 64 (enc i).length) is

def lenOfL (is : List Ins) : Nat := (is.map fun i => (enc i).length).sum

theorem code_prefix {C : W → B} : ∀ {a : W} {is js : List Ins}, Code C a (is ++ js) → Code C a is
  | _, [], _, _ => trivial
  | _, _ :: _, _, ⟨ho, hb, hc⟩ => ⟨ho, hb, code_prefix hc⟩

theorem code_append {C : W → B} : ∀ {a : W} {is js : List Ins},
    Code C a (is ++ js) → Code C (a + BitVec.ofNat 64 (lenOfL is)) js
  | a, [], js, h => by simpa [lenOfL] using h
  | a, i :: is, js, ⟨_, _, hc⟩ => by
    have := code_append (is := is) (js := js) hc
    simp only [lenOfL, List.map_cons, List.sum_cons] at this ⊢
    rwa [BitVec.ofNat_add, ← BitVec.add_assoc]

theorem enc_len_le (i : Ins) : (enc i).length ≤ 15 := by
  cases i <;> simp [enc, memEnc, regEnc, le32]

theorem fetch_eq {C : W → B} {a : W} {l : List B} (h : Bytes C a l) (hl : l.length ≤ 15) :
    ∃ r, fetch C a = l ++ r := by
  refine ⟨(List.range (15 - l.length)).map fun j => C (a + BitVec.ofNat 64 (l.length + j)), ?_⟩
  have e : fetch C a = (List.range (l.length + (15 - l.length))).map
      (fun i => C (a + BitVec.ofNat 64 i)) := by
    simp only [fetch]
    congr 2
    omega
  rw [e, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.ext_getElem (by simp)
  intro j h1 _
  simp only [List.getElem_map, List.getElem_range]
  exact h j (by simpa using h1)

theorem step_code {C : W → B} {x : X} {i : Ins} {is : List Ins} (h : Code C x.rip (i :: is)) :
    step C x = exec i (enc i).length x := by
  obtain ⟨ho, hb, _⟩ := h
  obtain ⟨r, hr⟩ := fetch_eq hb (enc_len_le i)
  simp only [step, hr, decode_enc i ho r]

/-! ## Request trees of straight code -/

def _root_.Runner.Res.bind {σ : Type} : Res σ → (σ → Res σ) → Res σ
  | .next s, f => f s
  | .fault, _ => .fault
  | .unk, _ => .unk
  | .ask o k, f => .ask o fun a => (k a).bind f

@[simp] theorem bind_next {σ : Type} (s : σ) (f : σ → Res σ) : (Res.next s).bind f = f s := rfl
@[simp] theorem bind_fault {σ : Type} (f : σ → Res σ) : (Res.fault).bind f = .fault := rfl
@[simp] theorem bind_unk {σ : Type} (f : σ → Res σ) : (Res.unk).bind f = .unk := rfl
@[simp] theorem bind_ask {σ : Type} (o : Op) (k : Ans → Res σ) (f : σ → Res σ) :
    (Res.ask o k).bind f = .ask o fun a => (k a).bind f := rfl
@[simp] theorem bind_opt {σ α : Type} (o : Option α) (g : α → Res σ) (f : σ → Res σ) :
    (opt o g).bind f = opt o (fun a => (g a).bind f) := by
  cases o <;> rfl

def runL : List Ins → X → Res X
  | [], x => .next x
  | i :: is, x => (exec i (enc i).length x).bind (runL is)

/-- Instructions that fall through to the next one when they continue. -/
def Fall : Ins → Bool
  | .jmp _ | .jcc _ _ | .jmpm _ | .ud2 => false
  | _ => true

/-- Every state a tree ends in satisfies `P`. -/
def Leaves {σ : Type} (P : σ → Prop) : Res σ → Prop
  | .next s => P s
  | .fault | .unk => True
  | .ask _ k => ∀ a, Leaves P (k a)

theorem leaves_bind {σ : Type} {P Q : σ → Prop} {f : σ → Res σ} :
    ∀ {r : Res σ}, Leaves P r → (∀ s, P s → Leaves Q (f s)) → Leaves Q (r.bind f)
  | .next _, h, hf => hf _ h
  | .fault, _, _ => trivial
  | .unk, _, _ => trivial
  | .ask _ _, h, hf => fun a => leaves_bind (h a) hf

theorem set_rip (x : X) (r : Reg) (v : W) : (x.set r v).rip = x.rip := by cases r <;> rfl

theorem aluStep_rip (x : X) (o : Alu) (d : Reg) (b : W) : (aluStep x o d b).rip = x.rip := by
  cases o <;> simp [aluStep, X.cmpf, X.nof, set_rip]

theorem leaves_opt {σ α : Type} {P : σ → Prop} {o : Option α} {g : α → Res σ} (h : ∀ a, Leaves P (g a)) :
    Leaves P (opt o g) := by
  cases o
  · trivial
  · exact h _

/-- A falling-through instruction ends after itself, after every answer. -/
theorem exec_rip {i : Ins} (hf : Fall i = true) (n : Nat) (x : X) :
    Leaves (fun y => y.rip = x.rip + BitVec.ofNat 64 n) (exec i n x) := by
  cases i with
  | ld | ldsx | ldzx | cmpxchg =>
    simp only [exec, rd64, rd32, rd8, cas, Leaves]
    intro _
    apply leaves_opt
    intro _
    simp only [Leaves, set_rip, X.cmpf]
  | st =>
    simp only [exec, wr64, Leaves]
    intro _
    apply leaves_opt
    intro _
    simp only [Leaves]
  | syscall =>
    simp only [exec, Leaves]
    intro _
    apply leaves_opt
    intro _
    simp only [Leaves, X.nof]
  | udiv =>
    simp only [exec, opt]
    split
    · trivial
    · simp only [Leaves, set_rip, X.nof]
  | idiv =>
    simp only [exec]
    split
    · trivial
    · split
      · trivial
      · simp only [Leaves, set_rip, X.nof]
  | set c d =>
    simp only [exec]
    split
    · trivial
    · simp only [Leaves, set_rip]
  | jmp | jcc | jmpm | ud2 => exact absurd hf Bool.false_ne_true
  | alu | alui => simp only [exec, Leaves, aluStep_rip]
  | mov | movi | zx8 | lea | imul | cqo | shl | shr => simp only [exec, Leaves, set_rip, X.nof]

theorem runL_rip : ∀ (is : List Ins) (x : X), (∀ i ∈ is, Fall i = true) →
    Leaves (fun y => y.rip = x.rip + BitVec.ofNat 64 (lenOfL is)) (runL is x)
  | [], x, _ => by simp [runL, Leaves, lenOfL]
  | i :: is, x, hf => by
    simp only [runL]
    apply leaves_bind (exec_rip (hf i (List.mem_cons_self ..)) _ x)
    intro y hy
    have := runL_rip is y (fun j hj => hf j (List.mem_cons_of_mem _ hj))
    simp only [hy, lenOfL, List.map_cons, List.sum_cons, BitVec.ofNat_add, BitVec.add_assoc] at this ⊢
    exact this

end Runner.Beweis
