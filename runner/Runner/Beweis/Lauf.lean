import Runner.X86.DecEnc
import Runner.X86.Step

/-! # Runs of the x86-64 model: reachability and straight-line code

* `Bytes m a l`: the bytes `l` lie at `a`, readable and not writable. `Code m a is`: the instructions `is` lie one
  after the other from `a` (each encodable).
* `Keeps m m'`: every byte that is not writable in `m` is the same in `m'`, with the same permissions. Every
  step of the model keeps its memory so (a write needs the permission), so code that is not writable stays.
* `Star x y`: the model steps from `x` to `y` without a system call. `Reach x r`: from `x` the model reaches the
  outcome `r`.
* `runL is x` executes `is` one after the other; `reach_runL`: the model really does so when `Code x.mem x.rip is`
  and no instruction but the last transfers control. -/

namespace Runner.Beweis
open Runner.X86

def Bytes (m : Mem) (a : W) (l : List B) : Prop :=
  ∀ j (h : j < l.length), m.b (a + BitVec.ofNat 64 j) = l[j] ∧ m.rd (a + BitVec.ofNat 64 j) = true ∧
    m.wr (a + BitVec.ofNat 64 j) = false

def Code (m : Mem) : W → List Ins → Prop
  | _, [] => True
  | a, i :: is => i.ok = true ∧ Bytes m a (enc i) ∧ Code m (a + BitVec.ofNat 64 (enc i).length) is

def Keeps (m m' : Mem) : Prop :=
  ∀ y, m.wr y = false → m'.b y = m.b y ∧ m'.rd y = m.rd y ∧ m'.wr y = m.wr y

theorem Keeps.refl (m : Mem) : Keeps m m := fun _ _ => ⟨rfl, rfl, rfl⟩

theorem Keeps.trans {m1 m2 m3 : Mem} (h1 : Keeps m1 m2) (h2 : Keeps m2 m3) : Keeps m1 m3 := by
  intro y hy
  obtain ⟨b1, r1, w1⟩ := h1 y hy
  obtain ⟨b2, r2, w2⟩ := h2 y (by rw [w1]; exact hy)
  exact ⟨b2.trans b1, r2.trans r1, w2.trans w1⟩

theorem Bytes.keep {m m' : Mem} {a : W} {l : List B} (hk : Keeps m m') (h : Bytes m a l) : Bytes m' a l := by
  intro j hj
  obtain ⟨hb, hr, hw⟩ := h j hj
  obtain ⟨kb, kr, kw⟩ := hk _ hw
  exact ⟨kb.trans hb, kr.trans hr, kw.trans hw⟩

theorem Code.keep {m m' : Mem} (hk : Keeps m m') : ∀ {a : W} {is : List Ins}, Code m a is → Code m' a is
  | _, [], _ => trivial
  | _, _ :: _, ⟨ho, hb, hc⟩ => ⟨ho, hb.keep hk, Code.keep hk hc⟩

theorem Code.append {m : Mem} : ∀ {a : W} {is js : List Ins},
    Code m a (is ++ js) → Code m (a + BitVec.ofNat 64 ((is.map fun i => (enc i).length).sum)) js
  | a, [], js, h => by simpa using h
  | a, i :: is, js, ⟨_, _, hc⟩ => by
    have := Code.append (is := is) (js := js) hc
    simp only [List.map_cons, List.sum_cons]
    rwa [BitVec.ofNat_add, ← BitVec.add_assoc]

/-! ## Memory operations keep what is not writable -/

theorem all_spec {p : W → Bool} {a : W} : ∀ {n j : Nat}, Mem.all p a n = true → j < n →
    p (a + BitVec.ofNat 64 j) = true
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, j, h, hj => by
    simp only [Mem.all, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact all_spec h.1 hj
    · exact h.2

theorem all_of {p : W → Bool} {a : W} : ∀ {n : Nat}, (∀ j, j < n → p (a + BitVec.ofNat 64 j) = true) →
    Mem.all p a n = true
  | 0, _ => rfl
  | n + 1, h => by
    simp only [Mem.all, Bool.and_eq_true]
    exact ⟨all_of fun j hj => h j (Nat.lt_succ_of_lt hj), h n (Nat.lt_succ_self n)⟩

theorem sub_add_ofNat (a y : W) : a + BitVec.ofNat 64 (y - a).toNat = y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_sub]
  have := a.isLt
  have := y.isLt
  omega

theorem write_keeps {m : Mem} {a : W} {n v : Nat} (h : Mem.all m.wr a n = true) :
    Keeps m (Mem.write m a n v) := by
  intro y hy
  refine ⟨?_, rfl, rfl⟩
  simp only [Mem.write]
  split
  · next hlt =>
    have := all_spec h hlt
    rw [sub_add_ofNat] at this
    rw [hy] at this
    exact absurd this (by decide)
  · rfl

theorem wr64_keeps {m m' : Mem} {a v : W} (h : m.wr64 a v = some m') : Keeps m m' := by
  simp only [Mem.wr64] at h
  split at h
  · next hw => cases h; exact write_keeps hw
  · cases h

theorem cas_keeps {m m' : Mem} {a e n old : W} (h : m.cas a e n = some (old, m')) : Keeps m m' := by
  simp only [Mem.cas] at h
  split at h
  · next hw =>
    simp only [Bool.and_eq_true] at hw
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    split
    · exact write_keeps hw.2
    · exact Keeps.refl m
  · cases h

/-! ## Steps -/

inductive Star : X → X → Prop
  | refl (x : X) : Star x x
  | step {x y z : X} : step x = .next y → Star y z → Star x z

theorem Star.trans {x y z : X} (h1 : Star x y) (h2 : Star y z) : Star x z := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

/-- At least one step. -/
def Plus (x z : X) : Prop := ∃ y, step x = .next y ∧ Star y z

def Reach (x : X) : Res X → Prop
  | .next y => Star x y
  | r => ∃ y, Star x y ∧ step y = r

theorem Reach.cons {x y : X} {r : Res X} (h : step x = .next y) (hr : Reach y r) : Reach x r := by
  cases r with
  | next z => exact Star.step h hr
  | fault | sys | unk => obtain ⟨z, hz, hs⟩ := hr; exact ⟨z, Star.step h hz, hs⟩

theorem Reach.here {x : X} {r : Res X} (h : step x = r) (hn : ∀ y, r ≠ .next y) : Reach x r := by
  cases r with
  | next y => exact absurd rfl (hn y)
  | fault | sys | unk => exact ⟨x, .refl x, h⟩

def _root_.Runner.Res.bind {σ : Type} : Res σ → (σ → Res σ) → Res σ
  | .next s, f => f s
  | .fault, _ => .fault
  | .sys q k, _ => .sys q k
  | .unk, _ => .unk

@[simp] theorem bind_next {σ : Type} (s : σ) (f : σ → Res σ) : (Res.next s).bind f = f s := rfl
@[simp] theorem bind_fault {σ : Type} (f : σ → Res σ) : (Res.fault).bind f = .fault := rfl
@[simp] theorem bind_unk {σ : Type} (f : σ → Res σ) : (Res.unk).bind f = .unk := rfl
@[simp] theorem bind_sys {σ : Type} (q : Req) (k : Resp → Option σ) (f : σ → Res σ) :
    (Res.sys q k).bind f = .sys q k := rfl
@[simp] theorem bind_opt {σ α : Type} (o : Option α) (g : α → Res σ) (f : σ → Res σ) :
    (opt o g).bind f = opt o (fun a => (g a).bind f) := by
  cases o <;> rfl

def runL : List Ins → X → Res X
  | [], x => .next x
  | i :: is, x => (exec i (enc i).length x).bind (runL is)

/-- Instructions that fall through to the next one when they continue. -/
def Fall : Ins → Bool
  | .jmp _ | .jcc _ _ | .jmpm _ | .syscall | .ud2 => false
  | _ => true

theorem set_rip (x : X) (r : Reg) (v : W) : (x.set r v).rip = x.rip := by cases r <;> rfl
theorem set_mem (x : X) (r : Reg) (v : W) : (x.set r v).mem = x.mem := by cases r <;> rfl

theorem aluStep_rip (x : X) (o : Alu) (d : Reg) (b : W) : (aluStep x o d b).rip = x.rip := by
  cases o <;> simp [aluStep, X.cmpf, X.nof, set_rip]

theorem aluStep_mem (x : X) (o : Alu) (d : Reg) (b : W) : (aluStep x o d b).mem = x.mem := by
  cases o <;> simp [aluStep, X.cmpf, X.nof, set_mem]

/-- A continuing step keeps the memory's non-writable bytes and, if it falls through, moves past itself. -/
def NextOk (x y : X) (fall : Bool) (n : Nat) : Prop :=
  Keeps x.mem y.mem ∧ (fall = true → y.rip = x.rip + BitVec.ofNat 64 n)

theorem nextOk_same {x y : X} {fall : Bool} {n : Nat} (hm : y.mem = x.mem)
    (hr : y.rip = x.rip + BitVec.ofNat 64 n) : NextOk x y fall n :=
  ⟨by rw [hm]; exact Keeps.refl _, fun _ => hr⟩

theorem nextOk_jump {x y : X} {n : Nat} (hm : y.mem = x.mem) : NextOk x y false n :=
  ⟨by rw [hm]; exact Keeps.refl _, fun h => absurd h (by decide)⟩

theorem exec_next {i : Ins} {n : Nat} {x y : X} (h : exec i n x = .next y) : NextOk x y (Fall i) n := by
  cases i with
  | ld d m | ldsx d m | ldzx d m =>
    simp only [exec, opt] at h
    split at h <;> simp only [reduceCtorEq, Res.next.injEq] at h
    subst h; exact nextOk_same (set_mem _ _ _) (set_rip _ _ _)
  | st m s =>
    simp only [exec, opt] at h
    split at h <;> simp only [reduceCtorEq, Res.next.injEq] at h
    next ho => subst h; exact ⟨wr64_keeps ho, fun _ => rfl⟩
  | mov d s | movi d v | zx8 d s | lea d m =>
    simp only [exec, Res.next.injEq] at h
    subst h; exact nextOk_same (set_mem _ _ _) (set_rip _ _ _)
  | alu o d s | alui o d v =>
    simp only [exec, Res.next.injEq] at h
    subst h; exact nextOk_same (aluStep_mem _ _ _ _) (aluStep_rip _ _ _ _)
  | imul d s | shl d | shr d =>
    simp only [exec, Res.next.injEq] at h
    subst h; exact nextOk_same (set_mem _ _ _) (set_rip _ _ _)
  | cqo =>
    simp only [exec, Res.next.injEq] at h
    subst h; exact nextOk_same rfl rfl
  | idiv s =>
    simp only [exec] at h
    split at h
    · cases h
    · split at h
      · cases h
      · simp only [Res.next.injEq] at h
        subst h; exact nextOk_same (by simp [set_mem, X.nof]) (by simp [set_rip, X.nof])
  | set c d =>
    simp only [exec] at h
    split at h <;> simp only [reduceCtorEq, Res.next.injEq] at h
    subst h; exact nextOk_same (set_mem _ _ _) (set_rip _ _ _)
  | jmp rel =>
    simp only [exec, Res.next.injEq] at h
    subst h; exact nextOk_jump rfl
  | jcc c rel =>
    simp only [exec] at h
    split at h <;> simp only [reduceCtorEq, Res.next.injEq] at h
    subst h; exact nextOk_jump rfl
  | jmpm m =>
    simp only [exec, opt] at h
    split at h <;> simp only [reduceCtorEq, Res.next.injEq] at h
    subst h; exact nextOk_jump rfl
  | cmpxchg m s =>
    simp only [exec, opt] at h
    split at h
    · cases h
    · next p ho =>
      simp only [Res.next.injEq] at h
      subst h
      exact ⟨by simp only [set_mem]; exact cas_keeps ho, fun _ => by simp only [set_rip]; rfl⟩
  | syscall | ud2 => simp only [exec, reduceCtorEq] at h

end Runner.Beweis
