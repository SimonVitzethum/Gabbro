import Runner.Beweis.Holen
import Runner.IR.Step
import Runner.Prog.Code

/-! # The simulation relation between `S0IR` and the runner on the x86-64 model

* `Lay`: where the runner lies, the handler of each opcode and the dispatch table. `ImgInv L m`: the runner's
  code and table are in memory, readable and not writable.
* `R L s x`: `x` stands at a copy of the dispatch code with `r12 = pc`, `r13 = fp`, `r14` = the table, the same
  memory as `s`, and the runner in place.
* `HSim L r y`: from `y` (just after the dispatch jumped to the handler) the model does what the IR step `r`
  does: the same fault, the same request to the kernel and after every answer the same continuation, or a state
  related to the IR's next state. -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog

def wbytes (v : W) : List B := (List.range 8).map fun i => byte (v.toNat / 256 ^ i)

structure Lay where
  H : Nat → W
  T : W

def ImgInv (L : Lay) (m : Mem) : Prop :=
  (∀ op : B, Bytes m (L.T + op.setWidth 64 * BitVec.ofNat 64 (2 ^ 3) + sx32 0) (wbytes (L.H op.toNat))) ∧
  (∀ k, Code m (L.H k) (handler k))

theorem ImgInv.keep {L : Lay} {m m' : Mem} (hk : Keeps m m') (h : ImgInv L m) : ImgInv L m' :=
  ⟨fun op => (h.1 op).keep hk, fun k => (h.2 k).keep hk⟩

structure R (L : Lay) (s : IR.S) (x : X) : Prop where
  code : Code x.mem x.rip dispatch
  pc : x.r12 = s.pc
  fp : x.r13 = s.fp
  tb : x.r14 = L.T
  mem : x.mem = s.mem
  img : ImgInv L x.mem

def HSim (L : Lay) : Res IR.S → X → Prop
  | .next s', y => ∃ z, Star y z ∧ R L s' z
  | .fault, y => Reach y .fault
  | .sys q k, y => ∃ z k', Star y z ∧ step z = .sys q k' ∧ ∀ resp, ImgInv L resp.mem →
      ∃ z', k' resp = some z' ∧
        match k resp with
        | none => Reach z' .fault
        | some s' => ∃ w, Star z' w ∧ R L s' w
  | .unk, _ => False

/-! ## Reading a word placed as bytes -/

theorem rd64_bytes {m : Mem} {a v : W} (h : Bytes m a (wbytes v)) : m.rd64 a = some v := by
  have hv := v.isLt
  have hb : ∀ j, j < 8 → m.b (a + BitVec.ofNat 64 j) = byte (v.toNat / 256 ^ j) ∧
      m.rd (a + BitVec.ofNat 64 j) = true := fun j hj => by
    obtain ⟨b1, b2, _⟩ := h j (by simp [wbytes]; exact hj)
    simp only [wbytes, List.getElem_map, List.getElem_range] at b1
    exact ⟨b1, b2⟩
  have ha : Mem.all m.rd a 8 = true := all_of fun j hj => (hb j hj).2
  simp only [Mem.rd64, ha, ↓reduceIte, Option.some.injEq]
  simp only [Mem.le, (hb 0 (by decide)).1, (hb 1 (by decide)).1, (hb 2 (by decide)).1, (hb 3 (by decide)).1,
    (hb 4 (by decide)).1, (hb 5 (by decide)).1, (hb 6 (by decide)).1, (hb 7 (by decide)).1]
  apply BitVec.eq_of_toNat_eq
  simp only [byte, BitVec.toNat_ofNat]
  omega

/-! ## Dispatch -/

@[simp] theorem sx32_zero : sx32 0#32 = 0#64 := by decide

theorem dispatch_ok {L : Lay} {s : IR.S} {x : X} (hR : R L s x) :
    (s.mem.rd8 s.pc = none → Reach x .fault) ∧
    (∀ op, s.mem.rd8 s.pc = some op → ∃ y, Plus x y ∧ y.rip = L.H op.toNat ∧ y.r12 = x.r12 ∧
      y.r13 = x.r13 ∧ y.r14 = x.r14 ∧ y.mem = x.mem) := by
  have h1 := step_code hR.code
  have hc2 : Code x.mem (x.rip + BitVec.ofNat 64 (enc (.ldzx .rax (mb .r12))).length) [.jmpm (ms .r14 .rax)] :=
    hR.code.2.2
  have hea : ea x (mb .r12) = s.pc := by simp [ea, mb, X.get, sx32_zero, hR.pc]
  constructor
  · intro hn
    refine Reach.here ?_ (by simp)
    rw [h1]
    simp only [exec, hea, hR.mem, hn, opt_none]
  · intro op hop
    have hx : exec (.ldzx .rax (mb .r12)) (enc (.ldzx .rax (mb .r12))).length x =
        .next ({ x with rip := x.rip + BitVec.ofNat 64 (enc (.ldzx .rax (mb .r12))).length }.set .rax
          (op.setWidth 64)) := by
      simp only [exec, hea, hR.mem, hop, opt_some]
    let x1 := ({ x with rip := x.rip + BitVec.ofNat 64 (enc (.ldzx .rax (mb .r12))).length }.set .rax
      (op.setWidth 64))
    have h2 : step x1 = exec (.jmpm (ms .r14 .rax)) (enc (.jmpm (ms .r14 .rax))).length x1 :=
      step_code (x := x1) hc2
    have ht := rd64_bytes (hR.img.1 op)
    refine ⟨{ x1 with rip := L.H op.toNat }, ⟨x1, h1.trans hx, ?_⟩, rfl, rfl, rfl, rfl, rfl⟩
    refine Star.step ?_ (Star.refl _)
    rw [h2]
    simp only [exec, ea, ms, X.get, x1, X.set, hR.tb] at ht ⊢
    simp only [ht, opt_some]

end Runner.Beweis
