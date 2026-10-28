import Runner.Beweis.Sim
import Runner.Beweis.BV

/-! # Straight handlers: a body without jumps, then the dispatch

`straight_ok`: if the handler is `body ++ dispatch`, every instruction of `body` falls through, and the run of
`body` (`runL`) ends where the IR step ends (`Corr`: the same fault, or `r12`, `r13`, `r14` and the memory of the
IR's next state), then the handler simulates the IR step. What is left for each handler is `Corr`, an equation
between two chains of memory reads and writes. -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog

theorem code_prefix {m : Mem} : ∀ {a : W} {is js : List Ins}, Code m a (is ++ js) → Code m a is
  | _, [], _, _ => trivial
  | _, _ :: _, _, ⟨ho, hb, hc⟩ => ⟨ho, hb, code_prefix hc⟩

theorem runL_next : ∀ (is : List Ins) (x z : X), (∀ i ∈ is, Fall i = true) → runL is x = .next z →
    z.rip = x.rip + BitVec.ofNat 64 (lenOf is) ∧ Keeps x.mem z.mem
  | [], x, z, _, h => by
    simp only [runL, Res.next.injEq] at h
    subst h
    exact ⟨by simp [lenOf], Keeps.refl _⟩
  | i :: is, x, z, hf, h => by
    simp only [runL] at h
    cases he : exec i (enc i).length x with
    | next y =>
      rw [he, bind_next] at h
      obtain ⟨hk, hr⟩ := exec_next he
      obtain ⟨hr2, hk2⟩ := runL_next is y z (fun j hj => hf j (List.mem_cons_of_mem _ hj)) h
      refine ⟨?_, hk.trans hk2⟩
      rw [hr2, hr (hf i (List.mem_cons_self ..)), lenOf, lenOf, List.map_cons, List.sum_cons,
        BitVec.ofNat_add, BitVec.add_assoc]
    | fault | sys | unk => rw [he] at h; simp at h

def Corr (y : X) : Res IR.S → Res X → Prop
  | .next s', .next z => z.r12 = s'.pc ∧ z.r13 = s'.fp ∧ z.r14 = y.r14 ∧ z.mem = s'.mem
  | .fault, .fault => True
  | _, _ => False

theorem HSim.prefix {L : Lay} {r : Res IR.S} {y z : X} (h : Star y z) (hs : HSim L r z) : HSim L r y := by
  cases r with
  | next s' => obtain ⟨w, hw, hR⟩ := hs; exact ⟨w, h.trans hw, hR⟩
  | fault => obtain ⟨w, hw, hf⟩ := hs; exact ⟨w, h.trans hw, hf⟩
  | sys q k => obtain ⟨w, k', hw, hst, hk⟩ := hs; exact ⟨w, k', h.trans hw, hst, hk⟩
  | unk => exact hs

/-- A body without jumps at `rip`, then the dispatch. -/
theorem straight_at {L : Lay} {body : List Ins} {r : Res IR.S} (hf : ∀ i ∈ body, Fall i = true) (y : X)
    (hc : Code y.mem y.rip (body ++ dispatch)) (htb : y.r14 = L.T) (hi : ImgInv L y.mem)
    (hcorr : Corr y r (runL body y)) : HSim L r y := by
  have hreach := reach_runL body y (code_prefix hc) (fun i h => hf i ((List.dropLast_sublist _).subset h))
  cases r with
  | next s' =>
    cases hr : runL body y with
    | next z =>
      rw [hr] at hcorr hreach
      obtain ⟨h1, h2, h3, h4⟩ := hcorr
      obtain ⟨hrip, hkp⟩ := runL_next body y z hf hr
      refine ⟨z, hreach, { code := ?_, pc := h1, fp := h2, tb := h3.trans htb, mem := h4, img := hi.keep hkp }⟩
      rw [hrip]
      exact (Code.append hc).keep hkp
    | fault | sys | unk => rw [hr] at hcorr; simp [Corr] at hcorr
  | fault =>
    cases hr : runL body y with
    | fault => rw [hr] at hreach; exact hreach
    | next | sys | unk => rw [hr] at hcorr; simp [Corr] at hcorr
  | sys | unk => cases hr : runL body y <;> rw [hr] at hcorr <;> simp [Corr] at hcorr

theorem straight_ok {L : Lay} {k : Nat} {body : List Ins} {r : Res IR.S} (hk : handler k = body ++ dispatch)
    (hf : ∀ i ∈ body, Fall i = true) (y : X) (hc : Code y.mem y.rip (handler k)) (htb : y.r14 = L.T)
    (hi : ImgInv L y.mem) (hcorr : Corr y r (runL body y)) : HSim L r y :=
  straight_at hf y (hk ▸ hc) htb hi hcorr

/-! ## Matching the two chains -/

@[simp] theorem opt_map {σ α β : Type} (o : Option α) (f : α → β) (g : β → Res σ) :
    opt (o.map f) g = opt o (fun a => g (f a)) := by
  cases o <;> rfl

@[simp] theorem ir_sx (v : BitVec 32) : IR.sx v = sx32 v := rfl

@[simp] theorem sx32_4 : sx32 4#32 = 4#64 := by decide
@[simp] theorem sx32_8 : sx32 8#32 = 8#64 := by decide
@[simp] theorem sx32_12 : sx32 12#32 = 12#64 := by decide
@[simp] theorem sx32_16 : sx32 16#32 = 16#64 := by decide
@[simp] theorem sx32_24 : sx32 24#32 = 24#64 := by decide
@[simp] theorem sx32_32 : sx32 32#32 = 32#64 := by decide
@[simp] theorem sx32_40 : sx32 40#32 = 40#64 := by decide
@[simp] theorem sx32_48 : sx32 48#32 = 48#64 := by decide

theorem corr_opt {σ : Type} {y : X} {o : Option σ} {f : σ → Res IR.S} {g : σ → Res X}
    (h : ∀ a, Corr y (f a) (g a)) : Corr y (opt o f) (opt o g) := by
  cases o
  · trivial
  · exact h _

/-- Match the chains: equal reads on both sides, then the next states. -/
macro "corr_tail" : tactic => `(tactic|
  repeat (first | (apply corr_opt; intro _) | (simp only [opt_some, bind_next]) | (simp only [Corr, and_self]; done) |
    (simp [Corr, aluStep, aluOp, X.set, X.get, X.nof, exec, ea, sx32_zero]; done)))


/-- Unfold both sides of a straight handler, then match the chains read by read. -/
macro "corr" : tactic => `(tactic| (
  simp [IR.op, IR.bin, IR.ret1, IR.f1, IR.f2, IR.f3, IR.ld, IR.slot, IR.nxt, runL, exec, fld, sld, sst, mb, ms,
    ea, X.get, X.set, aluStep, aluOp, X.nof, X.cmpf] <;>
  corr_tail))

end Runner.Beweis
