import Runner.Beweis.Handler.Sprung

/-! # `sys`: the handler asks the kernel in the middle

The first twelve instructions read the operands and the seven argument words and execute `syscall`. After the
kernel's answer -- whose memory keeps the runner (`ImgInv`, the named assumption on the kernel) -- the handler
stores `rax` into the result slot and dispatches: a straight body again, handled by `straight_at`. -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog

def sysSeg : List Ins :=
  [fld .rbx 1, .lea .rbx (ms .r13 .rbx), fld .rcx 2, .lea .rcx (ms .r13 .rcx),
   .ld .rax (mb .rcx), .ld .rdi (mb .rcx 8), .ld .rsi (mb .rcx 16), .ld .rdx (mb .rcx 24),
   .ld .r10 (mb .rcx 32), .ld .r8 (mb .rcx 40), .ld .r9 (mb .rcx 48), .syscall]

def sysPost : List Ins := [.st (mb .rbx) .rax, .alui .add .r12 16]

/-- After the answer: the x86 continuation exists and does what the IR continuation does. -/
def SysEnd (L : Lay) (k : Resp → Option IR.S) (k' : Resp → Option X) : Prop :=
  ∀ resp, ImgInv L resp.mem → ∃ z', k' resp = some z' ∧
    HSim L (match k resp with | none => .fault | some s' => .next s') z'

def CorrS (L : Lay) : Res IR.S → Res X → Prop
  | .fault, .fault => True
  | .sys q k, .sys q' k' => q = q' ∧ SysEnd L k k'
  | _, _ => False

theorem corrS_opt {σ : Type} {L : Lay} {o : Option σ} {f : σ → Res IR.S} {g : σ → Res X}
    (h : ∀ a, CorrS L (f a) (g a)) : CorrS L (opt o f) (opt o g) := by
  cases o
  · trivial
  · exact h _

theorem sys_of {L : Lay} {r : Res IR.S} {r' : Res X} {y : X} (hreach : Reach y r') (h : CorrS L r r') :
    HSim L r y := by
  cases r <;> cases r' <;> simp only [CorrS] at h
  · exact hreach
  · next q k q' k' =>
    obtain ⟨rfl, hk⟩ := h
    obtain ⟨z, hz, hs⟩ := hreach
    refine ⟨z, k', hz, hs, fun resp hresp => ?_⟩
    obtain ⟨z', h1, h2⟩ := hk resp hresp
    refine ⟨z', h1, ?_⟩
    cases hkr : k resp <;> simp only [hkr] at h2 ⊢ <;> exact h2

theorem h23_ok {L : Lay} {y : X} (h : HPre L 23 y) : HSim L (IR.op 23 ⟨y.r12, y.r13, y.mem⟩) y := by
  have hc' : Code y.mem y.rip (sysSeg ++ (sysPost ++ dispatch)) := h.code
  obtain ⟨hrip, htb, hi⟩ := h
  apply sys_of (reach_runL sysSeg y (code_prefix hc') (by decide))
  simp [IR.op, IR.f1, IR.f2, IR.ld, IR.slot, sysSeg, runL, exec, fld, ms, mb, ea, X.get, X.set, X.nof]
  repeat (apply corrS_opt; intro _)
  rename_i d _ _ _ _ _ _ _ _
  refine ⟨rfl, fun resp hresp => ⟨_, rfl, ?_⟩⟩
  have hc2 : Code resp.mem (L.H 23) (sysSeg ++ (sysPost ++ dispatch)) := hresp.2 23
  have hcode := Code.append hc2
  have hsum : L.H 23 + BitVec.ofNat 64 (List.map (fun i => (enc i).length) sysSeg).sum =
      y.rip + BitVec.ofNat 64 (enc (fld .rbx 1)).length +
        BitVec.ofNat 64 (enc (.lea .rbx (ms .r13 .rbx))).length + BitVec.ofNat 64 (enc (fld .rcx 2)).length +
        BitVec.ofNat 64 (enc (.lea .rcx (ms .r13 .rcx))).length + BitVec.ofNat 64 (enc (.ld .rax (mb .rcx))).length +
        BitVec.ofNat 64 (enc (.ld .rdi (mb .rcx 8))).length + BitVec.ofNat 64 (enc (.ld .rsi (mb .rcx 16))).length +
        BitVec.ofNat 64 (enc (.ld .rdx (mb .rcx 24))).length + BitVec.ofNat 64 (enc (.ld .r10 (mb .rcx 32))).length +
        BitVec.ofNat 64 (enc (.ld .r8 (mb .rcx 40))).length + BitVec.ofNat 64 (enc (.ld .r9 (mb .rcx 48))).length +
        BitVec.ofNat 64 (enc .syscall).length := by
    rw [hrip]
    simp only [sysSeg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      BitVec.ofNat_add, BitVec.add_assoc]
  simp only [fld, ms, mb] at hsum
  rw [hsum] at hcode
  cases hw : resp.mem.wr64 (y.r13 + sx32 d * 8#64) resp.ret with
  | none =>
    refine straight_at (body := sysPost) (by decide) _ hcode htb hresp ?_
    simp only [sysPost]
    corr
    simp only [hw, opt_none]
    trivial
  | some m =>
    refine straight_at (body := sysPost) (by decide) _ hcode htb hresp ?_
    simp only [sysPost]
    corr
    simp only [hw, opt_some]
    simp [Corr]

end Runner.Beweis
