import Runner.Beweis.Gerade

/-! # The straight handlers simulate their IR instruction

For each opcode whose handler is a body without jumps followed by the dispatch: `straight_ok` with the body and
the matching of the two chains (`corr`). -/

namespace Runner.Beweis
open Runner.X86 Runner.Prog

/-- The common premises: `rip` at the handler, `r14` the table, the runner in place. -/
abbrev HPre (L : Lay) (k : Nat) (y : X) : Prop :=
  y.rip = L.H k ∧ y.r14 = L.T ∧ ImgInv L y.mem

theorem HPre.code {L : Lay} {k : Nat} {y : X} (h : HPre L k y) : Code y.mem y.rip (handler k) := by
  rw [h.1]; exact h.2.2.2 k

def binBody (b : List Ins) : List Ins :=
  [fld .rax 2, sld .rax .rax, fld .rdx 3, sld .rdx .rdx] ++ b ++ [fld .rcx 1, sst .rcx .rax, .alui .add .r12 16]

def divBody (r : Reg) : List Ins :=
  [fld .rax 2, sld .rax .rax, fld .rsi 3, sld .rsi .rsi, .cqo, .idiv .rsi, fld .rcx 1, sst .rcx r, .alui .add .r12 16]

def shiftBody (sh : Ins) : List Ins :=
  [fld .rax 2, sld .rax .rax, fld .rcx 3, sld .rcx .rcx, sh, fld .rdx 1, sst .rdx .rax, .alui .add .r12 16]

theorem h1_ok {L : Lay} {y : X} (h : HPre L 1 y) : HSim L (IR.op 1 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := [fld .rax 2, fld .rcx 1, sst .rcx .rax, .alui .add .r12 16]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    corr)

theorem h2_ok {L : Lay} {y : X} (h : HPre L 2 y) : HSim L (IR.op 2 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := [fld .rax 2, sld .rax .rax, fld .rcx 1, sst .rcx .rax, .alui .add .r12 16]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    corr)

theorem h3_ok {L : Lay} {y : X} (h : HPre L 3 y) : HSim L (IR.op 3 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := binBody [.alu .add .rax .rdx]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    simp only [binBody, List.cons_append, List.nil_append]
    corr)

theorem h4_ok {L : Lay} {y : X} (h : HPre L 4 y) : HSim L (IR.op 4 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := binBody [.alu .sub .rax .rdx]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    simp only [binBody, List.cons_append, List.nil_append]
    corr)

theorem h5_ok {L : Lay} {y : X} (h : HPre L 5 y) : HSim L (IR.op 5 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := binBody [.imul .rax .rdx]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    simp only [binBody, List.cons_append, List.nil_append]
    corr)

theorem h6_ok {L : Lay} {y : X} (h : HPre L 6 y) : HSim L (IR.op 6 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := divBody .rax) rfl (by decide) y h.code h.2.1 h.2.2 (by
    simp [IR.op, IR.bin, IR.ret1, IR.f1, IR.f2, IR.f3, IR.ld, IR.slot, IR.nxt, runL, exec, fld, sld, sst, mb, ms,
      ea, X.get, X.set, aluStep, aluOp, X.nof, X.cmpf, binBody, divBody, shiftBody, cqo_int', IR.sdiv]
    repeat (apply corr_opt; intro _)
    split
    · trivial
    · split
      · trivial
      · corr_tail)

theorem h7_ok {L : Lay} {y : X} (h : HPre L 7 y) : HSim L (IR.op 7 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := divBody .rdx) rfl (by decide) y h.code h.2.1 h.2.2 (by
    simp [IR.op, IR.bin, IR.ret1, IR.f1, IR.f2, IR.f3, IR.ld, IR.slot, IR.nxt, runL, exec, fld, sld, sst, mb, ms,
      ea, X.get, X.set, aluStep, aluOp, X.nof, X.cmpf, binBody, divBody, shiftBody, cqo_int', IR.srem]
    repeat (apply corr_opt; intro _)
    split
    · trivial
    · split
      · trivial
      · corr_tail)

theorem h8_ok {L : Lay} {y : X} (h : HPre L 8 y) : HSim L (IR.op 8 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := binBody [.alu .and .rax .rdx]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    simp only [binBody, List.cons_append, List.nil_append]
    corr)

theorem h9_ok {L : Lay} {y : X} (h : HPre L 9 y) : HSim L (IR.op 9 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := binBody [.alu .or .rax .rdx]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    simp only [binBody, List.cons_append, List.nil_append]
    corr)

theorem h10_ok {L : Lay} {y : X} (h : HPre L 10 y) : HSim L (IR.op 10 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := binBody [.alu .xor .rax .rdx]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    simp only [binBody, List.cons_append, List.nil_append]
    corr)

theorem h11_ok {L : Lay} {y : X} (h : HPre L 11 y) : HSim L (IR.op 11 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := shiftBody (.shl .rax)) rfl (by decide) y h.code h.2.1 h.2.2 (by
    simp only [shiftBody, List.cons_append, List.nil_append]
    corr)

theorem h12_ok {L : Lay} {y : X} (h : HPre L 12 y) : HSim L (IR.op 12 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := shiftBody (.shr .rax)) rfl (by decide) y h.code h.2.1 h.2.2 (by
    simp only [shiftBody, List.cons_append, List.nil_append]
    corr)

theorem h13_ok {L : Lay} {y : X} (h : HPre L 13 y) : HSim L (IR.op 13 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := binBody [.alu .cmp .rax .rdx, .set .l .rax, .zx8 .rax .rax]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    simp [IR.op, IR.bin, IR.ret1, IR.f1, IR.f2, IR.f3, IR.ld, IR.slot, IR.nxt, runL, exec, fld, sld, sst, mb, ms,
      ea, X.get, X.set, aluStep, aluOp, X.nof, X.cmpf, binBody, divBody, shiftBody, Cond.eval, slt_flags, IR.bool, zx_bool]
    corr_tail)

theorem h14_ok {L : Lay} {y : X} (h : HPre L 14 y) : HSim L (IR.op 14 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := binBody [.alu .cmp .rax .rdx, .set .z .rax, .zx8 .rax .rax]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    simp [IR.op, IR.bin, IR.ret1, IR.f1, IR.f2, IR.f3, IR.ld, IR.slot, IR.nxt, runL, exec, fld, sld, sst, mb, ms,
      ea, X.get, X.set, aluStep, aluOp, X.nof, X.cmpf, binBody, divBody, shiftBody, Cond.eval, eq_flags, IR.bool, zx_prop]
    corr_tail)

theorem h15_ok {L : Lay} {y : X} (h : HPre L 15 y) : HSim L (IR.op 15 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := [fld .rax 2, sld .rax .rax, .ld .rax (mb .rax), fld .rcx 1, sst .rcx .rax, .alui .add .r12 16]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    corr)

theorem h16_ok {L : Lay} {y : X} (h : HPre L 16 y) : HSim L (IR.op 16 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := [fld .rax 1, sld .rax .rax, fld .rdx 2, sld .rdx .rdx, .st (mb .rax) .rdx, .alui .add .r12 16]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    corr)

theorem h17_ok {L : Lay} {y : X} (h : HPre L 17 y) : HSim L (IR.op 17 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := [fld .rax 2, .lea .rax (ms .r13 .rax), fld .rcx 1, sst .rcx .rax, .alui .add .r12 16]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    corr)

theorem h18_ok {L : Lay} {y : X} (h : HPre L 18 y) : HSim L (IR.op 18 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := [fld .rax 1, .alu .add .r12 .rax]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    corr)

theorem h20_ok {L : Lay} {y : X} (h : HPre L 20 y) : HSim L (IR.op 20 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := [fld .rax 1, sld .rax .rax, fld .rdx 2, .lea .rdx (ms .r13 .rdx), .lea .rcx (mb .r12 16),
      .st (mb .rdx) .rcx, .st (mb .rdx 8) .r13, .mov .r13 .rdx, .mov .r12 .rax]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    corr)

theorem h21_ok {L : Lay} {y : X} (h : HPre L 21 y) : HSim L (IR.op 21 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := [.ld .rax (mb .r13), .ld .r13 (mb .r13 8), .mov .r12 .rax]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    corr)

theorem h22_ok {L : Lay} {y : X} (h : HPre L 22 y) : HSim L (IR.op 22 ⟨y.r12, y.r13, y.mem⟩) y :=
  straight_ok (body := [fld .rax 2, .ld .rdx (ms .r13 .rax), fld .rcx 3, .ld .rax (ms .r13 .rcx),
      .ld .rsi (ms .r13 .rcx 8), .cmpxchg (mb .rdx) .rsi, fld .rcx 1, sst .rcx .rax, .alui .add .r12 16]) rfl (by decide) y h.code h.2.1 h.2.2 (by
    corr)

end Runner.Beweis
