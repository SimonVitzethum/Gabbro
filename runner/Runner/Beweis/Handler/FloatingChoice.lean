module
public import Runner.Beweis.Handler.Sprung
@[expose] public section

namespace Runner.Beweis
open Runner.X86 Runner.Prog

/-! The portable conversion arms share an actual relative-branch continuation.
    Keep its address algebra abstract over both instruction lists. -/

theorem fpChoose_yes_code {C : W → B} {address : W} {condition : Cond}
    {yes no tail : List Ins} (hc : Code C address (fpChoose condition yes no ++ tail))
    (hsmall : lenOf no + lenOf [.jmp 0] < 2 ^ 31) :
    Code C (address + BitVec.ofNat 64
        (enc (.jcc condition (BitVec.ofNat 32 (lenOf no + lenOf [.jmp 0])))).length +
      sx32 (BitVec.ofNat 32 (lenOf no + lenOf [.jmp 0]))) (yes ++ tail) := by
  have placed := code_append
    (is := [.jcc condition (BitVec.ofNat 32 (lenOf no + lenOf [.jmp 0]))] ++ no ++
      [.jmp (BitVec.ofNat 32 (lenOf yes))]) (js := yes ++ tail)
    (by simpa only [fpChoose, List.append_assoc] using hc)
  rw [sx32_ofNat hsmall]
  simpa [lenOfL, lenOf, enc, le32, BitVec.ofNat_add, BitVec.add_assoc] using placed

theorem fpChoose_no_code {C : W → B} {address : W} {condition : Cond}
    {yes no tail : List Ins} (hc : Code C address (fpChoose condition yes no ++ tail)) :
    Code C (address + BitVec.ofNat 64
        (enc (.jcc condition (BitVec.ofNat 32 (lenOf no + lenOf [.jmp 0])))).length)
      (no ++ [.jmp (BitVec.ofNat 32 (lenOf yes))] ++ yes ++ tail) := by
  simpa only [fpChoose, List.cons_append, List.nil_append, List.append_assoc] using hc.2.2

theorem fpChoose_true {L : Lay} {r : Res IR.T} {x : X} {condition : Cond}
    {yes no tail : List Ins} (hc : Code L.C x.rip (fpChoose condition yes no ++ tail))
    (ht : Cond.eval x condition = some true)
    (hn : Match L r { x with rip := x.rip + BitVec.ofNat 64
        (enc (.jcc condition (BitVec.ofNat 32 (lenOf no + lenOf [.jmp 0])))).length +
      sx32 (BitVec.ofNat 32 (lenOf no + lenOf [.jmp 0])) }) : Match L r x := by
  refine .priv ((step_code hc).trans ?_) hn
  simp only [exec, ht]

theorem fpChoose_false {L : Lay} {r : Res IR.T} {x : X} {condition : Cond}
    {yes no tail : List Ins} (hc : Code L.C x.rip (fpChoose condition yes no ++ tail))
    (ht : Cond.eval x condition = some false)
    (hn : Match L r { x with rip := x.rip + BitVec.ofNat 64
        (enc (.jcc condition (BitVec.ofNat 32 (lenOf no + lenOf [.jmp 0])))).length }) :
    Match L r x := by
  refine .priv ((step_code hc).trans ?_) hn
  simp only [exec, ht]

theorem fpChoose_join_code {C : W → B} {address : W} {yes tail : List Ins}
    (hc : Code C address (.jmp (BitVec.ofNat 32 (lenOf yes)) :: yes ++ tail))
    (hsmall : lenOf yes < 2 ^ 31) :
    Code C (address + BitVec.ofNat 64 (enc (.jmp (BitVec.ofNat 32 (lenOf yes)))).length +
      sx32 (BitVec.ofNat 32 (lenOf yes))) tail := by
  have placed := code_append (is := [.jmp (BitVec.ofNat 32 (lenOf yes))] ++ yes)
    (js := tail) (by simpa only [List.cons_append, List.nil_append, List.append_assoc] using hc)
  rw [sx32_ofNat hsmall]
  simpa [lenOfL, lenOf, BitVec.ofNat_add, BitVec.add_assoc] using placed

end Runner.Beweis
