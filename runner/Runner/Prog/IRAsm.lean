import Runner.Prog.Elf

/-! # An assembler for `S0IR` images (for probes; the real images come from the stage-0 lowering)

Image layout at `IMG`: word 0 the first frame's address, word 1 zero, the code from byte 16, then data and the
frame area. Jumps are byte offsets relative to the jumping instruction. -/

namespace Runner.Prog
open Runner.X86

inductive IItem
  | op (o : Nat) (a b c : Int)
  | lab (l : Nat)
  | jmpL (l : Nat)
  | brzL (a : Int) (l : Nat)
  /-- `const d (IMG + offset of l)` -/
  | adr (d : Int) (l : Nat)
  /-- `n` zero bytes -/
  | zeros (n : Nat)

def IItem.len : IItem → Nat
  | .lab _ => 0
  | .zeros n => n
  | _ => 16

def ilabels : List IItem → Nat → List (Nat × Nat)
  | [], _ => []
  | .lab l :: r, o => (l, o) :: ilabels r o
  | it :: r, o => ilabels r (o + it.len)

def i32 (v : Int) : List B := le32 (BitVec.ofInt 32 v)

def insB (o : Nat) (a b c : Int) : List B := [byte o, byte 0, byte 0, byte 0] ++ i32 a ++ i32 b ++ i32 c

def IItem.bytes (t : List (Nat × Nat)) (o : Nat) : IItem → List B
  | .op k a b c => insB k a b c
  | .lab _ => []
  | .jmpL l => insB 18 ((find t l : Int) - o) 0 0
  | .brzL a l => insB 19 a ((find t l : Int) - o) 0
  | .adr d l => insB 1 d (IMG + find t l) 0
  | .zeros n => List.replicate n (byte 0)

def iemit (t : List (Nat × Nat)) : List IItem → Nat → List B
  | [], _ => []
  | it :: r, o => it.bytes t o ++ iemit t r (o + it.len)

/-- An image whose first frame is at label `fr`. -/
def irImage (its : List IItem) (fr : Nat) : List B :=
  let t := ilabels its 16
  leN 8 (IMG + find t fr) ++ leN 8 0 ++ iemit t its 16

end Runner.Prog
