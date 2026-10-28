import Runner.Prog.IRAsm

/-! # Probe images for the runner on the processor

`hello` writes one line. `probe` uses every opcode but `spawn`: a recursive factorial (`call`, `ret`, `lt`, `brz`,
`mul`, `sub`), its decimal print (`div`, `rem`, `ld`, `st`, `and`, `or`, `xor`, `lea`, `jmp`), and an exit code
folded from `cas`, `shl`, `shr`, `eq`, signed `div`/`rem` of negative numbers. The expected output is computed by
the IR semantics (`Runner.Haupt`), never written by hand. -/

namespace Runner.Prog
open Runner.X86

def c (d k : Int) : IItem := .op 1 d k 0

def hello : List B :=
  let msg := "hello from S0IR\n".toUTF8.toList.map fun u => byte u.toNat
  let its : List IItem :=
    [ c 0 1, c 1 1, .adr 2 1, c 3 msg.length, c 4 0, c 5 0, c 6 0, .op 23 7 0 0,
      c 0 231, c 1 0, .op 23 7 0 0, .lab 1, .zeros msg.length, .lab 2, .zeros 512 ]
  let img := irImage its 2
  -- the message over the zeros at label 1
  let t := ilabels its 16
  let o := find t 1
  img.take o ++ msg ++ img.drop (o + msg.length)

def FACT : Nat := 10
def REC : Nat := 11
def LOOP : Nat := 12
def DONE : Nat := 13
def FRAME : Nat := 14

def probe : List B :=
  irImage
    [ -- fact 10 in the callee frame at slot 64 (arg slot 66, result slot 67)
      c 66 10, .adr 30 FACT, .op 20 30 64 0, .op 2 21 67 0,
      -- decimal print of slot 21 into the buffer at slots 40..43, digits backwards from buf+24
      .op 17 22 40 0, c 23 24, .op 3 24 22 23, c 25 10, c 26 48, c 27 1,
      c 29 255, c 31 (-1), .op 10 29 29 31,
      .lab LOOP,
      .op 7 28 21 25, .op 3 28 28 26, .op 4 24 24 27,
      .op 15 32 24 0, .op 8 32 32 29, .op 9 32 32 28, .op 16 24 32 0,
      .op 6 21 21 25, .brzL 21 DONE, .jmpL LOOP,
      .lab DONE,
      c 33 10, .op 3 34 22 23, .op 16 34 33 0, .op 4 35 34 24, .op 3 35 35 27,
      c 50 1, c 51 1, .op 2 52 24 0, .op 2 53 35 0, c 54 0, c 55 0, c 56 0, .op 23 57 50 0,
      -- exit code: cas, shl, shr, eq, div, rem
      c 70 5, .op 17 71 70 0, c 73 5, c 74 9, .op 22 72 71 73,
      c 75 1, c 76 4, .op 11 77 75 76, c 75 256, c 76 3, .op 12 78 75 76,
      .op 14 79 77 77, c 75 (-7), c 76 2, .op 6 80 75 76, .op 7 81 75 76,
      .op 3 82 70 77, .op 3 82 82 78, .op 3 82 82 79, .op 3 82 82 80, .op 3 82 82 81, .op 3 82 82 72,
      c 50 231, .op 2 51 82 0, .op 23 57 50 0,
      -- fact(n): slot 2 = n, slot 3 = result; callee frame at slot 8 (arg 10, result 11)
      .lab FACT,
      c 4 1, .op 13 5 2 4, .brzL 5 REC, c 3 1, .op 21 0 0 0,
      .lab REC,
      .op 4 10 2 4, .adr 6 FACT, .op 20 6 8 0, .op 5 3 2 11, .op 21 0 0 0,
      .lab FRAME, .zeros 4096 ]
    FRAME

end Runner.Prog
