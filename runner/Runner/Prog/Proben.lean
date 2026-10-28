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

namespace Runner.Prog
open Runner.X86

def WORKER : Nat := 20
def WLOOP : Nat := 21
def WRETRY : Nat := 22
def WDONE : Nat := 23
def WAIT : Nat := 24
def CNT : Nat := 25
def DONEC : Nat := 26
def PLOOP : Nat := 27
def PDONE : Nat := 28
def WF : Nat := 30   -- worker frames: labels 30..33
def MF : Nat := 40

/-- Four threads (`spawn`) each add 1 a thousand times to one shared word with `cas`, then add 1 to a
    second word and `exit`; `main` waits for the second word to reach 4 and prints the first: "4000". -/
def threads : List B :=
  let spawnW (w : Nat) : List IItem := [.adr 60 WORKER, .adr 61 (WF + w), .op 24 62 60 0]
  irImage
    ( spawnW 0 ++ spawnW 1 ++ spawnW 2 ++ spawnW 3 ++
      [ .lab WAIT, .adr 43 DONEC, .op 15 44 43 0, c 45 4, .op 14 46 44 45, .brzL 46 WAIT,
        .adr 47 CNT, .op 15 21 47 0,
        .op 17 22 40 0, c 23 24, .op 3 24 22 23, c 25 10, c 26 48, c 27 1,
        c 29 255, c 31 (-1), .op 10 29 29 31,
        .lab PLOOP,
        .op 7 28 21 25, .op 3 28 28 26, .op 4 24 24 27,
        .op 15 32 24 0, .op 8 32 32 29, .op 9 32 32 28, .op 16 24 32 0,
        .op 6 21 21 25, .brzL 21 PDONE, .jmpL PLOOP,
        .lab PDONE,
        c 33 10, .op 3 34 22 23, .op 16 34 33 0, .op 4 35 34 24, .op 3 35 35 27,
        c 50 1, c 51 1, .op 2 52 24 0, .op 2 53 35 0, c 54 0, c 55 0, c 56 0, .op 23 57 50 0,
        c 50 231, c 51 0, .op 23 57 50 0,
        -- the worker: slot 1 the count, slot 2 = 1, slot 3 the word's address
        .lab WORKER, c 1 1000, c 2 1, .adr 3 CNT,
        .lab WLOOP, .op 15 6 3 0, .op 3 7 6 2, .op 22 8 3 6, .op 14 9 8 6, .brzL 9 WLOOP,
        .op 4 1 1 2, .brzL 1 WDONE, .jmpL WLOOP,
        .lab WDONE, .adr 3 DONEC,
        .lab WRETRY, .op 15 6 3 0, .op 3 7 6 2, .op 22 8 3 6, .op 14 9 8 6, .brzL 9 WRETRY,
        c 10 60, c 11 0, .op 23 12 10 0,
        .lab CNT, .zeros 8, .lab DONEC, .zeros 8,
        .lab (WF + 0), .zeros 1024, .lab (WF + 1), .zeros 1024, .lab (WF + 2), .zeros 1024, .lab (WF + 3), .zeros 1024,
        .lab MF, .zeros 4096 ] )
    MF

end Runner.Prog
