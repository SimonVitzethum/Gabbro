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

namespace Runner.Prog
open Runner.X86

def PATH : Nat := 70
def MSG : Nat := 71
def PING : Nat := 72
def BUF : Nat := 73
def IOF : Nat := 74

/-- `sys` with number `nr` and the arguments in slots 51..56, the result into slot `r` (args set before). -/
def sysc (nr : Int) (r : Int) : List IItem := [c 50 nr, .op 23 r 50 0]

/-- Arbitrary system calls with buffers in the image: `openat`/`write`/`close` a file, `openat`/`read`/`close` it
    again, `unlink` it, print what was read; then `socketpair`, `write` into one end, `read` from the other, print
    it. Expected: "file io ok\nping\n", exit 0. -/
def io : List B :=
  let str (s : String) : List B := s.toUTF8.toList.map fun u => byte u.toNat
  let path := str "runner-io-probe.txt" ++ [byte 0]
  let msg := str "file io ok\n"
  let ping := str "ping\n"
  let its : List IItem :=
    [ -- fd = openat(AT_FDCWD, path, O_CREAT|O_WRONLY|O_TRUNC, 0644)
      c 51 (-100), .adr 52 PATH, c 53 0x241, c 54 0o644, c 55 0, c 56 0 ] ++ sysc 257 60 ++
    [ .op 2 51 60 0, .adr 52 MSG, c 53 msg.length, c 54 0 ] ++ sysc 1 61 ++          -- write(fd, msg, n)
    [ .op 2 51 60 0 ] ++ sysc 3 61 ++                                                  -- close(fd)
    [ c 51 (-100), .adr 52 PATH, c 53 0, c 54 0 ] ++ sysc 257 60 ++                    -- openat(.., O_RDONLY)
    [ .op 2 51 60 0, .adr 52 BUF, c 53 64 ] ++ sysc 0 62 ++                            -- n = read(fd, buf, 64)
    [ .op 2 51 60 0 ] ++ sysc 3 61 ++
    [ c 51 (-100), .adr 52 PATH, c 53 0 ] ++ sysc 263 61 ++                             -- unlinkat(.., path, 0)
    [ c 51 1, .adr 52 BUF, .op 2 53 62 0 ] ++ sysc 1 61 ++                              -- write(1, buf, n)
    -- socketpair(AF_UNIX, SOCK_STREAM, 0, &sv): sv is slot 63 (two 32-bit fds in one word)
    [ c 51 1, c 52 1, c 53 0, .op 17 54 63 0 ] ++ sysc 53 61 ++
    [ c 64 0xFFFFFFFF, .op 8 65 63 64, c 66 32, .op 12 67 63 66 ] ++                   -- fd0, fd1
    [ .op 2 51 65 0, .adr 52 PING, c 53 ping.length ] ++ sysc 1 61 ++                   -- write(fd0, "ping\n")
    [ .op 2 51 67 0, .adr 52 BUF, c 53 64 ] ++ sysc 0 62 ++                             -- n = read(fd1, buf, 64)
    [ c 51 1, .adr 52 BUF, .op 2 53 62 0 ] ++ sysc 1 61 ++
    [ c 51 0 ] ++ sysc 231 61 ++
    [ .lab PATH, .zeros path.length, .lab MSG, .zeros msg.length, .lab PING, .zeros ping.length,
      .lab BUF, .zeros 64, .lab IOF, .zeros 4096 ]
  let img := irImage its IOF
  let t := ilabels its 16
  let put (img : List B) (l : Nat) (bs : List B) : List B :=
    let o := find t l
    img.take o ++ bs ++ img.drop (o + bs.length)
  put (put (put img PATH path) MSG msg) PING ping

end Runner.Prog

namespace Runner.Prog
open Runner.X86

/-! ## Litmus tests of x86-TSO, run by the runner on real threads

Two threads run `N` rounds; a barrier (`cas` on a counter) starts each round together. Round `k` uses its own
`x` at `XS + 16k` and `y` at `XS + 16k + 8`; each thread stores what it read at `RS + 16k + 8w`. `main` writes the
result area to stdout. Slots of a thread: 16 = x, 17 = y, 19 = its result address, 5 = 1, 21/23 = values read. -/

def LX : Nat := 80
def LRS : Nat := 81
def LBAR : Nat := 82
def LDONE : Nat := 83
def LT0 : Nat := 84
def LT1 : Nat := 85
def LF0 : Nat := 86
def LF1 : Nat := 87
def LMF : Nat := 88
def LWAIT : Nat := 89

/-- One thread of a litmus test, labels from `b`: the body runs in each round with `16` = x, `17` = y,
    `19` = the result address. -/
def litmusThread (b : Nat) (w : Nat) (n : Nat) (body : List IItem) : List IItem :=
  let LOOP := b; let RETRY := b + 1; let WT := b + 2; let GO := b + 3; let END := b + 4; let DR := b + 5
  [ c 1 0, c 2 n, .adr 3 LX, .adr 4 LRS, c 5 1, .adr 6 LBAR, c 7 16, c 20 2, c 18 8, c 24 0,
    .lab LOOP,
    .lab RETRY, .op 15 8 6 0, .op 3 9 8 5, .op 22 10 6 8, .op 14 11 10 8, .brzL 11 RETRY,
    .op 3 13 1 5, .op 5 12 13 20,
    .lab WT, .op 15 8 6 0, .op 13 14 8 12, .brzL 14 GO, .jmpL WT,
    .lab GO, .op 5 15 1 7, .op 3 16 3 15, .op 3 17 16 18, .op 3 19 4 15, c 25 (8 * w), .op 3 19 19 25 ] ++
  body ++
  [ .op 3 1 1 5, .op 13 22 1 2, .brzL 22 END, .jmpL LOOP,
    .lab END, .adr 6 LDONE,
    .lab DR, .op 15 8 6 0, .op 3 9 8 5, .op 22 10 6 8, .op 14 11 10 8, .brzL 11 DR,
    c 30 60, c 31 0, .op 23 32 30 0 ]

/-- A litmus image: two thread bodies, `n` rounds. -/
def litmus (n : Nat) (b0 b1 : List IItem) : List B :=
  irImage
    ( [ .adr 60 LT0, .adr 61 LF0, .op 24 62 60 0, .adr 60 LT1, .adr 61 LF1, .op 24 62 60 0,
        .lab LWAIT, .adr 43 LDONE, .op 15 44 43 0, c 45 2, .op 14 46 44 45, .brzL 46 LWAIT,
        c 50 1, c 51 1, .adr 52 LRS, c 53 (16 * n), c 54 0, c 55 0, c 56 0, .op 23 57 50 0,
        c 50 231, c 51 0, .op 23 57 50 0,
        .lab LT0 ] ++ litmusThread 100 0 n b0 ++ [.lab LT1] ++ litmusThread 110 1 n b1 ++
      [ .lab LBAR, .zeros 8, .lab LDONE, .zeros 8, .lab LX, .zeros (16 * n), .lab LRS, .zeros (16 * n),
        .lab LF0, .zeros 1024, .lab LF1, .zeros 1024, .lab LMF, .zeros 4096 ] )
    LMF

def LN : Nat := 20000

/-- store x then load y, against store y then load x: (0, 0) is allowed by TSO. -/
def litSB : List B := litmus LN [.op 16 16 5 0, .op 15 21 17 0, .op 16 19 21 0]
                                [.op 16 17 5 0, .op 15 21 16 0, .op 16 19 21 0]
/-- the stores by `cas` (locked, the buffer empty): (0, 0) is forbidden. -/
def litSBcas : List B := litmus LN [c 26 0, c 27 1, .op 22 28 16 26, .op 15 21 17 0, .op 16 19 21 0]
                                   [c 26 0, c 27 1, .op 22 28 17 26, .op 15 21 16 0, .op 16 19 21 0]
/-- store x, store y, against load y, load x (results at +0 and +8 of thread 1's slot pair): (1, 0) forbidden. -/
def litMP : List B := litmus LN [.op 16 16 5 0, .op 16 17 5 0]
                                [.op 15 21 17 0, .op 15 23 16 0, c 25 8, .op 4 19 19 25, .op 16 19 21 0,
                                 .op 3 29 19 25, .op 16 29 23 0]
/-- load x then store y, against load y then store x: (1, 1) forbidden. -/
def litLB : List B := litmus LN [.op 15 21 16 0, .op 16 17 5 0, .op 16 19 21 0]
                                [.op 15 21 17 0, .op 16 16 5 0, .op 16 19 21 0]

end Runner.Prog
