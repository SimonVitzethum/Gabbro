import Runner.Prog.Code

/-! # The runner's file: ELF header, program headers, code, table

One `PT_LOAD` maps the whole file at `BASE`, readable and executable, not writable; `PT_GNU_STACK` asks for a
non-executable stack. The entry is the loader. That Linux maps the file so is the loader assumption. -/

namespace Runner.Prog
open Runner.X86

def leN (n v : Nat) : List B := (List.range n).map fun i => byte (v / 256 ^ i)

def fileLen : Nat := tblOff + 256 * 8

def ehdr : List B :=
  [byte 0x7F, byte 0x45, byte 0x4C, byte 0x46, byte 2, byte 1, byte 1, byte 0] ++ leN 8 0 ++
  leN 2 2 ++ leN 2 0x3E ++ leN 4 1 ++ leN 8 (BASE + find tab LOADER) ++ leN 8 64 ++ leN 8 0 ++
  leN 4 0 ++ leN 2 64 ++ leN 2 56 ++ leN 2 2 ++ leN 2 64 ++ leN 2 0 ++ leN 2 0

def phdrLoad : List B :=
  leN 4 1 ++ leN 4 5 ++ leN 8 0 ++ leN 8 BASE ++ leN 8 BASE ++ leN 8 fileLen ++ leN 8 fileLen ++ leN 8 0x1000

def phdrStack : List B :=
  leN 4 0x6474E551 ++ leN 4 6 ++ leN 8 0 ++ leN 8 0 ++ leN 8 0 ++ leN 8 0 ++ leN 8 0 ++ leN 8 16

def pad (l : List B) (n : Nat) : List B := l ++ List.replicate (n - l.length) (byte 0)

def code : List B := prog.flatMap fun p => enc p.2

def table : List B := (List.range 256).flatMap fun k => leN 8 (target k)

/-- The whole file. -/
def image : List B := pad (pad (ehdr ++ phdrLoad ++ phdrStack) CODE ++ code) tblOff ++ table

end Runner.Prog
