import Grammatik.Kern.Semantik.Syscall.Syscall
import Grammatik.Code.Model.Types

/-
  File:      Grammatik/Hardware/Tor/Abi.lean
  Subject:   L2 + L7 + L8 -- THE TRAP CLAUSE OF A GATE, REGISTER NAMES AS DATA, TARGETS AS DATA.
             PLAN-HARDWARE.md section 16.3, 16.8, 16.9 (design); LLVM-BACKEND.md section 11 (A6, A7, A11, A12).

  A `syscall` item already states its number, its input registers, its output register and its clobbers
  (`SysAbi`, Kern/Semantik/Syscall/Syscall.lean) -- but the Lean record there names the sixteen x86_64
  registers as a FIXED enumeration (`SysReg`), and it lacks the two things a compiler needs to emit the
  call without a table of its own: the TRAP INSTRUCTION and the register the NUMBER travels in. This
  file is the generic record:

    * `RegName`   -- a register is a NAME, opaque data of the program (L7: no class table; the name is the
                     one the target's assembler / LLVM constraint `{name}` uses);
    * `Falle`     -- the trap clause `trap "<text>" number in <reg>` (L2): the instruction text is user
                     data the compiler hands to the assembler unread, plus the number register;
    * `TorAbi`    -- number, trap clause, input map, output register, clobbers, with well-formedness
                     `gut` (the checks N063-N066 plus: the number register is no input and no clobber);
    * `ZielDaten` -- a target as data (L8): triple, data layout, word width, byte order, register names.

  What the clause means for machine G: NOTHING. The meaning of a gate call is the gate's contract
  (`Ax`: parameters, answer, frame, `ensures`); the trap clause is LOWERING data. `loese_text_unabh`
  says the register assignment before the trap does not read the text, `Tor.mitFalle_bed` that changing
  the clause changes no meaning. What the CPU must do with the text is a NAMED hardware assumption of the
  gate (the gate's own `assume`), whose Code-side form is `Code/Gate/Need.lean`.

  Proved here: `belegung_nodup` (one value per register at the trap: arguments and number never collide),
  `belegung_param` / `belegung_nummer` (each argument and the number land in their registers),
  `sysabi_zu_tor` (the existing x86_64 `SysAbi` is an instance), planted defects (a clobbered answer
  register, a doubled input register, a number register that is also an input), and witnesses for three
  architectures plus a made-up one -- which is the point: no per-architecture table anywhere.

  No `sorry`, no `native_decide`, no new axiom.
-/

namespace Gabbro.Grammatik.Tor

/-- A register is a name: opaque data of the program or of a target description. -/
structure RegName where
  name : String
  deriving DecidableEq, Repr

/-- **The trap clause** `trap "<text>" number in <reg>`: the instruction text (user data, passed to
    the assembler unread) and the register the call number is loaded into. -/
structure Falle where
  text : String
  nummerReg : RegName
  deriving DecidableEq, Repr

/-- The machine side of one gate: number, trap clause, input map (register, parameter index), the
    answer register, the clobbered registers. -/
structure TorAbi where
  nummer : Nat
  falle : Falle
  ein : List (RegName × Nat)
  aus : RegName
  clobber : List RegName
  deriving DecidableEq, Repr

/-- **Well-formedness.** Input registers pairwise distinct, no parameter bound twice, the answer
    register not clobbered (the old `SysAbi.gut`), and the number register is neither an input nor a
    clobber (it may equal the answer register: x86_64 `rax`). -/
def TorAbi.gut (a : TorAbi) : Prop :=
  (a.ein.map Prod.fst).Nodup ∧ (a.ein.map Prod.snd).Nodup ∧ a.aus ∉ a.clobber ∧
  a.falle.nummerReg ∉ a.ein.map Prod.fst ∧ a.falle.nummerReg ∉ a.clobber

instance (a : TorAbi) : Decidable a.gut :=
  inferInstanceAs (Decidable ((a.ein.map Prod.fst).Nodup ∧ (a.ein.map Prod.snd).Nodup ∧
    a.aus ∉ a.clobber ∧ a.falle.nummerReg ∉ a.ein.map Prod.fst ∧ a.falle.nummerReg ∉ a.clobber))

/-- Every parameter `0 .. np-1` is bound exactly once (the checker's `N065`). -/
def TorAbi.deckt (a : TorAbi) (np : Nat) : Prop := (a.ein.map Prod.snd).Perm (List.range np)

/-! ## 1. The register assignment before the trap -/

/-- What a register holds when the trap executes: the call number or one argument. -/
inductive Quelle where
  | nummer (n : Nat)
  | param (i : Nat)
  deriving DecidableEq, Repr

/-- The assignment: the number register first, then every input register. The trap TEXT is not read. -/
def TorAbi.belegung (a : TorAbi) : List (RegName × Quelle) :=
  (a.falle.nummerReg, .nummer a.nummer) :: a.ein.map (fun p => (p.1, .param p.2))

/-- One value per register: arguments and the number never collide. -/
theorem belegung_nodup {a : TorAbi} (h : a.gut) : (a.belegung.map Prod.fst).Nodup := by
  obtain ⟨h1, -, -, h4, -⟩ := h
  unfold TorAbi.belegung
  simp only [List.map_cons, List.map_map, List.nodup_cons]
  refine ⟨?_, ?_⟩
  · intro hm
    apply h4
    simpa [Function.comp_def] using hm
  · simpa [Function.comp_def] using h1

/-- The number lands in its register. -/
theorem belegung_nummer (a : TorAbi) :
    (a.falle.nummerReg, Quelle.nummer a.nummer) ∈ a.belegung := List.mem_cons_self ..

/-- Every bound parameter lands in its register. -/
theorem belegung_param {a : TorAbi} {r : RegName} {i : Nat} (h : (r, i) ∈ a.ein) :
    (r, Quelle.param i) ∈ a.belegung :=
  List.mem_cons_of_mem _ (List.mem_map.2 ⟨(r, i), h, rfl⟩)

/-- **The clause adds no meaning to the assignment**: the trap text is not read. -/
theorem loese_text_unabh (a : TorAbi) (t : String) :
    ({ a with falle := { a.falle with text := t } } : TorAbi).belegung = a.belegung := rfl

/-- A gate with its machine-G meaning `B` (whatever the model reads of a gate: parameters, answer,
    frame, `ensures`) and its machine side. -/
structure Tor (B : Type) where
  bed : B
  abi : TorAbi

/-- Replacing the trap clause. -/
def Tor.mitFalle {B : Type} (t : Tor B) (f : Falle) : Tor B := { t with abi := { t.abi with falle := f } }

/-- **The trap clause changes no meaning.** -/
theorem Tor.mitFalle_bed {B : Type} (t : Tor B) (f : Falle) : (t.mitFalle f).bed = t.bed := rfl

/-! ## 2. The existing x86_64 record is an instance -/

/-- The x86_64 register name of the old enumeration. -/
def sysRegName : SysReg → RegName
  | .rax => ⟨"rax"⟩ | .rbx => ⟨"rbx"⟩ | .rcx => ⟨"rcx"⟩ | .rdx => ⟨"rdx"⟩
  | .rsi => ⟨"rsi"⟩ | .rdi => ⟨"rdi"⟩ | .rbp => ⟨"rbp"⟩ | .rsp => ⟨"rsp"⟩
  | .r8 => ⟨"r8"⟩ | .r9 => ⟨"r9"⟩ | .r10 => ⟨"r10"⟩ | .r11 => ⟨"r11"⟩
  | .r12 => ⟨"r12"⟩ | .r13 => ⟨"r13"⟩ | .r14 => ⟨"r14"⟩ | .r15 => ⟨"r15"⟩

theorem sysRegName_inj {x y : SysReg} (h : sysRegName x = sysRegName y) : x = y := by
  cases x <;> cases y <;> first | rfl | (exfalso; revert h; decide)

/-- The old record with the trap clause the old model did not carry. -/
def sysAbiZuTor (a : SysAbi) (f : Falle) : TorAbi :=
  { nummer := a.nummer, falle := f, ein := a.ein.map (fun p => (sysRegName p.1, p.2)),
    aus := sysRegName a.aus, clobber := a.clobber.map sysRegName }

/-- **`sysabi_zu_tor`**: a well-formed old record, with a number register that is no input and no
    clobber, is a well-formed generic one. -/
theorem sysabi_zu_tor {a : SysAbi} (h : a.gut) (f : Falle)
    (hn : f.nummerReg ∉ a.ein.map (fun p => sysRegName p.1))
    (hc : f.nummerReg ∉ a.clobber.map sysRegName) : (sysAbiZuTor a f).gut := by
  obtain ⟨h1, h2, h3⟩ := h
  have hinj : Function.Injective sysRegName := fun _ _ h => sysRegName_inj h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [sysAbiZuTor, List.map_map, Function.comp_def]
    have : (a.ein.map Prod.fst).map sysRegName = a.ein.map (fun p => sysRegName p.1) := by
      simp [List.map_map, Function.comp_def]
    rw [← this]
    exact List.Pairwise.map sysRegName (fun _ _ h e => h (hinj e)) h1
  · simpa [sysAbiZuTor, Function.comp_def] using h2
  · intro hm
    simp only [sysAbiZuTor] at hm
    obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hm
    have := hinj hxe
    subst this
    exact h3 hx
  · simpa [sysAbiZuTor, Function.comp_def] using hn
  · simpa [sysAbiZuTor] using hc

/-! ## 3. Targets as data (L8) -/

/-- **A target as data**: the LLVM triple and data layout (strings handed to LLVM unread), the word
    width and byte order the `Code` model is parameterised by (`Code.Conf`), and the register names
    the target's assembler knows. -/
structure ZielDaten where
  triple : String
  layout : String
  wbits : Nat
  big : Bool
  regs : List RegName
  deriving DecidableEq, Repr

/-- A usable target: a word `Code` can be parameterised by, distinct register names. -/
def ZielDaten.gut (z : ZielDaten) : Prop := (z.wbits = 32 ∨ z.wbits = 64) ∧ z.regs.Nodup

instance (z : ZielDaten) : Decidable z.gut :=
  inferInstanceAs (Decidable ((z.wbits = 32 ∨ z.wbits = 64) ∧ z.regs.Nodup))

/-- The `Code` parameters of a usable target: nothing about it is fixed to one ISA. -/
@[reducible] def ZielDaten.conf (z : ZielDaten) (h : z.gut) : Gabbro.Code.Conf := ⟨z.wbits, z.big, h.1⟩

theorem ZielDaten.conf_wbits (z : ZielDaten) (h : z.gut) : (z.conf h).wbits = z.wbits := rfl
theorem ZielDaten.conf_big (z : ZielDaten) (h : z.gut) : (z.conf h).big = z.big := rfl

/-- Every register a gate names is a register of the target. -/
def TorAbi.passtZu (a : TorAbi) (z : ZielDaten) : Prop :=
  (∀ p ∈ a.ein, p.1 ∈ z.regs) ∧ a.aus ∈ z.regs ∧ (∀ c ∈ a.clobber, c ∈ z.regs) ∧
  a.falle.nummerReg ∈ z.regs

instance (a : TorAbi) (z : ZielDaten) : Decidable (a.passtZu z) :=
  inferInstanceAs (Decidable ((∀ p ∈ a.ein, p.1 ∈ z.regs) ∧ a.aus ∈ z.regs ∧
    (∀ c ∈ a.clobber, c ∈ z.regs) ∧ a.falle.nummerReg ∈ z.regs))

/-! ## 4. Witnesses: three architectures and a made-up one -/

def r (s : String) : RegName := ⟨s⟩

/-- x86_64 Linux `write`: number 1 in `rax`, `syscall`, `rcx`/`r11` destroyed. -/
def schreibX86 : TorAbi :=
  { nummer := 1, falle := ⟨"syscall", r "rax"⟩,
    ein := [(r "rdi", 0), (r "rsi", 1), (r "rdx", 2)], aus := r "rax", clobber := [r "rcx", r "r11"] }

/-- aarch64 Linux `write`: number 64 in `x8`, `svc #0`, nothing destroyed. -/
def schreibArm : TorAbi :=
  { nummer := 64, falle := ⟨"svc #0", r "x8"⟩,
    ein := [(r "x0", 0), (r "x1", 1), (r "x2", 2)], aus := r "x0", clobber := [] }

/-- A made-up third architecture (the shape of a RISC-V ecall): number in `a7`, `ecall`. No compiler
    change is needed for it: the whole description is the program's. -/
def schreibRv : TorAbi :=
  { nummer := 64, falle := ⟨"ecall", r "a7"⟩,
    ein := [(r "a0", 0), (r "a1", 1), (r "a2", 2)], aus := r "a0", clobber := [] }

theorem schreib_gut : schreibX86.gut ∧ schreibArm.gut ∧ schreibRv.gut := by decide

theorem schreib_deckt : schreibX86.deckt 3 ∧ schreibArm.deckt 3 ∧ schreibRv.deckt 3 := by
  unfold TorAbi.deckt schreibX86 schreibArm schreibRv
  refine ⟨?_, ?_, ?_⟩ <;> simp [r, List.range, List.range.loop] <;> decide

/-- Three targets as data; the last is 32-bit big endian, to show `Code.Conf` follows the data. -/
def zielX86 : ZielDaten :=
  { triple := "x86_64-unknown-linux-gnu",
    layout := "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128",
    wbits := 64, big := false,
    regs := ["rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp", "r8", "r9", "r10", "r11",
      "r12", "r13", "r14", "r15"].map r }

def zielArm : ZielDaten :=
  { triple := "aarch64-unknown-linux-gnu", layout := "e-m:e-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128",
    wbits := 64, big := false,
    regs := (List.range 31).map (fun i => r ("x" ++ toString i)) }

def zielPpc : ZielDaten :=
  { triple := "powerpc-unknown-linux-gnu", layout := "E-m:e-p:32:32-Fn32-i64:64-n32",
    wbits := 32, big := true, regs := (List.range 32).map (fun i => r ("r" ++ toString i)) }

theorem ziele_gut : zielX86.gut ∧ zielArm.gut ∧ zielPpc.gut := by decide

/-- The two Linux gates fit their targets (every named register is a register of the target). -/
theorem schreib_passt : schreibX86.passtZu zielX86 ∧ schreibArm.passtZu zielArm := by decide

/-- `Code.Conf` follows the data, byte order included. -/
theorem conf_folgt : ((zielPpc.conf (by decide)).wbits = 32 ∧ (zielPpc.conf (by decide)).big = true) ∧
    ((zielX86.conf (by decide)).wbits = 64 ∧ (zielX86.conf (by decide)).big = false) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- Belegung witness: the x86_64 `write` assigns the number to `rax` and the arguments to
    `rdi`, `rsi`, `rdx`, in that order, with no collision. -/
theorem belegung_zeuge :
    schreibX86.belegung = [(r "rax", .nummer 1), (r "rdi", .param 0), (r "rsi", .param 1),
      (r "rdx", .param 2)] ∧ (schreibX86.belegung.map Prod.fst).Nodup :=
  ⟨rfl, belegung_nodup (by decide)⟩

/-! ## 5. Planted defects -/

/-- The answer register is clobbered: refused. -/
theorem defekt_aus_zerstoert :
    ¬ ({ schreibX86 with clobber := [r "rax"] } : TorAbi).gut := by decide

/-- Two parameters in one register: refused. -/
theorem defekt_ein_doppelt :
    ¬ ({ schreibX86 with ein := [(r "rdi", 0), (r "rdi", 1)] } : TorAbi).gut := by decide

/-- The number register is also an input (the number would overwrite an argument): refused. -/
theorem defekt_nummer_ist_eingabe :
    ¬ ({ schreibX86 with ein := [(r "rax", 0)] } : TorAbi).gut := by decide

/-- A gate that names a register its target does not have does not fit that target. -/
theorem defekt_fremdes_register : ¬ schreibArm.passtZu zielX86 := by decide

/-- A target word of 48 bits is no target (`Code.Conf` has no such word). -/
theorem defekt_wort_48 : ¬ ({ zielX86 with wbits := 48 } : ZielDaten).gut := by decide

end Gabbro.Grammatik.Tor
