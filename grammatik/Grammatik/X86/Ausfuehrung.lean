/-
  File:      Grammatik/X86/Ausfuehrung.lean
  Subject:   Executable pilot transitions over the canonical x86 vocabulary.

  Lane 272 (wave A): single-step semantics for the canonical `Befehl`
  constructors, reusing the shared arithmetic (`Wort.lean`: add64/sub64/xor64,
  bedingung) and byte-memory (`Speicher.lean`: read64/write64) helpers. The
  decode length is checked data (1..15); RIP advances before relative control
  flow; displacements are sign-extended int32. MOV preserves flags; CMP writes
  no operand. Failed memory access is explicit `none`; no invented halt.
  No whole-binary, source or concurrency claim is made here.
-/
import Grammatik.X86.Typen
import Grammatik.X86.Wort
import Grammatik.X86.Speicher

namespace Gabbro.Grammatik.X86

/-- Decode-length guard: validated decoding data, never trusted metadata. -/
def laengeOk (l : Nat) : Bool := decide (1 ≤ l ∧ l ≤ 15)

/-- Address after the decoded instruction. -/
def ripNach (rip : Adresse) (l : Nat) : Adresse := rip + BitVec.ofNat 64 l

/-- Sign extension of a 32-bit displacement to a full word. -/
def dispWort (d : BitVec 32) : Wort := sext .b32 (BitVec.ofNat 64 d.toNat)

/-- Base-plus-displacement effective address. -/
def effAddr (s : Zustand) (base : Register) (disp : BitVec 32) : Adresse :=
  s.register base + dispWort disp

/-- Register-file update: `dst` holds `v`, every other register is kept. -/
def regSet (r : Register → Wort) (dst : Register) (v : Wort) :
    Register → Wort :=
  fun q => if q = dst then v else r q

/-- Register write with new RIP and flags; memory is untouched. -/
def schrittRegister (s : Zustand) (nach : Adresse) (f : Flags) (dst : Register)
    (v : Wort) : Zustand :=
  { s with register := regSet s.register dst v, rip := nach, flags := f }

/-- Push successor: stack pointer moved, word stored, RIP advanced. -/
def schrittPush (s : Zustand) (stk : Register) (nach oben : Adresse)
    (m : Speicher) : Zustand :=
  { s with register := regSet s.register stk oben, speicher := m, rip := nach }

/-- Pop into the stack pointer itself: the loaded value wins. -/
def schrittPopTop (s : Zustand) (stk : Register) (nach : Adresse)
    (v : Wort) : Zustand :=
  { s with register := regSet s.register stk v, rip := nach }

/-- Pop into another register: stack pointer advances past the word. -/
def schrittPopReg (s : Zustand) (stk dst : Register) (nach : Adresse)
    (weiter v : Wort) : Zustand :=
  { s with register := regSet (regSet s.register stk weiter) dst v, rip := nach }

/-- Call successor: return address stored, control transferred. -/
def schrittCall (s : Zustand) (stk : Register) (m : Speicher)
    (oben ziel : Adresse) : Zustand :=
  { s with register := regSet s.register stk oben, speicher := m, rip := ziel }

/-- Return successor: target popped, stack pointer advanced. -/
def schrittRet (s : Zustand) (stk : Register) (weiter ziel : Adresse) :
    Zustand :=
  { s with register := regSet s.register stk weiter, rip := ziel }

/-- Single pilot step; `none` is an explicit refusal (bad length or failed
    memory access). Grows one instruction form per commit. -/
def schritt (d : Decodiert) (s : Zustand) : Option Zustand :=
  match laengeOk d.laenge with
  | false => none
  | true =>
    let nach := ripNach s.rip d.laenge
    match d.befehl with
    | .movImm64 dst v => some (schrittRegister s nach s.flags dst v)
    | .movReg64 dst src =>
      some (schrittRegister s nach s.flags dst (s.register src))
    | .addReg64 dst src =>
      let r := add64 (s.register dst) (s.register src)
      some (schrittRegister s nach r.2 dst r.1)
    | .subReg64 dst src =>
      let r := sub64 (s.register dst) (s.register src)
      some (schrittRegister s nach r.2 dst r.1)
    | .xorReg64 dst src =>
      let r := xor64 (s.register dst) (s.register src)
      some (schrittRegister s nach r.2 dst r.1)
    | .cmpReg64 lhs rhs =>
      let r := sub64 (s.register lhs) (s.register rhs)
      some ({ s with rip := nach, flags := r.2 })
    | .load64 dst base disp =>
      match read64 s.speicher (effAddr s base disp) with
      | some v => some (schrittRegister s nach s.flags dst v)
      | none => none
    | .store64 base src disp =>
      match write64 s.speicher (effAddr s base disp) (s.register src) with
      | some m => some ({ s with speicher := m, rip := nach })
      | none => none
    | .jump32 disp => some ({ s with rip := nach + dispWort disp })
    | .jumpIf32 cond disp =>
      some ({ s with rip := if bedingung cond s.flags then nach + dispWort disp
        else nach })
    | .push64 src =>
      -- The pushed value is read BEFORE rsp moves, so `push rsp` stores
      -- the old top, matching the architecture.
      let v := s.register src
      let stk := Register.rsp
      let oben := s.register stk - BitVec.ofNat 64 8
      match write64 s.speicher oben v with
      | some m => some (schrittPush s stk nach oben m)
      | none => none
    | .pop64 dst =>
      let stk := Register.rsp
      match read64 s.speicher (s.register stk) with
      | some v =>
        -- A `pop rsp` destination takes the loaded value: the increment
        -- is discarded, matching the architecture.
        let weiter := s.register stk + BitVec.ofNat 64 8
        some (if dst = stk then schrittPopTop s stk nach v
          else schrittPopReg s stk dst nach weiter v)
      | none => none
    | .call32 disp =>
      let stk := Register.rsp
      let oben := s.register stk - BitVec.ofNat 64 8
      match write64 s.speicher oben nach with
      | some m => some (schrittCall s stk m oben (nach + dispWort disp))
      | none => none
    | .ret =>
      let stk := Register.rsp
      match read64 s.speicher (s.register stk) with
      | some ziel =>
        some (schrittRet s stk (s.register stk + BitVec.ofNat 64 8) ziel)
      | none => none

/-! ## Step equations for the register-only forms.

    Each equation pins the full successor state; every premise is used. -/

/-- The updated register file answers `v` at `dst`. -/
theorem regSet_gleich (r : Register → Wort) (dst : Register) (v : Wort) :
    regSet r dst v dst = v := by
  simp [regSet]

/-- Every other register keeps its value. -/
theorem regSet_fremd (r : Register → Wort) (dst q : Register) (v : Wort)
    (h : q ≠ dst) : regSet r dst v q = r q := by
  unfold regSet
  rw [if_neg h]

/-- A register write keeps the memory. -/
theorem schrittRegister_speicher (s : Zustand) (nach : Adresse) (f : Flags)
    (dst : Register) (v : Wort) :
    (schrittRegister s nach f dst v).speicher = s.speicher := by
  rfl

/-- A register write sets the new flags. -/
theorem schrittRegister_flags (s : Zustand) (nach : Adresse) (f : Flags)
    (dst : Register) (v : Wort) :
    (schrittRegister s nach f dst v).flags = f := by
  rfl

/-- A register write advances RIP to the post-decode address. -/
theorem schrittRegister_rip (s : Zustand) (nach : Adresse) (f : Flags)
    (dst : Register) (v : Wort) :
    (schrittRegister s nach f dst v).rip = nach := by
  rfl

/-- `mov` with an immediate: flags preserved, destination set. -/
theorem schritt_movImm64 (d : Decodiert) (s : Zustand) (dst : Register)
    (v : Wort) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .movImm64 dst v) :
    schritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge) s.flags dst v) := by
  unfold schritt
  rw [hok, h]

/-- `mov` between registers: flags preserved, destination set. -/
theorem schritt_movReg64 (d : Decodiert) (s : Zustand) (dst src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .movReg64 dst src) :
    schritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge) s.flags dst
        (s.register src)) := by
  unfold schritt
  rw [hok, h]

/-- `add`: destination holds the modular sum with architectural flags. -/
theorem schritt_addReg64 (d : Decodiert) (s : Zustand) (dst src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .addReg64 dst src) :
    schritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (add64 (s.register dst) (s.register src)).2 dst
        (add64 (s.register dst) (s.register src)).1) := by
  unfold schritt
  rw [hok, h]

/-- `sub`: destination holds the modular difference with borrow flags. -/
theorem schritt_subReg64 (d : Decodiert) (s : Zustand) (dst src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .subReg64 dst src) :
    schritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (sub64 (s.register dst) (s.register src)).2 dst
        (sub64 (s.register dst) (s.register src)).1) := by
  unfold schritt
  rw [hok, h]

/-- `xor`: destination holds the bitwise xor; AF stays undefined. -/
theorem schritt_xorReg64 (d : Decodiert) (s : Zustand) (dst src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .xorReg64 dst src) :
    schritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge)
        (xor64 (s.register dst) (s.register src)).2 dst
        (xor64 (s.register dst) (s.register src)).1) := by
  unfold schritt
  rw [hok, h]

/-- `cmp`: no operand is written; only flags and RIP move. -/
theorem schritt_cmpReg64 (d : Decodiert) (s : Zustand) (lhs rhs : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .cmpReg64 lhs rhs) :
    schritt d s = some ({ s with rip := ripNach s.rip d.laenge, flags := (sub64 (s.register lhs) (s.register rhs)).2 }) := by
  unfold schritt
  rw [hok, h]

/-! ## Loads, stores and control flow: success and explicit refusal. -/

/-- `load` success: the word at base plus sign-extended displacement lands
    in the destination; flags are preserved. -/
theorem schritt_load64_erfolg (d : Decodiert) (s : Zustand) (dst base : Register)
    (disp : BitVec 32) (v : Wort) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .load64 dst base disp)
    (hrd : read64 s.speicher (effAddr s base disp) = some v) :
    schritt d s =
      some (schrittRegister s (ripNach s.rip d.laenge) s.flags dst v) := by
  unfold schritt
  simp [hok, h, hrd]

/-- `load` refusal: a failed read is an explicit step failure. -/
theorem schritt_load64_verweigert (d : Decodiert) (s : Zustand)
    (dst base : Register) (disp : BitVec 32) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .load64 dst base disp)
    (hrd : read64 s.speicher (effAddr s base disp) = none) :
    schritt d s = none := by
  unfold schritt
  simp [hok, h, hrd]

/-- `store` success: memory carries the word, registers and flags are kept,
    RIP advances past the instruction. -/
theorem schritt_store64_erfolg (d : Decodiert) (s : Zustand)
    (base src : Register) (disp : BitVec 32) (m : Speicher)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .store64 base src disp)
    (hwr : write64 s.speicher (effAddr s base disp) (s.register src) = some m) :
    schritt d s = some ({ s with speicher := m, rip := ripNach s.rip d.laenge }) := by
  unfold schritt
  simp [hok, h, hwr]

/-- `store` refusal: a failed write is an explicit step failure. -/
theorem schritt_store64_verweigert (d : Decodiert) (s : Zustand)
    (base src : Register) (disp : BitVec 32) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .store64 base src disp)
    (hwr : write64 s.speicher (effAddr s base disp) (s.register src) = none) :
    schritt d s = none := by
  unfold schritt
  simp [hok, h, hwr]

/-- Unconditional jump: RIP moves to the post-decode address plus the
    sign-extended displacement; nothing else changes. -/
theorem schritt_jump32 (d : Decodiert) (s : Zustand) (disp : BitVec 32)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .jump32 disp) :
    schritt d s =
      some ({ s with rip := ripNach s.rip d.laenge + dispWort disp }) := by
  unfold schritt
  rw [hok, h]

/-- Conditional jump taken: RIP moves past the decode point by the
    sign-extended displacement. -/
theorem schritt_jumpIf32_genommen (d : Decodiert) (s : Zustand)
    (cond : Bedingung) (disp : BitVec 32) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .jumpIf32 cond disp)
    (hbed : bedingung cond s.flags = true) :
    schritt d s =
      some ({ s with rip := ripNach s.rip d.laenge + dispWort disp }) := by
  unfold schritt
  simp [hok, h, hbed]

/-- Conditional jump not taken: RIP is the post-decode address. -/
theorem schritt_jumpIf32_nicht (d : Decodiert) (s : Zustand) (cond : Bedingung)
    (disp : BitVec 32) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .jumpIf32 cond disp)
    (hbed : bedingung cond s.flags = false) :
    schritt d s = some ({ s with rip := ripNach s.rip d.laenge }) := by
  unfold schritt
  simp [hok, h, hbed]

/-- A bad decode length refuses every form, unconditionally. -/
theorem schritt_laenge_verweigert (d : Decodiert) (s : Zustand)
    (h : laengeOk d.laenge = false) : schritt d s = none := by
  unfold schritt
  simp [h]

/-! ## Stack and call steps: success and explicit refusal. -/

/-- `push` success: the old register value lands below the old top. -/
theorem schritt_push64_erfolg (d : Decodiert) (s : Zustand) (src : Register)
    (m : Speicher) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .push64 src)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (s.register src) = some m) :
    schritt d s = some (schrittPush s Register.rsp (ripNach s.rip d.laenge)
      (s.register Register.rsp - BitVec.ofNat 64 8) m) := by
  unfold schritt
  simp [hok, h, hwr]

/-- `push` refusal: a failed stack write is an explicit step failure. -/
theorem schritt_push64_verweigert (d : Decodiert) (s : Zustand) (src : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .push64 src)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (s.register src) = none) :
    schritt d s = none := by
  unfold schritt
  simp [hok, h, hwr]

/-- `pop rsp` success: the loaded word becomes the stack pointer. -/
theorem schritt_pop64_top (d : Decodiert) (s : Zustand) (dst : Register)
    (v : Wort) (hok : laengeOk d.laenge = true) (h : d.befehl = .pop64 dst)
    (hdst : dst = Register.rsp)
    (hrd : read64 s.speicher (s.register Register.rsp) = some v) :
    schritt d s =
      some (schrittPopTop s Register.rsp (ripNach s.rip d.laenge) v) := by
  unfold schritt
  simp [hok, h, hdst, hrd]

/-- `pop` into another register: the stack pointer advances past the word. -/
theorem schritt_pop64_reg (d : Decodiert) (s : Zustand) (dst : Register)
    (v : Wort) (hok : laengeOk d.laenge = true) (h : d.befehl = .pop64 dst)
    (hdst : dst ≠ Register.rsp)
    (hrd : read64 s.speicher (s.register Register.rsp) = some v) :
    schritt d s = some (schrittPopReg s Register.rsp dst
      (ripNach s.rip d.laenge)
      (s.register Register.rsp + BitVec.ofNat 64 8) v) := by
  unfold schritt
  simp [hok, h, hdst, hrd]

/-- `pop` refusal: a failed stack read is an explicit step failure. -/
theorem schritt_pop64_verweigert (d : Decodiert) (s : Zustand) (dst : Register)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .pop64 dst)
    (hrd : read64 s.speicher (s.register Register.rsp) = none) :
    schritt d s = none := by
  unfold schritt
  simp [hok, h, hrd]

/-- `call` success: the post-decode address is stored, control transfers
    to it plus the sign-extended displacement. -/
theorem schritt_call32_erfolg (d : Decodiert) (s : Zustand) (disp : BitVec 32)
    (m : Speicher) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .call32 disp)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip d.laenge) = some m) :
    schritt d s = some (schrittCall s Register.rsp m
      (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip d.laenge + dispWort disp)) := by
  unfold schritt
  simp [hok, h, hwr]

/-- `call` refusal: a failed return-address write is an explicit failure. -/
theorem schritt_call32_verweigert (d : Decodiert) (s : Zustand)
    (disp : BitVec 32) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .call32 disp)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip d.laenge) = none) :
    schritt d s = none := by
  unfold schritt
  simp [hok, h, hwr]

/-- `ret` success: control moves to the popped word, the stack advances. -/
theorem schritt_ret_erfolg (d : Decodiert) (s : Zustand) (ziel : Wort)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .ret)
    (hrd : read64 s.speicher (s.register Register.rsp) = some ziel) :
    schritt d s = some (schrittRet s Register.rsp
      (s.register Register.rsp + BitVec.ofNat 64 8) ziel) := by
  unfold schritt
  simp [hok, h, hrd]

/-- `ret` refusal: a failed target read is an explicit step failure. -/
theorem schritt_ret_verweigert (d : Decodiert) (s : Zustand)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .ret)
    (hrd : read64 s.speicher (s.register Register.rsp) = none) :
    schritt d s = none := by
  unfold schritt
  simp [hok, h, hrd]

/-! ## State and memory frames: what each step leaves alone. -/

/-- `mov` with an immediate changes no memory byte. -/
theorem schritt_movImm64_speicher (d s s' dst v) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .movImm64 dst v) (hstep : schritt d s = some s') :
    s'.speicher = s.speicher := by
  rw [schritt_movImm64 d s dst v hok h] at hstep
  cases hstep
  rfl

/-- `mov` with an immediate preserves the flags. -/
theorem schritt_movImm64_flags (d s s' dst v) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .movImm64 dst v) (hstep : schritt d s = some s') :
    s'.flags = s.flags := by
  rw [schritt_movImm64 d s dst v hok h] at hstep
  cases hstep
  rfl

/-- `mov` with an immediate writes exactly the destination register. -/
theorem schritt_movImm64_reg (d s s' dst q v) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .movImm64 dst v) (hstep : schritt d s = some s')
    (hq : q ≠ dst) : s'.register q = s.register q := by
  rw [schritt_movImm64 d s dst v hok h] at hstep
  cases hstep
  exact regSet_fremd s.register dst q v hq

/-- Register `mov` changes no memory byte. -/
theorem schritt_movReg64_speicher (d s s' dst src) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .movReg64 dst src) (hstep : schritt d s = some s') :
    s'.speicher = s.speicher := by
  rw [schritt_movReg64 d s dst src hok h] at hstep
  cases hstep
  rfl

/-- Register `mov` preserves the flags. -/
theorem schritt_movReg64_flags (d s s' dst src) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .movReg64 dst src) (hstep : schritt d s = some s') :
    s'.flags = s.flags := by
  rw [schritt_movReg64 d s dst src hok h] at hstep
  cases hstep
  rfl

/-- `add` changes no memory byte. -/
theorem schritt_addReg64_speicher (d s s' dst src) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .addReg64 dst src) (hstep : schritt d s = some s') :
    s'.speicher = s.speicher := by
  rw [schritt_addReg64 d s dst src hok h] at hstep
  cases hstep
  rfl

/-- `sub` changes no memory byte. -/
theorem schritt_subReg64_speicher (d s s' dst src) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .subReg64 dst src) (hstep : schritt d s = some s') :
    s'.speicher = s.speicher := by
  rw [schritt_subReg64 d s dst src hok h] at hstep
  cases hstep
  rfl

/-- `xor` changes no memory byte. -/
theorem schritt_xorReg64_speicher (d s s' dst src) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .xorReg64 dst src) (hstep : schritt d s = some s') :
    s'.speicher = s.speicher := by
  rw [schritt_xorReg64 d s dst src hok h] at hstep
  cases hstep
  rfl

/-- `cmp` writes no register at all. -/
theorem schritt_cmpReg64_reg (d s s' lhs rhs q) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .cmpReg64 lhs rhs) (hstep : schritt d s = some s') :
    s'.register q = s.register q := by
  rw [schritt_cmpReg64 d s lhs rhs hok h] at hstep
  cases hstep
  rfl

/-- `cmp` changes no memory byte. -/
theorem schritt_cmpReg64_speicher (d s s' lhs rhs) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .cmpReg64 lhs rhs) (hstep : schritt d s = some s') :
    s'.speicher = s.speicher := by
  rw [schritt_cmpReg64 d s lhs rhs hok h] at hstep
  cases hstep
  rfl

/-- A successful `load` changes no memory byte. -/
theorem schritt_load64_speicher (d s s' dst base disp v)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .load64 dst base disp)
    (hrd : read64 s.speicher (effAddr s base disp) = some v)
    (hstep : schritt d s = some s') :
    s'.speicher = s.speicher := by
  rw [schritt_load64_erfolg d s dst base disp v hok h hrd] at hstep
  cases hstep
  rfl

/-- A successful `load` preserves the flags. -/
theorem schritt_load64_flags (d s s' dst base disp v)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .load64 dst base disp)
    (hrd : read64 s.speicher (effAddr s base disp) = some v)
    (hstep : schritt d s = some s') :
    s'.flags = s.flags := by
  rw [schritt_load64_erfolg d s dst base disp v hok h hrd] at hstep
  cases hstep
  rfl

/-- A successful `store` keeps every permission: only bytes change. -/
theorem schritt_store64_berechtigungen (d s s' base src disp m)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .store64 base src disp)
    (hwr : write64 s.speicher (effAddr s base disp) (s.register src) = some m)
    (hstep : schritt d s = some s') :
    s'.speicher.lesbar = s.speicher.lesbar ∧
      s'.speicher.schreibbar = s.speicher.schreibbar ∧
        s'.speicher.ausfuehrbar = s.speicher.ausfuehrbar := by
  rw [schritt_store64_erfolg d s base src disp m hok h hwr] at hstep
  cases hstep
  exact write64_erhaelt_berechtigungen s.speicher (effAddr s base disp)
    (s.register src) m hwr

/-- A successful `store` changes nothing outside its eight bytes. -/
theorem schritt_store64_rahmen (d s s' base src disp m x)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .store64 base src disp)
    (hwr : write64 s.speicher (effAddr s base disp) (s.register src) = some m)
    (hstep : schritt d s = some s')
    (haussen : ∀ k : Nat, k < 8 → x ≠ addrOff (effAddr s base disp) k) :
    s'.speicher.bytes x = s.speicher.bytes x := by
  rw [schritt_store64_erfolg d s base src disp m hok h hwr] at hstep
  cases hstep
  exact write64_rahmen s.speicher m (effAddr s base disp) x (s.register src)
    hwr haussen

/-- A successful `store` keeps every register. -/
theorem schritt_store64_reg (d s s' base src disp m q)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .store64 base src disp)
    (hwr : write64 s.speicher (effAddr s base disp) (s.register src) = some m)
    (hstep : schritt d s = some s') :
    s'.register q = s.register q := by
  rw [schritt_store64_erfolg d s base src disp m hok h hwr] at hstep
  cases hstep
  rfl

/-- A successful `store` preserves the flags. -/
theorem schritt_store64_flags (d s s' base src disp m)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .store64 base src disp)
    (hwr : write64 s.speicher (effAddr s base disp) (s.register src) = some m)
    (hstep : schritt d s = some s') :
    s'.flags = s.flags := by
  rw [schritt_store64_erfolg d s base src disp m hok h hwr] at hstep
  cases hstep
  rfl

/-- An unconditional jump keeps every register. -/
theorem schritt_jump32_reg (d s s' disp q) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .jump32 disp) (hstep : schritt d s = some s') :
    s'.register q = s.register q := by
  rw [schritt_jump32 d s disp hok h] at hstep
  cases hstep
  rfl

/-- An unconditional jump changes no memory byte. -/
theorem schritt_jump32_speicher (d s s' disp) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .jump32 disp) (hstep : schritt d s = some s') :
    s'.speicher = s.speicher := by
  rw [schritt_jump32 d s disp hok h] at hstep
  cases hstep
  rfl

/-- An unconditional jump preserves the flags. -/
theorem schritt_jump32_flags (d s s' disp) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .jump32 disp) (hstep : schritt d s = some s') :
    s'.flags = s.flags := by
  rw [schritt_jump32 d s disp hok h] at hstep
  cases hstep
  rfl

/-- A taken conditional jump keeps every register. -/
theorem schritt_jumpIf32_genommen_reg (d s s' cond disp q)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .jumpIf32 cond disp)
    (hbed : bedingung cond s.flags = true) (hstep : schritt d s = some s') :
    s'.register q = s.register q := by
  rw [schritt_jumpIf32_genommen d s cond disp hok h hbed] at hstep
  cases hstep
  rfl

/-- A taken conditional jump changes no memory byte. -/
theorem schritt_jumpIf32_genommen_speicher (d s s' cond disp)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .jumpIf32 cond disp)
    (hbed : bedingung cond s.flags = true) (hstep : schritt d s = some s') :
    s'.speicher = s.speicher := by
  rw [schritt_jumpIf32_genommen d s cond disp hok h hbed] at hstep
  cases hstep
  rfl

/-- A taken conditional jump preserves the flags. -/
theorem schritt_jumpIf32_genommen_flags (d s s' cond disp)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .jumpIf32 cond disp)
    (hbed : bedingung cond s.flags = true) (hstep : schritt d s = some s') :
    s'.flags = s.flags := by
  rw [schritt_jumpIf32_genommen d s cond disp hok h hbed] at hstep
  cases hstep
  rfl

/-- An untaken conditional jump keeps every register. -/
theorem schritt_jumpIf32_nicht_reg (d s s' cond disp q)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .jumpIf32 cond disp)
    (hbed : bedingung cond s.flags = false) (hstep : schritt d s = some s') :
    s'.register q = s.register q := by
  rw [schritt_jumpIf32_nicht d s cond disp hok h hbed] at hstep
  cases hstep
  rfl

/-- An untaken conditional jump changes no memory byte. -/
theorem schritt_jumpIf32_nicht_speicher (d s s' cond disp)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .jumpIf32 cond disp)
    (hbed : bedingung cond s.flags = false) (hstep : schritt d s = some s') :
    s'.speicher = s.speicher := by
  rw [schritt_jumpIf32_nicht d s cond disp hok h hbed] at hstep
  cases hstep
  rfl

/-- An untaken conditional jump preserves the flags. -/
theorem schritt_jumpIf32_nicht_flags (d s s' cond disp)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .jumpIf32 cond disp)
    (hbed : bedingung cond s.flags = false) (hstep : schritt d s = some s') :
    s'.flags = s.flags := by
  rw [schritt_jumpIf32_nicht d s cond disp hok h hbed] at hstep
  cases hstep
  rfl

/-- A successful `push` preserves the flags. -/
theorem schritt_push64_flags (d s s' src m) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .push64 src)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (s.register src) = some m) (hstep : schritt d s = some s') :
    s'.flags = s.flags := by
  rw [schritt_push64_erfolg d s src m hok h hwr] at hstep
  cases hstep
  rfl

/-- A successful `push` keeps every permission: only bytes change. -/
theorem schritt_push64_berechtigungen (d s s' src m)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .push64 src)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (s.register src) = some m) (hstep : schritt d s = some s') :
    s'.speicher.lesbar = s.speicher.lesbar ∧
      s'.speicher.schreibbar = s.speicher.schreibbar ∧
        s'.speicher.ausfuehrbar = s.speicher.ausfuehrbar := by
  rw [schritt_push64_erfolg d s src m hok h hwr] at hstep
  cases hstep
  exact write64_erhaelt_berechtigungen s.speicher
    (s.register Register.rsp - BitVec.ofNat 64 8) (s.register src) m hwr

/-- A successful `push` changes nothing outside the eight top bytes. -/
theorem schritt_push64_rahmen (d s s' src m x) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .push64 src)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (s.register src) = some m) (hstep : schritt d s = some s')
    (haussen : ∀ k : Nat, k < 8 →
      x ≠ addrOff (s.register Register.rsp - BitVec.ofNat 64 8) k) :
    s'.speicher.bytes x = s.speicher.bytes x := by
  rw [schritt_push64_erfolg d s src m hok h hwr] at hstep
  cases hstep
  exact write64_rahmen s.speicher m
    (s.register Register.rsp - BitVec.ofNat 64 8) x (s.register src) hwr
    haussen

/-- A successful `pop` changes no memory byte. -/
theorem schritt_pop64_speicher (d s s' dst v) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .pop64 dst)
    (hrd : read64 s.speicher (s.register Register.rsp) = some v)
    (hstep : schritt d s = some s') :
    s'.speicher = s.speicher := by
  by_cases hdst : dst = Register.rsp
  · rw [schritt_pop64_top d s dst v hok h hdst hrd] at hstep
    cases hstep
    rfl
  · rw [schritt_pop64_reg d s dst v hok h hdst hrd] at hstep
    cases hstep
    rfl

/-- A successful `pop` preserves the flags. -/
theorem schritt_pop64_flags (d s s' dst v) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .pop64 dst)
    (hrd : read64 s.speicher (s.register Register.rsp) = some v)
    (hstep : schritt d s = some s') :
    s'.flags = s.flags := by
  by_cases hdst : dst = Register.rsp
  · rw [schritt_pop64_top d s dst v hok h hdst hrd] at hstep
    cases hstep
    rfl
  · rw [schritt_pop64_reg d s dst v hok h hdst hrd] at hstep
    cases hstep
    rfl

/-- A successful `call` preserves the flags. -/
theorem schritt_call32_flags (d s s' disp m) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .call32 disp)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip d.laenge) = some m) (hstep : schritt d s = some s') :
    s'.flags = s.flags := by
  rw [schritt_call32_erfolg d s disp m hok h hwr] at hstep
  cases hstep
  rfl

/-- A successful `call` keeps every permission: only bytes change. -/
theorem schritt_call32_berechtigungen (d s s' disp m)
    (hok : laengeOk d.laenge = true) (h : d.befehl = .call32 disp)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip d.laenge) = some m) (hstep : schritt d s = some s') :
    s'.speicher.lesbar = s.speicher.lesbar ∧
      s'.speicher.schreibbar = s.speicher.schreibbar ∧
        s'.speicher.ausfuehrbar = s.speicher.ausfuehrbar := by
  rw [schritt_call32_erfolg d s disp m hok h hwr] at hstep
  cases hstep
  exact write64_erhaelt_berechtigungen s.speicher
    (s.register Register.rsp - BitVec.ofNat 64 8) (ripNach s.rip d.laenge) m
    hwr

/-- A successful `call` changes nothing outside the eight top bytes. -/
theorem schritt_call32_rahmen (d s s' disp m x) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .call32 disp)
    (hwr : write64 s.speicher (s.register Register.rsp - BitVec.ofNat 64 8)
      (ripNach s.rip d.laenge) = some m) (hstep : schritt d s = some s')
    (haussen : ∀ k : Nat, k < 8 →
      x ≠ addrOff (s.register Register.rsp - BitVec.ofNat 64 8) k) :
    s'.speicher.bytes x = s.speicher.bytes x := by
  rw [schritt_call32_erfolg d s disp m hok h hwr] at hstep
  cases hstep
  exact write64_rahmen s.speicher m
    (s.register Register.rsp - BitVec.ofNat 64 8) x
    (ripNach s.rip d.laenge) hwr haussen

/-- A successful `ret` changes no memory byte. -/
theorem schritt_ret_speicher (d s s' ziel) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .ret)
    (hrd : read64 s.speicher (s.register Register.rsp) = some ziel)
    (hstep : schritt d s = some s') :
    s'.speicher = s.speicher := by
  rw [schritt_ret_erfolg d s ziel hok h hrd] at hstep
  cases hstep
  rfl

/-- A successful `ret` preserves the flags. -/
theorem schritt_ret_flags (d s s' ziel) (hok : laengeOk d.laenge = true)
    (h : d.befehl = .ret)
    (hrd : read64 s.speicher (s.register Register.rsp) = some ziel)
    (hstep : schritt d s = some s') :
    s'.flags = s.flags := by
  rw [schritt_ret_erfolg d s ziel hok h hrd] at hstep
  cases hstep
  rfl

/- CUTS:
   All pilot constructors step; step equations, frame facts, the reached
   witness and the branch/call probes are still open. No decoder, encoder,
   TSO bridge, source correspondence, ABI/loader, cost transfer or
   final-image claim is proved here.
-/

#print axioms schritt

end Gabbro.Grammatik.X86
