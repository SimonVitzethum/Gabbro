import Grammatik.Code.Conc.Await

/-
  File:      Grammatik/Code/Conc/Witness.lean
  Subject:   TRACK L, PHASE L3 (START) -- A WITNESS that the lowering of `publish` and `await` is not vacuous.

  One declaration with a table and ONE atomic global whose range is the word of the target (`0 .. 2^w - 1`:
  a `u64` on a 64-bit target, a `u32` on a 32-bit one), so the cell is word-sized and `atomicG` holds. The
  kernel computes, at 64-bit little endian and at 32-bit big endian:
    * `publish g = 0` lowers to one block whose body ends in `astor .. release`;
    * `let x = g awaits {..}; <nothing>` lowers to a block whose body starts with `aload .. acquire`.
  What this does NOT show: a run of two threads (no thread machine over `Code` yet).
-/

namespace Gabbro.Code.Lower.WitC

open Gabbro.Grammatik

def sigC : Signatur Unit Unit Unit Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun _ => true
  konsumiert := []
  produziert := []

/-- The declaration: one table, one atomic global holding a machine word. -/
def cD [Conf] : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 1
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 1
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Unit
  decGlob := inferInstance
  gtyp := fun _ => .int 0 (2 ^ Conf.wbits - 1)
  nutzlast := fun _ => []
  atomar := fun _ => true
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Unit
  decLock := inferInstance
  rang := fun _ => 0
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => sigC
  eigner_nie_erzeugt := fun n _ _ _ h => by simp only [List.not_mem_nil] at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun t h => absurd h (by decide)
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun g h => absurd h (by decide)

section Gen

variable [Conf]

def cLay : Layout cD where
  gblk := fun _ => 0
  tty := fun _ => .arr 1 (.fld (.int 8) .unit)
  rty := fun _ => .fld (.int 8) .unit
  fidx := fun _ _ => 0
  ggblk := fun _ => 1
  lblk := fun _ => 2
  lsrv := fun _ => 3
  shared := fun _ => true
  fno := fun _ => 0

def vC : Vertrag cD := ⟨fun _ => true, fun _ => true, none, 0, [], [], none⟩

theorem pow_pos' [Conf] : (0 : Int) < 2 ^ Conf.wbits := by exact_mod_cast Nat.two_pow_pos _

/-- `publish g = 0` : the value of `0` as a word. -/
def pubE : Expr cD [] [] (cD.gtyp ()) :=
  .widen (lo := 0) (hi := 0) (lo' := 0) (hi' := 2 ^ Conf.wbits - 1) (by decide)
    (by have := pow_pos'
        omega) (.lit 0)

/-- The `await` with nothing after it. -/
def awRest : Gabbro.Grammatik.Block cD vC false [.int 0 (2 ^ Conf.wbits - 1)] [] [] := .nil

def hasInstr (p : Instr → Bool) (r : Option (List Block × St)) : Bool :=
  match r with
  | some (b :: _, _) => b.body.any p
  | _ => false

end Gen

section C64

local instance conf64 : Conf := ⟨64, false, Or.inr rfl⟩

theorem wit64_publish : hasInstr (fun | .astor _ _ _ .rel => true | _ => false)
    (lowerPublish cLay [] () pubE 1 2 ⟨0, 3⟩) = true := by decide +kernel

theorem wit64_await : hasInstr (fun | .aload _ _ _ .acq => true | _ => false)
    (lowerAwait cLay [] (0, 0) () awRest 1 2 ⟨0, 3⟩) = true := by decide +kernel

end C64

section C32

local instance conf32 : Conf := ⟨32, true, Or.inl rfl⟩

theorem wit32_publish : hasInstr (fun | .astor _ _ _ .rel => true | _ => false)
    (lowerPublish cLay [] () pubE 1 2 ⟨0, 3⟩) = true := by decide +kernel

theorem wit32_await : hasInstr (fun | .aload _ _ _ .acq => true | _ => false)
    (lowerAwait cLay [] (0, 0) () awRest 1 2 ⟨0, 3⟩) = true := by decide +kernel

end C32

end Gabbro.Code.Lower.WitC
