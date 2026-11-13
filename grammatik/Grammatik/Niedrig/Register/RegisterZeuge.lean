/-
  File:      Grammatik/Niedrig/Register/RegisterZeuge.lean
  Subject:   WITNESS FOR DEVICE REGISTERS (L2c): a toy device with a
    read-write control register (mirror: the status register) and a
    read-only status register (promise: bit 0 set); a read, a fallible
    read taking the ELSE branch, a transition, and a refused write to the
    read-only register -- all by `rfl` on small terms, stated pointwise.
-/
module

public import Grammatik.Niedrig.Register.Register

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Register

/-- The control register index. -/
def steuerReg : Reg :=
  0

/-- The status register index. -/
def zustandReg : Reg :=
  1

/-- The control declaration: read-write, 8 bits, no promise check, mirror
    is the status register. -/
def steuerAnzeige : RegDecl :=
  { klasse := RegClass.rw
    breite := 8
    zusage := fun _ => true
    spiegel := some 1 }

/-- The status declaration: read-only, 8 bits, promise is bit 0 set. -/
def zustandAnzeige : RegDecl :=
  { klasse := RegClass.r
    breite := 8
    zusage := fun v => v % 2 == 1
    spiegel := none }

/-- The declaration table of the toy device. -/
def spielDecl : Reg → Option RegDecl
  | 0 => some steuerAnzeige
  | 1 => some zustandAnzeige
  | _ => none

/-- The toy state: control and status values. -/
structure Spiel where
  steuer : Nat
  zustand : Nat

/-- Reads name the stored field. -/
def spielLies (s : Spiel) (r : Reg) : Nat :=
  match r with
  | 0 => s.steuer
  | 1 => s.zustand
  | _ => 0

/-- Writes replace the named field. -/
def spielSchreib (s : Spiel) (r v : Nat) : Spiel :=
  match r with
  | 0 => { s with steuer := v }
  | 1 => { s with zustand := v }
  | _ => s

/-- The toy device. -/
def spielGeraet : Device Spiel :=
  { decl := spielDecl
    lies := spielLies
    schreib := spielSchreib }

/-- The fixture start: control 12, status 2 (bit 0 clear, so the promise
    fails). -/
def s0 : Spiel :=
  { steuer := 12
    zustand := 2 }

/-- The state after the transition: control 5, status unchanged. -/
def s1 : Spiel :=
  { steuer := 5
    zustand := 2 }

/-- Read of the control register. -/
theorem zLese :
    regRead spielGeraet s0 0 = (s0, Except.ok 12, [Event.lese 0]) :=
  rfl

/-- The control value read back pointwise. -/
theorem zLeseWert :
    (regRead spielGeraet s0 0).2.1 = Except.ok 12 :=
  rfl

/-- Fallible read of the status register takes the ELSE branch (bit 0 is
    clear). -/
theorem zElseSonst :
    regReadElse spielGeraet s0 1 =
      (s0, Except.ok (FallErgebnis.sonst 2), [Event.lese 1]) :=
  rfl

/-- The ELSE outcome read back pointwise. -/
theorem zElseSonstWert :
    (regReadElse spielGeraet s0 1).2.1 =
      Except.ok (FallErgebnis.sonst 2) :=
  rfl

/-- Transition on the control register reads the status mirror and writes
    back 5. -/
theorem zWechsel :
    regTransition spielGeraet s0 0 15 5 =
      (s1, Except.ok (), [Event.lese 1, Event.schreibe 0 5]) :=
  rfl

/-- The transitioned control value, read back pointwise. -/
theorem zWechselSteuer :
    spielGeraet.lies (regTransition spielGeraet s0 0 15 5).1 0 = 5 :=
  rfl

/-- The status register is untouched by the transition, read back
    pointwise. -/
theorem zWechselZustand :
    spielGeraet.lies (regTransition spielGeraet s0 0 15 5).1 1 = 2 :=
  rfl

/-- Refused: no write to the read-only status register. -/
theorem zSchreibVerweigert :
    regWrite spielGeraet s0 1 3 =
      (s0, Except.error ohneSchreibrecht, []) :=
  rfl

/-- The refused write keeps the control value pointwise. -/
theorem zVerweigertSteuer :
    spielGeraet.lies (regWrite spielGeraet s0 1 3).1 0 = 12 :=
  rfl

/-- The refused write keeps the status value pointwise. -/
theorem zVerweigertZustand :
    spielGeraet.lies (regWrite spielGeraet s0 1 3).1 1 = 2 :=
  rfl

#print axioms Gabbro.Grammatik.Niedrig.Register.zLese
#print axioms Gabbro.Grammatik.Niedrig.Register.zElseSonst
#print axioms Gabbro.Grammatik.Niedrig.Register.zWechsel
#print axioms Gabbro.Grammatik.Niedrig.Register.zSchreibVerweigert

end Gabbro.Grammatik.Niedrig.Register
