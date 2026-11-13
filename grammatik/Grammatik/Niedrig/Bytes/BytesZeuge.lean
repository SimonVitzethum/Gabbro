/-
  File:      Grammatik/Niedrig/Bytes/BytesZeuge.lean
  Subject:   WITNESS FOR BYTE CAPABILITIES (L3a): a capability over 4 bytes;
    read refused (uninitialised), write, read back, out-of-range refused,
    write through a read-only narrowing refused, growing refused; all by
    `rfl` on small `Except` equalities.
-/
module

public import Grammatik.Niedrig.Bytes.Bytes

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Bytes

/-- A capability over 4 bytes with both rights. -/
def k0 : ByteCap :=
  { traeger := 0
    lo := 0
    hi := 4
    rechte := Perm.beide }

/-- The start state: nothing initialised. -/
def s0 : ByteState :=
  leererZustand

/-- Refused: reading an uninitialised byte, even in range with rights. -/
theorem zLeseVerweigert : readByte k0 2 s0 = Except.error uninitialisiert :=
  rfl

/-- The state after writing 65 at byte 2. -/
def s1 : ByteState :=
  schreibNach s0 0 2 65

/-- The write computes the marked state. -/
theorem zSchreib : writeByte k0 2 65 s0 = Except.ok s1 :=
  rfl

/-- Read-after-write returns the written value. -/
theorem zLese : readByte k0 2 s1 = Except.ok 65 :=
  rfl

/-- A neighbouring byte stays uninitialised. -/
theorem zNachbar : readByte k0 3 s1 = Except.error uninitialisiert :=
  rfl

/-- Refused: byte 7 is out of range. -/
theorem zAussen : readByte k0 7 s1 = Except.error ausserhalb :=
  rfl

/-- The read-only narrowing of the capability. -/
def kLes : ByteCap :=
  { traeger := 0
    lo := 0
    hi := 4
    rechte := Perm.lese }

/-- Narrowing towards fewer rights computes the read-only capability. -/
theorem zEng : narrowPerm k0 Perm.lese = Except.ok kLes :=
  rfl

/-- Refused: writing through the read-only narrowing. -/
theorem zSchreibVerweigert :
    writeByte kLes 1 9 s1 = Except.error ohneSchreibrecht :=
  rfl

/-- But reading through it works. -/
theorem zLeseLes : readByte kLes 2 s1 = Except.ok 65 :=
  rfl

/-- Refused: narrowing back up to both rights would grow. -/
theorem zWachstumVerweigert :
    narrowPerm kLes Perm.beide = Except.error rechteWachsen :=
  rfl

#print axioms Gabbro.Grammatik.Niedrig.Bytes.zSchreib
#print axioms Gabbro.Grammatik.Niedrig.Bytes.zLese
#print axioms Gabbro.Grammatik.Niedrig.Bytes.zSchreibVerweigert

end Gabbro.Grammatik.Niedrig.Bytes
