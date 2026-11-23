module
public import Init.Data.Float.Model.Float
public import Init.Data.Float.Model.Float32

@[expose] public section

namespace Gabbro.Core.Katalog

inductive GleitBinaer where
  | add
  | sub
  | mul
  | div
  deriving DecidableEq, Repr

inductive GleitVergleich where
  | eq
  | lt
  | le
  deriving DecidableEq, Repr

inductive GleitFrage (Bits : Type) where
  | binaer (op : GleitBinaer) (a b : Bits)
  | sqrt (a : Bits)
  | fma (a b c : Bits)
  | vonInt (n : Int)
  | vergleich (op : GleitVergleich) (a b : Bits)

inductive GleitAntwort (Bits : Type) where
  | bits (wert : Bits)
  | wahr (wert : Bool)

structure GleitModell (Bits Modell : Type) where
  ofBits : Bits → Modell
  toBits : Modell → Bits
  binaer : GleitBinaer → Modell → Modell → Modell
  sqrt : Modell → Modell
  fma : Modell → Modell → Modell → Modell
  vonInt : Int → Modell
  vergleich : GleitVergleich → Modell → Modell → Bool

def GleitModell.rechne (m : GleitModell Bits Modell) : GleitFrage Bits → GleitAntwort Bits
  | .binaer op a b => .bits (m.toBits (m.binaer op (m.ofBits a) (m.ofBits b)))
  | .sqrt a => .bits (m.toBits (m.sqrt (m.ofBits a)))
  | .fma a b c => .bits (m.toBits (m.fma (m.ofBits a) (m.ofBits b) (m.ofBits c)))
  | .vonInt n => .bits (m.toBits (m.vonInt n))
  | .vergleich op a b => .wahr (m.vergleich op (m.ofBits a) (m.ofBits b))

/-- The model decoder canonicalizes NaNs, allowing hardware-specific NaN encodings while retaining
    the other bits, including a zero's sign. Comparisons return a Boolean. -/
def GleitModell.antwortGleich (m : GleitModell Bits Modell) :
    GleitAntwort Bits → GleitAntwort Bits → Prop
  | .bits a, .bits b => m.ofBits a = m.ofBits b
  | .wahr a, .wahr b => a = b
  | .bits _, .wahr _ => False
  | .wahr _, .bits _ => False

theorem GleitModell.antwortGleich_refl (m : GleitModell Bits Modell) (a : GleitAntwort Bits) :
    m.antwortGleich a a := by
  cases a <;> rfl

def binary32 : GleitModell UInt32 Float32.Model where
  ofBits := Float32.Model.ofBits
  toBits := Float32.Model.toBits
  binaer
    | .add => Float32.Model.add
    | .sub => Float32.Model.sub
    | .mul => Float32.Model.mul
    | .div => Float32.Model.div
  sqrt := Float32.Model.sqrt
  fma := Float32.Model.fma
  vonInt := Float32.Model.ofInt
  vergleich
    | .eq => Float32.Model.beq
    | .lt => Float32.Model.lt
    | .le => Float32.Model.le

def binary64 : GleitModell UInt64 Float.Model where
  ofBits := Float.Model.ofBits
  toBits := Float.Model.toBits
  binaer
    | .add => Float.Model.add
    | .sub => Float.Model.sub
    | .mul => Float.Model.mul
    | .div => Float.Model.div
  sqrt := Float.Model.sqrt
  fma := Float.Model.fma
  vonInt := Float.Model.ofInt
  vergleich
    | .eq => Float.Model.beq
    | .lt => Float.Model.lt
    | .le => Float.Model.le

structure GleitHardware where
  binary32 : GleitFrage UInt32 → GleitAntwort UInt32
  binary64 : GleitFrage UInt64 → GleitAntwort UInt64

/-- Native operations agree with binary32 and binary64 in the default IEEE rounding mode. -/
def nativeFloat (hw : GleitHardware) : Prop :=
  (∀ q, binary32.antwortGleich (binary32.rechne q) (hw.binary32 q)) ∧
  ∀ q, binary64.antwortGleich (binary64.rechne q) (hw.binary64 q)

theorem gleit_erfuellbar : ∃ hw, nativeFloat hw :=
  ⟨⟨binary32.rechne, binary64.rechne⟩, fun q => binary32.antwortGleich_refl (binary32.rechne q),
    fun q => binary64.antwortGleich_refl (binary64.rechne q)⟩

end Gabbro.Core.Katalog
