/- Subject: Byte writes capture the value and index before changing the world. -/
import Stage0.Senke.Ausdruck

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

/-- The quotient after dropping `j` low bytes. -/
def dropBytes : Nat → Int → Int
  | 0, z => z
  | j + 1, z => dropBytes j z / 256

/-- The captured value is the second variable of the extended environment. -/
def byteQuot {Γ : Ctx} {Λ : List (Res D)} (a b H : Int) : Nat →
    Expr D (.int a b :: .int 0 H :: Γ) Λ (.int 0 H)
  | 0 => .var (.there .here)
  | j + 1 => .div (by decide) (by decide) (byteQuot a b H j) (.lit 256)

/-- One byte of the captured value, expressed using existing G arithmetic. -/
def bytePart {Γ : Ctx} {Λ : List (Res D)} (a b H : Int) (j : Nat) :
    Expr D (.int a b :: .int 0 H :: Γ) Λ (.int 0 255) :=
  .rem (by decide) (by decide) (byteQuot a b H j) (.lit 256)

/-- The captured index plus a byte offset, with G's static bound. -/
def byteIndex {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab) (a b : Int) (H : Int)
    (j : Nat) (hlo : 0 ≤ a) (hhi : b + j < D.count t) :
    Expr D (.int a b :: .int 0 H :: Γ) Λ (.index (D.count t)) :=
  .widen (by omega) (by omega) (.add (.var .here) (.lit j))

/-- Reuse ordinary expression lowering and full-word stores for the byte cells.
    Unsigned values beyond the existing arithmetic fragment are refused by `lowE`. -/
def putBytesL (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab) (f : D.Feld t)
    (a b H : Int) (hlo : 0 ≤ a) : (n j : Nat) → b + j + n ≤ D.count t → Option (List II × Nat)
  | 0, _, _ => some ([], frei Γ + 2)
  | n + 1, j, hhi => do
    let ce ← lowE L (bytePart (Γ := Γ) (Λ := Λ) a b H j) (frei Γ + 2)
    let ci' ← lowE L (byteIndex (Γ := Γ) (Λ := Λ) t a b H j hlo (by omega)) (frei Γ + 3)
    let ca ← slotA L t f (frei Γ + 3) ci'
    let rest ← putBytesL L (Γ := Γ) (Λ := Λ) t f a b H hlo n (j + 1) (by omega)
    pure (ce.1 ++ ca.1 ++ [ci 16 (frei Γ + 3) (frei Γ + 2) 0] ++ rest.1,
      max (max ce.2 ca.2) rest.2)

end Gabbro.Stage0.Senke
