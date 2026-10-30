/- Subject: Byte writes capture the value and index before changing the world. -/
import Stage0.Senke.Ausdruck

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

/-- The quotient after dropping `j` low bytes. -/
def dropBytes : Nat → Int → Int
  | 0, z => z
  | j + 1, z => dropBytes j z / 256

/-- The captured word's byte `j` into `d`, with one scratch slot. -/
def bytePartC (src d j : Nat) : List II :=
  [ci 2 d src 0, ci 1 (d + 1) (8 * j) 0, ci 12 d d (d + 1),
   ci 1 (d + 1) 255 0, ci 8 d d (d + 1)]

/-- The captured index plus a byte offset, with G's static bound. -/
def byteIndex {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab) (a b : Int) (H : Int)
    (j : Nat) (hlo : 0 ≤ a) (hhi : b + j < D.count t) :
    Expr D (.int a b :: .int 0 H :: Γ) Λ (.index (D.count t)) :=
  .widen (by omega) (by omega) (.add (.var .here) (.lit j))

/-- Extract from the captured word and reuse ordinary index lowering and world stores. -/
def putBytesL (L : Lay D) {Γ : Ctx} {Λ : List (Res D)} (t : D.Tab) (f : D.Feld t)
    (a b H : Int) (hlo : 0 ≤ a) (reserved : Nat := 0) : (n j : Nat) → b + j + n ≤ D.count t → Option (List II × Nat)
  | 0, _, _ => some ([], frei Γ reserved + 2)
  | n + 1, j, hhi => do
    let ce := (bytePartC (frei Γ reserved) (frei Γ reserved + 2) j, frei Γ reserved + 4)
    let ci' ← lowE (reserved := reserved) L (byteIndex (Γ := Γ) (Λ := Λ) t a b H j hlo (by omega)) (frei Γ reserved + 3)
    let ca ← slotA L t f (frei Γ reserved + 3) ci'
    let rest ← putBytesL L (Γ := Γ) (Λ := Λ) t f a b H hlo reserved n (j + 1) (by omega)
    pure (ce.1 ++ ca.1 ++ [ci 16 (frei Γ reserved + 3) (frei Γ reserved + 2) 0] ++ rest.1,
      max (max ce.2 ca.2) rest.2)

end Gabbro.Stage0.Senke
