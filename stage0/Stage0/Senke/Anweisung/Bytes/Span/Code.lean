/- Chunked byte writes reuse putBytesL after capturing both complete operands. -/
module
public import Stage0.Senke.Anweisung.Bytes.Code
@[expose] public section

namespace Gabbro.Stage0.Senke
open Gabbro.Grammatik Runner.IR
variable {D : Deklaration}

abbrev ByteCapture (Γ : Ctx) (a b H : Int) : Ctx := .int a b :: .int 0 H :: Γ

/-- Index arithmetic reads only the captured variable, after all world reads. -/
def chunkIndex {Γ : Ctx} {Λ : List (Res D)} (a b H : Int) (q : Nat) :
    Expr D (.int 0 (2 ^ 64 - 1) :: ByteCapture Γ a b H) Λ (.int (a + 8 * q) (b + 8 * q)) :=
  .add (.var (.there .here)) (.lit (8 * q))

/-- One captured limb and its index become the two scalar bindings consumed by
    the existing byte-write kernel. Capture storage is never used as scratch. -/
def putBytesWordsL (L : Lay D) {Γ : Ctx} {Λ : List (Res D)}
    (t : D.Tab) (f : D.Feld t) (a b H : Int) (lower : 0 ≤ a) (reserved : Nat := 0) :
    (words n q : Nat) → b + 8 * q + n ≤ D.count t → Option (List II × Nat)
  | 0, _, _, _ => some ([], frei (ByteCapture Γ a b H) reserved + 2)
  | words + 1, n, q, upper =>
    if n = 0 then some ([], frei (ByteCapture Γ a b H) reserved + 2) else do
      let s := frei (ByteCapture Γ a b H) reserved
      let idx ← lowE (reserved := reserved) L (chunkIndex (Γ := Γ) (Λ := Λ) a b H q) (s + 1)
      let kernel ← putBytesL L (Γ := ByteCapture Γ a b H) (Λ := Λ)
        t f (a + 8 * q) (b + 8 * q) (2 ^ 64 - 1) (by omega) reserved (min 8 n) 0 (by omega)
      let rest ← if 8 < n then
        putBytesWordsL L (Γ := Γ) (Λ := Λ) t f a b H lower reserved words (n - 8) (q + 1) (by omega)
        else some ([], s + 2)
      pure ([ci 2 s (frei Γ reserved + q) 0] ++ idx.1 ++ kernel.1 ++ rest.1,
        max (s + 2) (max idx.2 (max kernel.2 rest.2)))

/-- Evaluate the complete value before the index; neither is recomputed after
    the first store. Both become ordinary typed bindings in ByteCapture. -/
def putBytesWideL (L : Lay D) {Γ : Ctx} {Λ : List (Res D)}
    (t : D.Tab) (f : D.Feld t) (a b : Int) (n : Nat) (lower : 0 ≤ a)
    (upper : b + n ≤ D.count t) (value index : Option (List II × Nat))
    (reserved : Nat := 0) : Option (List II × Nat) :=
  if n < 2 ^ 31 then do
    let ce ← value
    let ci' ← index
    let H := (256 : Int) ^ n - 1
    let rest ← putBytesWordsL L (Γ := Γ) (Λ := Λ) t f a b H lower reserved
      (valueWords (.int 0 H)) n 0 (by simpa using upper)
    pure (ce.1 ++ ci'.1 ++ rest.1,
      max (max ce.2 ci'.2) (max rest.2 (frei (ByteCapture Γ a b H) reserved + 2)))
  else none

end Gabbro.Stage0.Senke
