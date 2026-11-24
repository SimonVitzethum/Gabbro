module

public import Core.Text.Token
public import Init.Data.ByteArray.Lemmas
public import Init.Data.String.Basic
import Init.Omega

@[expose] public section

namespace Gabbro.Core.Ast

/-- The string domain is bytes; a source literal is encoded as UTF-8.
    Substring offsets count bytes, as does the capacity in a type. -/
structure TextValue (capacity : Nat) where
  bytes : ByteArray
  bound : bytes.size ≤ capacity

def TextValue.literal (decoded : List Char) : TextValue decoded.utf8Encode.size :=
  ⟨decoded.utf8Encode, Nat.le_refl _⟩

def TextValue.widen (value : TextValue source) (fits : source ≤ target) : TextValue target :=
  ⟨value.bytes, Nat.le_trans value.bound fits⟩

def TextValue.concat (left : TextValue a) (right : TextValue b) : TextValue (a + b) :=
  ⟨left.bytes ++ right.bytes, by
    rw [ByteArray.size_append]
    exact Nat.add_le_add left.bound right.bound⟩

def TextValue.slice (value : TextValue capacity) (first last : Nat) : TextValue capacity :=
  ⟨value.bytes.extract first last, by
    rw [ByteArray.size_extract]
    have := value.bound
    omega⟩

end Gabbro.Core.Ast
