/-
  File:      Grammatik/Niedrig/Bytes/Bytes.lean
  Subject:   BYTE CAPABILITIES WITH AN INITIALISATION DISCIPLINE (L3a),
    DEFINITIONS: `ByteCap`, `ByteState`, and the total `Except` operations
    with named refusals. The theorems are in `BytesSaetze.lean`.

  THE LAYER (outside the statement: `Spec.lean`, machine G and `Akzeptiert`
  are not touched; nothing imports this module except the witness).
  * A `ByteCap` names an abstract carrier (`Nat`, never a pointer), a
    half-open byte range `lo … hi` with `lo ≤ hi`, and a three-valued
    permission (read, write, both).
  * A `ByteState` maps each carrier and byte to its initialised flag and its
    value. Pointwise maps (`Nat → Nat → Bool`, `Nat → Nat → Nat`) instead of
    range lists: every lemma is a one-line `if` split with no list surgery.
    A byte value below 256 is the stated invariant `byteOk`.
  * `writeByte` needs write permission, range, and `v < 256`, and marks the
    byte initialised. `readByte` needs read permission, range, AND
    initialisation: reading an uninitialised byte is a refusal, never a
    default value. `splitAt` cuts a capability into two adjacent halves;
    `narrowPerm` weakens towards fewer rights only. Grants, generations, and
    loans are L3b, not this package.
-/
module

@[expose] public section


namespace Gabbro.Grammatik.Niedrig.Bytes

/-- The three-valued permission of a byte capability: read, write, or both. -/
inductive Perm
  | lese : Perm
  | schreibe : Perm
  | beide : Perm
  deriving DecidableEq

/-- Read is allowed under `lese` and `beide`. -/
def darfLesen : Perm → Bool
  | Perm.lese => true
  | Perm.schreibe => false
  | Perm.beide => true

/-- Write is allowed under `schreibe` and `beide`. -/
def darfSchreiben : Perm → Bool
  | Perm.lese => false
  | Perm.schreibe => true
  | Perm.beide => true

/-- A byte capability: carrier identity, half-open range, permission. -/
structure ByteCap where
  traeger : Nat
  lo : Nat
  hi : Nat
  rechte : Perm
  deriving DecidableEq

/-- A capability is well-formed when its range is half-open ordered. -/
def capOk (c : ByteCap) : Prop :=
  c.lo ≤ c.hi

/-- The byte state: per carrier and byte the initialised flag and the value. -/
structure ByteState where
  init : Nat → Nat → Bool
  wert : Nat → Nat → Nat

/-- Every stored byte value fits in a byte. -/
def byteOk (s : ByteState) : Prop :=
  ∀ t i, s.wert t i < 256

/-- The empty byte state: nothing initialised, all values zero. -/
def leererZustand : ByteState :=
  { init := fun _ _ => false
    wert := fun _ _ => 0 }

/-- Nothing is initialised in the empty state. -/
theorem leerUninitialisiert (t i : Nat) : leererZustand.init t i = false :=
  rfl

/-- Refusal: the capability has no read right. -/
def ohneLeserecht : String :=
  "byte-ohne-leserecht"

/-- Refusal: the capability has no write right. -/
def ohneSchreibrecht : String :=
  "byte-ohne-schreibrecht"

/-- Refusal: the index is outside `[lo, hi)`. -/
def ausserhalb : String :=
  "byte-ausserhalb"

/-- Refusal: the value does not fit in a byte. -/
def wertZuGross : String :=
  "byte-wert-zu-gross"

/-- Refusal: the byte was never initialised. -/
def uninitialisiert : String :=
  "byte-uninitialisiert"

/-- Refusal: the split point is outside `[lo, hi]`. -/
def teilungAussen : String :=
  "byte-teilung-ausserhalb"

/-- Refusal: narrowing would add rights. -/
def rechteWachsen : String :=
  "byte-rechte-wachsen"

/-- The flags with `(t, i)` marked initialised. -/
def initNach (s : ByteState) (t i : Nat) : Nat → Nat → Bool :=
  fun t' j => if t' = t ∧ j = i then true else s.init t' j

/-- The values with `(t, i)` set to `v`. -/
def wertNach (s : ByteState) (t i v : Nat) : Nat → Nat → Nat :=
  fun t' j => if t' = t ∧ j = i then v else s.wert t' j

/-- Reading back the written byte gives the mark. -/
theorem initNachEq (s : ByteState) (t i : Nat) :
    initNach s t i t i = true := by
  show (if t = t ∧ i = i then true else s.init t i) = true
  have hc : t = t ∧ i = i := ⟨rfl, rfl⟩
  rw [if_pos hc]

/-- Any other byte keeps its flag. -/
theorem initNachAnderer (s : ByteState) (t i t' j : Nat)
    (hfern : ¬ (t' = t ∧ j = i)) :
    initNach s t i t' j = s.init t' j := by
  show (if t' = t ∧ j = i then true else s.init t' j) = s.init t' j
  rw [if_neg hfern]

/-- Reading back the written byte gives the value. -/
theorem wertNachEq (s : ByteState) (t i v : Nat) :
    wertNach s t i v t i = v := by
  show (if t = t ∧ i = i then v else s.wert t i) = v
  have hc : t = t ∧ i = i := ⟨rfl, rfl⟩
  rw [if_pos hc]

/-- Any other byte keeps its value. -/
theorem wertNachAnderer (s : ByteState) (t i v t' j : Nat)
    (hfern : ¬ (t' = t ∧ j = i)) :
    wertNach s t i v t' j = s.wert t' j := by
  show (if t' = t ∧ j = i then v else s.wert t' j) = s.wert t' j
  rw [if_neg hfern]

/-- The state after writing `v` at `(t, i)`. -/
def schreibNach (s : ByteState) (t i v : Nat) : ByteState :=
  { init := initNach s t i
    wert := wertNach s t i v }

/-- The written byte is marked initialised. -/
theorem schreibNachInit (s : ByteState) (t i v : Nat) :
    (schreibNach s t i v).init t i = true :=
  initNachEq s t i

/-- The written byte reads back the value. -/
theorem schreibNachWert (s : ByteState) (t i v : Nat) :
    (schreibNach s t i v).wert t i = v :=
  wertNachEq s t i v

/-- Any other byte keeps its flag after the write. -/
theorem schreibNachInitAnderer (s : ByteState) (t i v t' j : Nat)
    (hfern : ¬ (t' = t ∧ j = i)) :
    (schreibNach s t i v).init t' j = s.init t' j :=
  initNachAnderer s t i t' j hfern

/-- Any other byte keeps its value after the write. -/
theorem schreibNachWertAnderer (s : ByteState) (t i v t' j : Nat)
    (hfern : ¬ (t' = t ∧ j = i)) :
    (schreibNach s t i v).wert t' j = s.wert t' j :=
  wertNachAnderer s t i v t' j hfern

/-- Total write with named refusals: write permission, range, byte value. -/
def writeByte (c : ByteCap) (i v : Nat) (s : ByteState) :
    Except String ByteState :=
  if darfSchreiben c.rechte = true then
    if c.lo ≤ i ∧ i < c.hi then
      if v < 256 then
        Except.ok (schreibNach s c.traeger i v)
      else Except.error wertZuGross
    else Except.error ausserhalb
  else Except.error ohneSchreibrecht

/-- Total read with named refusals: read permission, range, initialisation.
    Reading an uninitialised byte is refused, never a default value. -/
def readByte (c : ByteCap) (i : Nat) (s : ByteState) : Except String Nat :=
  if darfLesen c.rechte = true then
    if c.lo ≤ i ∧ i < c.hi then
      if s.init c.traeger i = true then
        Except.ok (s.wert c.traeger i)
      else Except.error uninitialisiert
    else Except.error ausserhalb
  else Except.error ohneLeserecht

/-- The half-open range test, as a boolean. -/
def inBereich (c : ByteCap) (i : Nat) : Bool :=
  if c.lo ≤ i ∧ i < c.hi then true else false

/-- Split at `k` into two adjacent capabilities over `[lo, k)` and `[k, hi)`;
    the split point must lie in `[lo, hi]`. -/
def splitAt (c : ByteCap) (k : Nat) : Except String (ByteCap × ByteCap) :=
  if c.lo ≤ k ∧ k ≤ c.hi then
    Except.ok ({ c with hi := k }, { c with lo := k })
  else Except.error teilungAussen

/-- The weakening order: `beide` weakens to all, each weakens to itself,
    and nothing else weakens. -/
def schwaecher : Perm → Perm → Bool
  | Perm.beide, Perm.beide => true
  | Perm.beide, _ => false
  | Perm.lese, Perm.schreibe => false
  | Perm.schreibe, Perm.lese => false
  | _, _ => true

/-- Narrow towards fewer rights only; growing is refused by name. -/
def narrowPerm (c : ByteCap) (p : Perm) : Except String ByteCap :=
  if schwaecher p c.rechte = true then
    Except.ok { c with rechte := p }
  else Except.error rechteWachsen

end Gabbro.Grammatik.Niedrig.Bytes
