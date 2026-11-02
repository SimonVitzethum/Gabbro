module

@[expose] public section

namespace Gabbro.Grammatik

/-- Die Typen der Kernsprache. -/
inductive Ty where
  /-- `intty "in" range` -- eine Zahl in `lo .. hi`. -/
  | int (lo hi : Int)
  | bool
  /-- `option index into T` -- abwesend, oder ein Index in `0 ..< n`. -/
  | opt (n : Int)
  /-- A closed tagged type, with a complete optional payload type for each case. -/
  | sum (cases : List (Option Ty))
  /-- `reason` -- `n` Gruende. -/
  | why (n : Nat)
  /-- `never` -- der Typ ohne Wert: die Antwort einer `divergent`/`prim` Funktion. -/
  | never
  /-- `f32`/`f64 in lo .. hi` («F») -- die Schranken als Brueche `(z, n)`, weil `0.5` eine
      Schranke ist. Der Wert ist eine ENDLICHE Gleitkommazahl der Maschine im Bereich. -/
  | fl (lo hi : Int × Int)
  /-- `fn(…) -> T effects {…} costs …` -- a function pointer («B8»): the value is a function whose
      own signature CONFORMS to signature number `sig` (`Deklaration.passt`, `SigPasst`; structural
      since 2026-10-21). -/
  | fnptr (sig : Nat)
  /-- `ptr<space, rights> T` -- ein Zeiger auf den Traeger Nummer `t` (M3). Der Wert ist die
      FAEHIGKEIT, `t` anzusprechen; jeder Zugriff hindurch braucht die Waechter von `t`
      wie ein direkter. Zwei Zeiger auf `t` sind damit zwei Namen fuer EINE Welt unter EINEM
      Waechter -- der Alias kostet keine Sicherheit, nur Logik (§15.8). -/
  | ptr (t : Nat) (rw : Bool)
  /-- `index into T` at an open table `T` -- a reference into the OPEN table number `t` (a region without a declared element ceiling,
      `Deklaration.offen`). The value is a cell number without an upper bound. A reference is made ONLY by the program's
      memory provider: the answer of a provider item (`syscall`/`extern`), whose contract (user logic) says the cell
      is fresh. That the provider has memory to give is user logic too (Simon, 2026-10-24: OOM is user logic). G itself makes no reference, and never one
      from an integer. Every access through it carries the guards of `t` like a slot access. -/
  | ref (t : Nat)
  /-- `[T; N]` as a VALUE (2026-10-25, Simon: aggregate values in G, lifting O15): `n` values of `τ`. Passed,
      returned and bound by copy; an element is read and replaced by index. -/
  | arr (τ : Ty) (n : Nat)
  /-- `string max N` as a VALUE (lane 261, in G since 2026-10-25): at most `n` bytes. -/
  | str (n : Nat)
  deriving Repr

/-- Decidable equality for nested payload schemas. Lean's deriving handler does not
    support nested inductives; compare the same finite tree without fuel. -/
mutual

def Ty.decEq : (a b : Ty) → Decidable (a = b)
  | .int a0 a1, .int b0 b1 => by
      if h0 : a0 = b0 then
        subst b0
        if h1 : a1 = b1 then
          subst b1
          exact isTrue rfl
        else exact isFalse (fun h => h1 (by cases h; rfl))
      else exact isFalse (fun h => h0 (by cases h; rfl))
  | .bool, .bool => isTrue rfl
  | .opt a0, .opt b0 => by
      if h0 : a0 = b0 then
        subst b0
        exact isTrue rfl
      else exact isFalse (fun h => h0 (by cases h; rfl))
  | .sum a0, .sum b0 => by
      letI : Decidable (a0 = b0) := Ty.decCases a0 b0
      if h0 : a0 = b0 then
        subst b0
        exact isTrue rfl
      else exact isFalse (fun h => h0 (by cases h; rfl))
  | .why a0, .why b0 => by
      if h0 : a0 = b0 then
        subst b0
        exact isTrue rfl
      else exact isFalse (fun h => h0 (by cases h; rfl))
  | .never, .never => isTrue rfl
  | .fl a0 a1, .fl b0 b1 => by
      if h0 : a0 = b0 then
        subst b0
        if h1 : a1 = b1 then
          subst b1
          exact isTrue rfl
        else exact isFalse (fun h => h1 (by cases h; rfl))
      else exact isFalse (fun h => h0 (by cases h; rfl))
  | .fnptr a0, .fnptr b0 => by
      if h0 : a0 = b0 then
        subst b0
        exact isTrue rfl
      else exact isFalse (fun h => h0 (by cases h; rfl))
  | .ptr a0 a1, .ptr b0 b1 => by
      if h0 : a0 = b0 then
        subst b0
        if h1 : a1 = b1 then
          subst b1
          exact isTrue rfl
        else exact isFalse (fun h => h1 (by cases h; rfl))
      else exact isFalse (fun h => h0 (by cases h; rfl))
  | .ref a0, .ref b0 => by
      if h0 : a0 = b0 then
        subst b0
        exact isTrue rfl
      else exact isFalse (fun h => h0 (by cases h; rfl))
  | .arr a0 a1, .arr b0 b1 => by
      letI : Decidable (a0 = b0) := Ty.decEq a0 b0
      if h0 : a0 = b0 then
        subst b0
        if h1 : a1 = b1 then
          subst b1
          exact isTrue rfl
        else exact isFalse (fun h => h1 (by cases h; rfl))
      else exact isFalse (fun h => h0 (by cases h; rfl))
  | .str a0, .str b0 => by
      if h0 : a0 = b0 then
        subst b0
        exact isTrue rfl
      else exact isFalse (fun h => h0 (by cases h; rfl))
  | .int _ _, .bool => isFalse (by intro h; cases h)
  | .int _ _, .opt _ => isFalse (by intro h; cases h)
  | .int _ _, .sum _ => isFalse (by intro h; cases h)
  | .int _ _, .why _ => isFalse (by intro h; cases h)
  | .int _ _, .never => isFalse (by intro h; cases h)
  | .int _ _, .fl _ _ => isFalse (by intro h; cases h)
  | .int _ _, .fnptr _ => isFalse (by intro h; cases h)
  | .int _ _, .ptr _ _ => isFalse (by intro h; cases h)
  | .int _ _, .ref _ => isFalse (by intro h; cases h)
  | .int _ _, .arr _ _ => isFalse (by intro h; cases h)
  | .int _ _, .str _ => isFalse (by intro h; cases h)
  | .bool, .int _ _ => isFalse (by intro h; cases h)
  | .bool, .opt _ => isFalse (by intro h; cases h)
  | .bool, .sum _ => isFalse (by intro h; cases h)
  | .bool, .why _ => isFalse (by intro h; cases h)
  | .bool, .never => isFalse (by intro h; cases h)
  | .bool, .fl _ _ => isFalse (by intro h; cases h)
  | .bool, .fnptr _ => isFalse (by intro h; cases h)
  | .bool, .ptr _ _ => isFalse (by intro h; cases h)
  | .bool, .ref _ => isFalse (by intro h; cases h)
  | .bool, .arr _ _ => isFalse (by intro h; cases h)
  | .bool, .str _ => isFalse (by intro h; cases h)
  | .opt _, .int _ _ => isFalse (by intro h; cases h)
  | .opt _, .bool => isFalse (by intro h; cases h)
  | .opt _, .sum _ => isFalse (by intro h; cases h)
  | .opt _, .why _ => isFalse (by intro h; cases h)
  | .opt _, .never => isFalse (by intro h; cases h)
  | .opt _, .fl _ _ => isFalse (by intro h; cases h)
  | .opt _, .fnptr _ => isFalse (by intro h; cases h)
  | .opt _, .ptr _ _ => isFalse (by intro h; cases h)
  | .opt _, .ref _ => isFalse (by intro h; cases h)
  | .opt _, .arr _ _ => isFalse (by intro h; cases h)
  | .opt _, .str _ => isFalse (by intro h; cases h)
  | .sum _, .int _ _ => isFalse (by intro h; cases h)
  | .sum _, .bool => isFalse (by intro h; cases h)
  | .sum _, .opt _ => isFalse (by intro h; cases h)
  | .sum _, .why _ => isFalse (by intro h; cases h)
  | .sum _, .never => isFalse (by intro h; cases h)
  | .sum _, .fl _ _ => isFalse (by intro h; cases h)
  | .sum _, .fnptr _ => isFalse (by intro h; cases h)
  | .sum _, .ptr _ _ => isFalse (by intro h; cases h)
  | .sum _, .ref _ => isFalse (by intro h; cases h)
  | .sum _, .arr _ _ => isFalse (by intro h; cases h)
  | .sum _, .str _ => isFalse (by intro h; cases h)
  | .why _, .int _ _ => isFalse (by intro h; cases h)
  | .why _, .bool => isFalse (by intro h; cases h)
  | .why _, .opt _ => isFalse (by intro h; cases h)
  | .why _, .sum _ => isFalse (by intro h; cases h)
  | .why _, .never => isFalse (by intro h; cases h)
  | .why _, .fl _ _ => isFalse (by intro h; cases h)
  | .why _, .fnptr _ => isFalse (by intro h; cases h)
  | .why _, .ptr _ _ => isFalse (by intro h; cases h)
  | .why _, .ref _ => isFalse (by intro h; cases h)
  | .why _, .arr _ _ => isFalse (by intro h; cases h)
  | .why _, .str _ => isFalse (by intro h; cases h)
  | .never, .int _ _ => isFalse (by intro h; cases h)
  | .never, .bool => isFalse (by intro h; cases h)
  | .never, .opt _ => isFalse (by intro h; cases h)
  | .never, .sum _ => isFalse (by intro h; cases h)
  | .never, .why _ => isFalse (by intro h; cases h)
  | .never, .fl _ _ => isFalse (by intro h; cases h)
  | .never, .fnptr _ => isFalse (by intro h; cases h)
  | .never, .ptr _ _ => isFalse (by intro h; cases h)
  | .never, .ref _ => isFalse (by intro h; cases h)
  | .never, .arr _ _ => isFalse (by intro h; cases h)
  | .never, .str _ => isFalse (by intro h; cases h)
  | .fl _ _, .int _ _ => isFalse (by intro h; cases h)
  | .fl _ _, .bool => isFalse (by intro h; cases h)
  | .fl _ _, .opt _ => isFalse (by intro h; cases h)
  | .fl _ _, .sum _ => isFalse (by intro h; cases h)
  | .fl _ _, .why _ => isFalse (by intro h; cases h)
  | .fl _ _, .never => isFalse (by intro h; cases h)
  | .fl _ _, .fnptr _ => isFalse (by intro h; cases h)
  | .fl _ _, .ptr _ _ => isFalse (by intro h; cases h)
  | .fl _ _, .ref _ => isFalse (by intro h; cases h)
  | .fl _ _, .arr _ _ => isFalse (by intro h; cases h)
  | .fl _ _, .str _ => isFalse (by intro h; cases h)
  | .fnptr _, .int _ _ => isFalse (by intro h; cases h)
  | .fnptr _, .bool => isFalse (by intro h; cases h)
  | .fnptr _, .opt _ => isFalse (by intro h; cases h)
  | .fnptr _, .sum _ => isFalse (by intro h; cases h)
  | .fnptr _, .why _ => isFalse (by intro h; cases h)
  | .fnptr _, .never => isFalse (by intro h; cases h)
  | .fnptr _, .fl _ _ => isFalse (by intro h; cases h)
  | .fnptr _, .ptr _ _ => isFalse (by intro h; cases h)
  | .fnptr _, .ref _ => isFalse (by intro h; cases h)
  | .fnptr _, .arr _ _ => isFalse (by intro h; cases h)
  | .fnptr _, .str _ => isFalse (by intro h; cases h)
  | .ptr _ _, .int _ _ => isFalse (by intro h; cases h)
  | .ptr _ _, .bool => isFalse (by intro h; cases h)
  | .ptr _ _, .opt _ => isFalse (by intro h; cases h)
  | .ptr _ _, .sum _ => isFalse (by intro h; cases h)
  | .ptr _ _, .why _ => isFalse (by intro h; cases h)
  | .ptr _ _, .never => isFalse (by intro h; cases h)
  | .ptr _ _, .fl _ _ => isFalse (by intro h; cases h)
  | .ptr _ _, .fnptr _ => isFalse (by intro h; cases h)
  | .ptr _ _, .ref _ => isFalse (by intro h; cases h)
  | .ptr _ _, .arr _ _ => isFalse (by intro h; cases h)
  | .ptr _ _, .str _ => isFalse (by intro h; cases h)
  | .ref _, .int _ _ => isFalse (by intro h; cases h)
  | .ref _, .bool => isFalse (by intro h; cases h)
  | .ref _, .opt _ => isFalse (by intro h; cases h)
  | .ref _, .sum _ => isFalse (by intro h; cases h)
  | .ref _, .why _ => isFalse (by intro h; cases h)
  | .ref _, .never => isFalse (by intro h; cases h)
  | .ref _, .fl _ _ => isFalse (by intro h; cases h)
  | .ref _, .fnptr _ => isFalse (by intro h; cases h)
  | .ref _, .ptr _ _ => isFalse (by intro h; cases h)
  | .ref _, .arr _ _ => isFalse (by intro h; cases h)
  | .ref _, .str _ => isFalse (by intro h; cases h)
  | .arr _ _, .int _ _ => isFalse (by intro h; cases h)
  | .arr _ _, .bool => isFalse (by intro h; cases h)
  | .arr _ _, .opt _ => isFalse (by intro h; cases h)
  | .arr _ _, .sum _ => isFalse (by intro h; cases h)
  | .arr _ _, .why _ => isFalse (by intro h; cases h)
  | .arr _ _, .never => isFalse (by intro h; cases h)
  | .arr _ _, .fl _ _ => isFalse (by intro h; cases h)
  | .arr _ _, .fnptr _ => isFalse (by intro h; cases h)
  | .arr _ _, .ptr _ _ => isFalse (by intro h; cases h)
  | .arr _ _, .ref _ => isFalse (by intro h; cases h)
  | .arr _ _, .str _ => isFalse (by intro h; cases h)
  | .str _, .int _ _ => isFalse (by intro h; cases h)
  | .str _, .bool => isFalse (by intro h; cases h)
  | .str _, .opt _ => isFalse (by intro h; cases h)
  | .str _, .sum _ => isFalse (by intro h; cases h)
  | .str _, .why _ => isFalse (by intro h; cases h)
  | .str _, .never => isFalse (by intro h; cases h)
  | .str _, .fl _ _ => isFalse (by intro h; cases h)
  | .str _, .fnptr _ => isFalse (by intro h; cases h)
  | .str _, .ptr _ _ => isFalse (by intro h; cases h)
  | .str _, .ref _ => isFalse (by intro h; cases h)
  | .str _, .arr _ _ => isFalse (by intro h; cases h)
termination_by a _ => sizeOf a

def Ty.decCases : (as bs : List (Option Ty)) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | a :: as, b :: bs => by
      letI : Decidable (a = b) := Ty.decPayload a b
      letI : Decidable (as = bs) := Ty.decCases as bs
      if h : a = b then
        subst b
        if ht : as = bs then
          subst bs
          exact isTrue rfl
        else exact isFalse (fun h => ht (by cases h; rfl))
      else exact isFalse (fun e => h (by cases e; rfl))
  | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
termination_by as _ => sizeOf as

def Ty.decPayload : (a b : Option Ty) → Decidable (a = b)
  | none, none => isTrue rfl
  | some a, some b => by
      letI : Decidable (a = b) := Ty.decEq a b
      if h : a = b then
        subst b
        exact isTrue rfl
      else exact isFalse (fun e => h (by cases e; rfl))
  | none, some _ | some _, none => isFalse (by intro h; cases h)
termination_by a _ => sizeOf a

end

instance : DecidableEq Ty := Ty.decEq

end Gabbro.Grammatik
