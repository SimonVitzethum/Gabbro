module

public import Grammatik.Parser.Elab.UebersetzeAllg.Teil2

@[expose] public section

/-
  C13: the lowering of the closed integer builtins (`USide.ib1/ib2`) and of the count fold (`UEns.zaehle`) to the
  typed G terms `Expr.intBuiltin1/2` and `Expr.count`.

  Every check the model's typing needs is made HERE, before a term is built: the operand range inside the declared
  operand range (a literal is widened only when its range is included), a bit scan over an operand that excludes
  zero, a shift or rotate amount below the width, a rotate or byte swap over the full word, a byte swap at 16, 32 or
  64 bits, a saturating addition over nested ranges, and a width the declaration did not name. Whatever fails has no
  term: the exporter refuses it by name.
-/

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

/-- A sided term inside the declared operand range `lo .. hi`, by the widening of `Expr.widen`: an operand whose range
    leaves it has no term. -/
def LowSide.passtIn {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (lo hi : Int) (x : LowSide u Γ Λ) :
    Except String (Expr (declOf u) Γ Λ (.int lo hi)) :=
  if h1 : lo ≤ x.range.1 then
    if h2 : x.range.2 ≤ hi then .ok (Expr.widen h1 h2 x.term)
    else .error "builtin operand outside its range"
  else .error "builtin operand outside its range"

/-- A sided term whose range IS `lo .. hi` (a rotate or byte swap works on the whole word). -/
def LowSide.genau {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (lo hi : Int) (x : LowSide u Γ Λ) :
    Except String (Expr (declOf u) Γ Λ (.int lo hi)) :=
  if x.range.1 = lo ∧ x.range.2 = hi then x.passtIn lo hi
  else .error "builtin operand is not the full word"

/-- `a +% b`, `a -% b`, `a *% b` and `a <<% s` at the storage width `W = w + 1`: the operands in `0 .. 2^W - 1`, the
    shift amount in `0 .. w`; the result is the whole unsigned range. -/
def LowSide.wrapW {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (bi : UBi) (W : Nat) (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  match W with
  | 0 => .error "builtin of unknown width"
  | w + 1 =>
    match bi with
    | .shlW =>
      match x.passtIn 0 ((2 : Int) ^ (w + 1) - 1), y.passtIn 0 (w : Int) with
      | .ok a, .ok b =>
        .ok { range := (0, (2 : Int) ^ (w + 1) - 1), term := Expr.intBuiltin2 (IntBuiltin.shlW w) a b }
      | .error e, _ | _, .error e => .error e
    | _ =>
      match x.passtIn 0 ((2 : Int) ^ (w + 1) - 1), y.passtIn 0 ((2 : Int) ^ (w + 1) - 1) with
      | .ok a, .ok b =>
        match bi with
        | .addW => .ok { range := (0, (2 : Int) ^ (w + 1) - 1), term := Expr.intBuiltin2 (IntBuiltin.addW w) a b }
        | .subW => .ok { range := (0, (2 : Int) ^ (w + 1) - 1), term := Expr.intBuiltin2 (IntBuiltin.subW w) a b }
        | .mulW => .ok { range := (0, (2 : Int) ^ (w + 1) - 1), term := Expr.intBuiltin2 (IntBuiltin.mulW w) a b }
        | _ => .error "builtin without a wrapping form"
      | .error e, _ | _, .error e => .error e

/-- `a +| b`: the saturation range is the larger of the two operand ranges when one includes the other (a literal is
    widened to the range of the other operand); operands of crossing ranges have no common declared range. -/
def LowSide.saturiert {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  if x.range.1 ≤ y.range.1 ∧ y.range.2 ≤ x.range.2 then
    match y.passtIn x.range.1 x.range.2 with
    | .ok b => .ok { range := x.range, term := Expr.intBuiltin2 (IntBuiltin.addS x.range.1 x.range.2) x.term b }
    | .error e => .error e
  else if y.range.1 ≤ x.range.1 ∧ x.range.2 ≤ y.range.2 then
    match x.passtIn y.range.1 y.range.2 with
    | .ok a => .ok { range := y.range, term := Expr.intBuiltin2 (IntBuiltin.addS y.range.1 y.range.2) a y.term }
    | .error e => .error e
  else .error "saturating operands of crossing ranges"

/-- `clz`, `ctz`, `log2_floor`, `popcount` at the storage width `W = w + 1`: the scans take an operand whose range
    excludes zero (no CPU zero-case convention), the population count the whole unsigned range. -/
def LowSide.bitZaehl {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (bi : UBi) (W : Nat) (x : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  match W with
  | 0 => .error "builtin of unknown width"
  | w + 1 =>
    match bi with
    | .popcount =>
      match x.passtIn 0 ((2 : Int) ^ (w + 1) - 1) with
      | .ok a => .ok { range := (0, (w : Int) + 1), term := Expr.intBuiltin1 (IntBuiltin.popcount w) a }
      | .error e => .error e
    | _ =>
      if x.range.1 < 1 then .error "bit scan of an operand that may be zero"
      else
        match x.passtIn 1 ((2 : Int) ^ (w + 1) - 1) with
        | .ok a =>
          match bi with
          | .clz => .ok { range := (0, (w : Int)), term := Expr.intBuiltin1 (IntBuiltin.clz w) a }
          | .ctz => .ok { range := (0, (w : Int)), term := Expr.intBuiltin1 (IntBuiltin.ctz w) a }
          | .log2Floor => .ok { range := (0, (w : Int)), term := Expr.intBuiltin1 (IntBuiltin.log2Floor w) a }
          | _ => .error "builtin without a scan form"
        | .error e => .error e

/-- `bswap` of a whole `u16`, `u32` or `u64`. -/
def LowSide.bswapW {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (W : Nat) (x : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  match W with
  | 16 =>
    match x.genau 0 ((2 : Int) ^ 16 - 1) with
    | .ok a => .ok { range := (0, (2 : Int) ^ 16 - 1), term := Expr.intBuiltin1 IntBuiltin.bswap16 a }
    | .error e => .error e
  | 32 =>
    match x.genau 0 ((2 : Int) ^ 32 - 1) with
    | .ok a => .ok { range := (0, (2 : Int) ^ 32 - 1), term := Expr.intBuiltin1 IntBuiltin.bswap32 a }
    | .error e => .error e
  | 64 =>
    match x.genau 0 ((2 : Int) ^ 64 - 1) with
    | .ok a => .ok { range := (0, (2 : Int) ^ 64 - 1), term := Expr.intBuiltin1 IntBuiltin.bswap64 a }
    | .error e => .error e
  | _ => .error "byte swap of an unsupported width"

/-- `rotl`, `rotr` of a whole word at `W = w + 1` by an amount in `0 .. w`. -/
def LowSide.dreh {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (bi : UBi) (W : Nat) (x s : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  match W with
  | 0 => .error "builtin of unknown width"
  | w + 1 =>
    match x.genau 0 ((2 : Int) ^ (w + 1) - 1), s.passtIn 0 (w : Int) with
    | .ok a, .ok b =>
      match bi with
      | .rotl => .ok { range := (0, (2 : Int) ^ (w + 1) - 1), term := Expr.intBuiltin2 (IntBuiltin.rotl w) a b }
      | .rotr => .ok { range := (0, (2 : Int) ^ (w + 1) - 1), term := Expr.intBuiltin2 (IntBuiltin.rotr w) a b }
      | _ => .error "builtin without a rotate form"
    | .error e, _ | _, .error e => .error e

/-- A one-operand builtin of the source. -/
def lowIb1 {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (bi : UBi) (W : Nat) (x : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  match bi with
  | .clz => LowSide.bitZaehl .clz W x
  | .ctz => LowSide.bitZaehl .ctz W x
  | .log2Floor => LowSide.bitZaehl .log2Floor W x
  | .popcount => LowSide.bitZaehl .popcount W x
  | .bswap => LowSide.bswapW W x
  | _ => .error "builtin without one operand"

/-- A two-operand builtin of the source. -/
def lowIb2 {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (bi : UBi) (W : Nat) (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  match bi with
  | .addW => LowSide.wrapW .addW W x y
  | .subW => LowSide.wrapW .subW W x y
  | .mulW => LowSide.wrapW .mulW W x y
  | .shlW => LowSide.wrapW .shlW W x y
  | .addS => LowSide.saturiert x y
  | .rotl => LowSide.dreh .rotl W x y
  | .rotr => LowSide.dreh .rotr W x y
  | _ => .error "builtin without two operands"

/-- The body of a count under the binder of the table's own count `a`, as a body under the binder `0 ..< b`. -/
def umIdx {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {a b : Int} (h : a = b)
    (e : Expr D (Ty.index a :: Γ) Λ .bool) : Expr D (Ty.index b :: Γ) Λ .bool := h ▸ e

/-- A comparison of two sided numbers (the integer branch of `lowCmp`). -/
def lowVglSeiten {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (op : String) (s1 s2 : LowSide u Γ Λ) :
    Except String (Expr (declOf u) Γ Λ .bool) :=
  match op with
  | "==" => .ok (Expr.eq s1.term s2.term)
  | "!=" => .ok (Expr.not (Expr.eq s1.term s2.term))
  | "<" => .ok (Expr.lt s1.term s2.term)
  | "<=" => .ok (Expr.le s1.term s2.term)
  | ">" => .ok (Expr.lt s2.term s1.term)
  | ">=" => .ok (Expr.le s2.term s1.term)
  | _ => .error "operator without G form"

end Gabbro.Grammatik.Parser.UebersetzeAllg
