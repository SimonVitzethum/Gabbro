module

public import Grammatik.Parser.Elab.UebersetzeAllg.Teil3Basis

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

/-- A number static read (`Expr.glob`): its type is the recorded range. -/
def lowGlobSide (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (p : String) :
    Except String (LowSide u Γ Λ) :=
  match globIdx u.globs p with
  | .error e => .error e
  | .ok g =>
    if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
    match h : (globAt u g).ty with
    | .int lo hi =>
      .ok { range := (lo, hi), term := by
              have hg : (declOf u).gtyp g = .int lo hi := by
                show (globAt u g).ty.toTy = _
                rw [h]
                rfl
              show Expr (declOf u) Γ Λ (.int lo hi)
              rw [← hg]
              exact Expr.glob (D := declOf u) g hd }
    | .bool => .error "bool static as a number"
    | .wert _ => .error "aggregate static as a number"
    else .error "access without held guard"

/-- A `bool` static read as a truth value. -/
def lowGlobBool (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (p : String) :
    Except String (Expr (declOf u) Γ Λ .bool) :=
  match globIdx u.globs p with
  | .error e => .error e
  | .ok g =>
    if hd : (∀ w ∈ (declOf u).gbraucht g, Res.von (declOf u) w ∈ Λ) then
    match h : (globAt u g).ty with
    | .bool =>
      .ok (by
        have hg : (declOf u).gtyp g = .bool := by
          show (globAt u g).ty.toTy = _
          rw [h]
          rfl
        rw [← hg]
        exact Expr.glob (D := declOf u) g hd)
    | .int _ _ => .error "number static as a truth value"
    | .wert _ => .error "aggregate static as a truth value"
    else .error "access without held guard"

/-- A `bool` slot read through a pointer parameter (positions shift by `sh`): the place's truth value. -/
def lowBoolDurch (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (b fname : String) (ix : UIdx) :
    Except String (Expr (declOf u) Γ Λ .bool) :=
  match paramPos fn.params b with
  | .error e => .error e
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr (.table num (true, w))) =>
      if h : num < u.tabs.length then
        match fieldHitB u ⟨num, h⟩ fname with
        | .error e => .error e
        | .ok fh =>
          match lowVar Γ (sh + j) (.ptr (.table num (true, w))) with
          | .error e => .error e
          | .ok v =>
            match lowIdx u Γ Λ fn sh ⟨num, h⟩ ix with
            | .error e => .error e
            | .ok i =>
              if hL : (∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
                  Res.von (declOf u) wdd ∈ Λ) then
                .ok (by
                  rw [← fh.hbool]
                  exact Expr.thru (D := declOf u) (Expr.var v) ⟨num, h⟩
                    (capTab_some u num h) fh.idx i hL)
              else .error "access without held guard"
      else .error "pointer table unknown"
    | some (.ptr ⟨0, ⟨true, w, some owner⟩, .table num⟩) =>
      if h : num < u.tabs.length then
        match fieldHitB u ⟨num, h⟩ fname with
        | .error e => .error e
        | .ok fh =>
          match heig : eignerMarke u owner with
          | .none => .error "owned read without a declared owner mark"
          | .some m =>
            match lowVar Γ (sh + j) (.ptr ⟨0, ⟨true, w, some owner⟩, .table num⟩) with
            | .error e => .error e
            | .ok v =>
              match lowIdx u Γ Λ fn sh ⟨num, h⟩ ix with
              | .error e => .error e
              | .ok i =>
                if hL : (∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
                    Res.von (declOf u) wdd ∈ Λ) then
                  if he : m ∈ eignerAt u ⟨num, h⟩ then
                    .ok (durchOwnTermB u Γ Λ num w h fh owner m v i heig he hL)
                  else .error "owned read without owner guard"
                else .error "access without held guard"
      else .error "pointer table unknown"
    | _ => .error "place without G form"

/-- A `bool` slot read at a table. -/
def lowBoolTab (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (b fname : String) (ix : UIdx) :
    Except String (Expr (declOf u) Γ Λ .bool) :=
  match tabIdx u.tabs b with
  | .error e => .error e
  | .ok t =>
    match fieldHitB u t fname with
    | .error e => .error e
    | .ok fh =>
      match lowIdx u Γ Λ fn sh t ix with
      | .error e => .error e
      | .ok i =>
        if hL : (∀ wdd ∈ (declOf u).braucht t,
            Res.von (declOf u) wdd ∈ Λ) then
          .ok (by
            rw [← fh.hbool]
            exact Expr.slot (D := declOf u) t fh.idx i hL)
        else .error "access without held guard"

/-- The result kind retains its declaration identity, particularly options/tags/reasons. -/
def resultKind (fn : UFn) : Ty → Except String UParamArt
  | .int .. => .ok .int
  | .bool => .ok .bool
  | .opt n =>
    match fn.resOpt with
    | some (num, count) => if n == count then .ok (.opt num) else .error "result option count mismatch"
    | none => .error "result option identity missing"
  | .sum cases =>
    match fn.resSum with
    | some (num, spec) => if cases == spec then .ok (.sum num) else .error "result tag cases mismatch"
    | none => .error "result tag identity missing"
  | .why n =>
    match fn.resWhy with
    | some (num, count) => if n == count then .ok (.why num) else .error "result reason count mismatch"
    | none => .error "result reason identity missing"
  | .ptr cap => .ok (.ptr cap)
  | .fnptr num => .ok (.fnptr num)
  | .ref num => .ok (.ref num)
  | _ => .error "quantifier beside a result of this type without G form"

/-- Only the newly represented result kinds require the original-source duty gate. -/
def resultContextGate (u : UProg) : Option Ty → Except String Unit
  | none | some (.int ..) | some .bool => .ok ()
  | _ => u.exportGate

/-- The result of an `ensures` as a parameter `#erg` in front of the others (a name no source can write): inside a
    quantifier the binder rides in front of the result, so the result is found by its name, not at position 0. -/
def ergAlsParam (u : UProg) (fn : UFn) : Option Ty → Except String UFn
  | none => .ok fn
  | some ty => do
    let kind ← resultKind fn ty
    resultContextGate u (some ty)
    pure {fn with params := ("#erg", ty) :: fn.params, kinds := kind :: fn.kinds}

/-! ### Aggregate values (`Ty.arr`, `Ty.str`, 2026-10-25)

A value of any type with its term: arrays and strings are lowered by their type, which travels with the term
(`lowWertE`); a number keeps the range the integer lowering gives it. -/

/-- A term with its type. -/
structure LowWert (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) where
  ty : Ty
  term : Expr (declOf u) Γ Λ ty

/-- A number as a value. -/
def LowSide.wert {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x : LowSide u Γ Λ) : LowWert u Γ Λ :=
  ⟨.int x.range.1 x.range.2, x.term⟩

/-- A value that is a number. -/
def LowWert.zahl {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} : LowWert u Γ Λ → Except String (LowSide u Γ Λ)
  | ⟨.int a b, t⟩ => .ok { range := (a, b), term := t }
  | _ => .error "aggregate as a number"

/-- A string literal at the type of its own length. -/
def lowText {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (bs : List Int) : Except String (LowWert u Γ Λ) :=
  match bytesZahl bs with
  | some zs => .ok ⟨.str zs.length, Expr.strLit zs (Nat.le_refl _)⟩
  | none => .error "string literal outside bytes"

/-- `a[i]`: an element of an array (the index fitted into `0 ..< n`) or a byte of a string. -/
def idxW {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} :
    LowWert u Γ Λ → LowSide u Γ Λ → Except String (LowWert u Γ Λ)
  | ⟨.arr τ n, t⟩, i =>
    if h1 : 0 ≤ i.range.1 then
      if h2 : i.range.2 ≤ (n : Int) - 1 then .ok ⟨τ, Expr.arrGet t (Expr.widen h1 h2 i.term)⟩
      else .error "index outside the array"
    else .error "index outside the array"
  | ⟨.str _, t⟩, i => .ok ⟨.int 0 255, Expr.strGet t i.term⟩
  | _, _ => .error "index of a value without elements"

/-- `lenof(a)`: the length of a string, the (constant) length of an array. -/
def lenW {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} : LowWert u Γ Λ → Except String (LowWert u Γ Λ)
  | ⟨.str n, t⟩ => .ok ⟨.int 0 n, Expr.strLen t⟩
  | ⟨.arr _ n, _⟩ => .ok ⟨.int n n, Expr.lit n⟩
  | _ => .error "lenof of a value without length"

/-- A value fitted to the type `τ`: the same type, a number widened into a larger range, a string under a larger
    maximum; everything else is refused. -/
def fitW {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (τ : Ty) (w : LowWert u Γ Λ) :
    Except String (Expr (declOf u) Γ Λ τ) :=
  if h : w.ty = τ then .ok (h ▸ w.term) else
  match w, τ with
  | ⟨.int a b, t⟩, .int lo hi =>
    if h1 : lo ≤ a then
      if h2 : b ≤ hi then .ok (Expr.widen h1 h2 t) else .error "value outside range"
    else .error "value outside range"
  | ⟨.str n, t⟩, .str m => if n ≤ m then .ok (Expr.strWeit m t) else .error "string longer than the maximum"
  | _, _ => .error "value of another type"

/-- `a[i] = v` on an array value: the array with the element replaced. -/
def updW {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} :
    LowWert u Γ Λ → LowSide u Γ Λ → LowWert u Γ Λ → Except String (LowWert u Γ Λ)
  | ⟨.arr τ n, t⟩, i, v =>
    if h1 : 0 ≤ i.range.1 then
      if h2 : i.range.2 ≤ (n : Int) - 1 then
        match fitW τ v with
        | .ok v' => .ok ⟨.arr τ n, Expr.arrSet t (Expr.widen h1 h2 i.term) v'⟩
        | .error e => .error e
      else .error "index outside the array"
    else .error "index outside the array"
  | _, _, _ => .error "element write into a value without elements"

/-- `s + t` on two strings, the maximum the sum of the maxima. -/
def catW {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} :
    LowWert u Γ Λ → LowWert u Γ Λ → Except String (LowWert u Γ Λ)
  | ⟨.str n, s⟩, ⟨.str m, t⟩ => .ok ⟨.str (n + m), Expr.strCat s t⟩
  | ⟨.int .., _⟩, _ | _, ⟨.int .., _⟩ => .error "number added to an aggregate"
  | _, _ => .error "addition of aggregates without G form"

/-- `[a, rest…]`: the element in front of an array of its type. -/
def consW {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} :
    LowWert u Γ Λ → LowWert u Γ Λ → Except String (LowWert u Γ Λ)
  | a, ⟨.arr τ n, r⟩ =>
    match fitW τ a with
    | .ok a' => .ok ⟨.arr τ (n + 1), Expr.arrCons a' r⟩
    | .error e => .error e
  | _, _ => .error "array literal without G form"

/-- An aggregate parameter or local (a number or any other kind goes to the integer lowering). -/
def lowParamWert (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (fn : UFn) (sh : Nat) (p : String) :
    Option (Except String (LowWert u Γ Λ)) :=
  match paramPos fn.params p with
  | .error _ => none
  | .ok j =>
    match fn.kinds[j]?, fn.params[j]? with
    | some .wert, some (_, τ) | _, some (_, τ@Ty.never) =>
      some (match lowVar Γ (sh + j) τ with
        | .error e => .error e
        | .ok v => .ok ⟨τ, Expr.var v⟩)
    | some (.ref region), some (_, .ref declared) =>
      some (do
        u.exportGate
        if same : region = declared then
          match lowVar Γ (sh + j) (.ref region) with
          | .error error => .error error
          | .ok reference => .ok ⟨.ref region, Expr.var reference⟩
        else .error "source export: reference origin disagrees with its declared region")
    | _, some (_, τ) =>
      match τ with
      | .int .. | .ref _ => none
      | _ => some (match lowVar Γ (sh + j) τ with
        | .error e => .error e
        | .ok v => .ok ⟨τ, Expr.var v⟩)
    | _, _ => none

/-- A named function uses the declaration's existing signature-conformance check. -/
def lowFnRef (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) (signature : Nat) (name : String) :
    Except String (Expr (declOf u) Γ Λ (.fnptr signature)) := do
  let target ← fnIdx u.fns name
  if fits : (declOf u).passt target signature = true then
    pure (Expr.fnref (D := declOf u) target signature fits)
  else .error "function does not conform to the pointer type"

end Gabbro.Grammatik.Parser.UebersetzeAllg
