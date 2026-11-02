module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Parser.Elab.Uebersetze
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil2

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

/-- `-a`: `Expr.neg`. -/
def LowSide.minusEins {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x : LowSide u Γ Λ) :
    LowSide u Γ Λ :=
  { range := (-x.range.2, -x.range.1), term := Expr.neg x.term }

/-- Two lowered operands into one lowered result (the first error wins). -/
def lowZwei {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))}
    (f : LowSide u Γ Λ → LowSide u Γ Λ → Except String (LowSide u Γ Λ))
    (a b : Except String (LowSide u Γ Λ)) : Except String (LowSide u Γ Λ) :=
  match a with
  | .error e => .error e
  | .ok x =>
    match b with
    | .error e => .error e
    | .ok y => f x y

/-- The table a basis names: a pointer parameter's target, or a
    table (for `old`, where both spellings travel). -/
def lowBasisTab (u : UProg) (fn : UFn) (b : String) :
    Except String (Fin u.tabs.length) :=
  match paramPos fn.params b with
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr ⟨0, ⟨true, _, none⟩, .table num⟩) =>
      if h : num < u.tabs.length then .ok ⟨num, h⟩
      else .error "pointer table unknown"
    | _ => .error "place without G form"
  | .error _ =>
    match tabIdx u.tabs b with
    | .ok t => .ok t
    | .error e => .error e

/-- A numeric parameter as a side (positions shift by `sh`,
    see `lowIdx`). -/
def lowParamSide (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (p : String) :
    Except String (LowSide u Γ Λ) :=
  match paramPos fn.params p with
  | .error e => .error e
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr _) => .error "pointer as value without G form"
    | some _ =>
      match fn.params[j]? with
      | some (_, .int a b) =>
        match lowVar Γ (sh + j) (.int a b) with
        | .error e => .error e
        | .ok v => .ok { range := (a, b), term := Expr.var v }
      | _ => .error "parameter without G form"
    | none => .error "parameter without G form"

/-- A `durch` term at its recorded range (the `rw` turns the
    goal into the field type, where the constructor fits). -/
def durchTerm (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (num : Nat) (w : Bool) (h : num < u.tabs.length)
    (fh : FieldHit u ⟨num, h⟩) (v : Var Γ (.ptr (.table num (true, w))))
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count ⟨num, h⟩)))
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
      Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2) := by
  rw [← fh.hint]
  exact Expr.thru (D := declOf u) (Expr.var v) ⟨num, h⟩
    (capTab_some u num h) fh.idx i hL

/-- A `slot` term at its recorded range. -/
def slotTerm (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (t : Fin u.tabs.length) (fh : FieldHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2) := by
  rw [← fh.hint]
  exact Expr.slot (D := declOf u) t fh.idx i hL

/-- An `altSlot` term at its recorded range. -/
def altTerm (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (t : Fin u.tabs.length) (fh : FieldHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2) := by
  rw [← fh.hint]
  exact Expr.oldS (D := declOf u) t fh.idx i hL

/-- A slot read through a pointer parameter (positions shift
    by `sh`, see `lowIdx`). -/
def lowDurch (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (b fname : String) (ix : UIdx) :
    Except String (LowSide u Γ Λ) :=
  match paramPos fn.params b with
  | .error e => .error e
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr (.table num (true, w))) =>
      if h : num < u.tabs.length then
        match fieldHit u ⟨num, h⟩ fname with
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
                .ok { range := fh.range, term := durchTerm u Γ Λ num w h fh v i hL }
              else .error "access without held guard"
      else .error "pointer table unknown"
    | _ => .error "place without G form"

/-- A field read through a reference into an open table, at the field's recorded range. -/
def refTerm (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (num : Nat) (h : num < u.tabs.length) (ho : (declOf u).offen ⟨num, h⟩ = true)
    (fh : FieldHit u ⟨num, h⟩) (v : Var Γ (.ref num))
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2) := by
  rw [← fh.hint]
  exact Expr.slotRef (D := declOf u) (Expr.var v) ⟨num, h⟩ (tabNr_some u num h) ho fh.idx hL

/-- `r->f`: a field read through a reference local `r` (positions shift by `sh`). -/
def lowRefRead (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (r fname : String) :
    Except String (LowSide u Γ Λ) :=
  match paramPos fn.params r with
  | .error e => .error e
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ref num) =>
      if h : num < u.tabs.length then
        if ho : (declOf u).offen ⟨num, h⟩ = true then
          match fieldHit u ⟨num, h⟩ fname with
          | .error e => .error e
          | .ok fh =>
            match lowVar Γ (sh + j) (.ref num) with
            | .error e => .error e
            | .ok v =>
              if hL : (∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
                  Res.von (declOf u) wdd ∈ Λ) then
                .ok { range := fh.range, term := refTerm u Γ Λ num h ho fh v hL }
              else .error "access without held guard"
        else .error "reference into a table that is not open"
      else .error "reference table unknown"
    | _ => .error "place without G form"

/-- A slot read at a table (positions shift by `sh`). -/
def lowTabRead (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (b fname : String) (ix : UIdx) :
    Except String (LowSide u Γ Λ) :=
  match tabIdx u.tabs b with
  | .error e => .error e
  | .ok t =>
    match fieldHit u t fname with
    | .error e => .error e
    | .ok fh =>
      match lowIdx u Γ Λ fn sh t ix with
      | .error e => .error e
      | .ok i =>
        if hL : (∀ wdd ∈ (declOf u).braucht t,
            Res.von (declOf u) wdd ∈ Λ) then
          .ok { range := fh.range, term := slotTerm u Γ Λ t fh i hL }
        else .error "access without held guard"

/-- An entry read (`old`) at a resolved table (positions
    shift by `sh`). -/
def lowAltRead (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (b fname : String) (ix : UIdx) :
    Except String (LowSide u Γ Λ) :=
  match lowBasisTab u fn b with
  | .error e => .error e
  | .ok t =>
    match fieldHit u t fname with
    | .error e => .error e
    | .ok fh =>
      match lowIdx u Γ Λ fn sh t ix with
      | .error e => .error e
      | .ok i =>
        if hL : (∀ wdd ∈ (declOf u).braucht t,
            Res.von (declOf u) wdd ∈ Λ) then
          .ok { range := fh.range, term := altTerm u Γ Λ t fh i hL }
        else .error "access without held guard"

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

/-- The bytes of a string literal as values of `0 .. 255`. -/
def bytesZahl : List Int → Option (List (Zahl 0 255))
  | [] => some []
  | b :: bs =>
    if h : 0 ≤ b ∧ b ≤ 255 then (bytesZahl bs).map (⟨b, h.1, h.2⟩ :: ·) else none

theorem bytesZahl_laenge : ∀ (bs : List Int) (zs : List (Zahl 0 255)), bytesZahl bs = some zs → zs.length = bs.length
  | [], zs, h => by simp only [bytesZahl, Option.some.injEq] at h; subst h; rfl
  | b :: bs, zs, h => by
    unfold bytesZahl at h
    split at h
    · cases hz : bytesZahl bs with
      | none => rw [hz] at h; cases h
      | some ys =>
        rw [hz] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        simp only [List.length_cons, bytesZahl_laenge bs ys hz]
    · cases h

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
