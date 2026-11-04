module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Parser.Elab.Uebersetze
public import Grammatik.Parser.Elab.UebersetzeAllg.Teil1
public import Grammatik.Parser.Elab.UebersetzeAllg.TableCapabilities

@[expose] public section

namespace Gabbro.Grammatik.Parser.UebersetzeAllg
open Gabbro.Grammatik.Parser.Uebersetze

theorem sigAt_haelt (u : UProg) (i : Fin u.fns.length) :
    (sigAt u i.val).haelt = heldAt u (fnAt u i) := by
  rw [sigAt_get]; rfl

theorem sigAt_konsumiert (u : UProg) (i : Fin u.fns.length) :
    (sigAt u i.val).konsumiert = nimmtAt u (fnAt u i) := by
  rw [sigAt_get]; rfl

theorem sigAt_produziert (u : UProg) (i : Fin u.fns.length) :
    (sigAt u i.val).produziert = gibtAt u (fnAt u i) := by
  rw [sigAt_get]; rfl

/-- Parameters through the declaration. -/
theorem params_eq (u : UProg) (i : Fin u.fns.length) :
    (declOf u).params i = (fnAt u i).params.map (·.2) := by
  simp only [Deklaration.params, declOf, Deklaration.signatur, sigAt_params]

/-- Result through the declaration. -/
theorem erg_eq (u : UProg) (i : Fin u.fns.length) :
    (declOf u).erg i = (fnAt u i).ergTy := by
  simp only [Deklaration.erg, declOf, Deklaration.signatur, sigAt_erg]

/-- Held locks through the declaration. -/
theorem haelt_eq (u : UProg) (i : Fin u.fns.length) :
    (declOf u).haelt i = heldAt u (fnAt u i) := by
  simp only [declOf, Deklaration.haelt, Deklaration.signatur, sigAt_haelt]

/-- **Decided call-boundary escrow (C09/C12).** The callee's owner flow is valid over
    its own inputs at stage 0, disjoint from ordinary consumption, and every
    input resolves to a table owner. Empty flows pass; a borrowing, moving or
    minting callee passes exactly when its loans, handbacks and mints name
    declared table owners nothing else consumes. -/
def ownerReadyB (u : UProg) (S : Signatur (Fin u.tabs.length) (Fin u.globs.length)
    (Fin u.locks.length) (Fin u.marken.length)) : Bool :=
  S.owner.validB (fun m => decide (m ∈ S.owner.inputs.map Prod.fst)) (declOf u).stufen &&
  (S.konsumiert.map Prod.fst).all (fun p => !((S.owner.inputs.map Prod.fst).any (· == p))) &&
  (S.owner.inputs.map Prod.fst).all
    (fun m => (List.finRange u.tabs.length).any (fun t => decide (m ∈ eignerAt u t)))

/-- The decided check supplies the static escrow condition of the call. -/
theorem ownerReadyB_ok (u : UProg) (S : Signatur (Fin u.tabs.length) (Fin u.globs.length)
    (Fin u.locks.length) (Fin u.marken.length)) (h : ownerReadyB u S = true) :
    S.owner.EscrowReady (fun m => decide (m ∈ S.owner.inputs.map Prod.fst))
      (declOf u).stufen (fun m => ∃ t, m ∈ (declOf u).eigner t) S.konsumiert := by
  unfold ownerReadyB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hV, hD⟩, hR⟩ := h
  have hV' := (OwnerFlow.validB_iff _ _ _).mp hV
  refine ⟨hV', ?_, ?_⟩
  · intro p hp
    have hm : p.1 ∈ S.konsumiert.map Prod.fst :=
      List.mem_map.mpr ⟨p, hp, rfl⟩
    have ha := List.all_eq_true.mp hD p.1 hm
    intro hcon
    have hbeq : (S.owner.inputs.map Prod.fst).any (· == p.1) = true := by
      rw [List.any_eq_true]
      exact ⟨p.1, hcon, by simp⟩
    simp only [hbeq, Bool.not_true] at ha
    cases ha
  · intro m hm
    have ha := List.all_eq_true.mp hR m hm
    rw [List.any_eq_true] at ha
    obtain ⟨t, _, ht⟩ := ha
    have member : m ∈ eignerAt u t := of_decide_eq_true ht
    exact ⟨t, member⟩

/-- Every field index has its recorded range. -/
theorem rangeO_some (u : UProg) (t : Fin u.tabs.length)
    (fld : Fin (fieldCount u t)) :
    ∃ w, fieldRangeO u t fld = some w := by
  unfold fieldRangeO
  have hlt : fld.val < (tabAt u t).cols.length := fld.isLt
  rw [List.getElem?_eq_getElem hlt]
  exact ⟨_, rfl⟩

/-- The type of a field that is neither a bool nor an option is the recorded range. -/
theorem typAt_of (u : UProg) (t : Fin u.tabs.length)
    (fld : Fin (fieldCount u t)) (w : Int × Int)
    (h : fieldRangeO u t fld = some w) (hb : boolFeldAt u t fld = false)
    (ho : optFeldAt u t fld = none) (hw : wertFeldAt u t fld = none) :
    typAt u t fld = .int w.1 w.2 := by
  unfold typAt
  rw [hb, ho, hw, h]
  rfl

/-- The type of an aggregate field is its aggregate. -/
theorem typAt_wert (u : UProg) (t : Fin u.tabs.length)
    (fld : Fin (fieldCount u t)) (τ : Ty) (hb : boolFeldAt u t fld = false)
    (ho : optFeldAt u t fld = none) (hw : wertFeldAt u t fld = some τ) :
    typAt u t fld = τ := by
  unfold typAt
  rw [hb, ho, hw]
  rfl

/-- The type of an option field is `opt` of the count of its table. -/
theorem typAt_opt (u : UProg) (t : Fin u.tabs.length)
    (fld : Fin (fieldCount u t)) (n : Int) (hb : boolFeldAt u t fld = false)
    (ho : optFeldAt u t fld = some n) :
    typAt u t fld = .opt n := by
  unfold typAt
  rw [hb, ho]
  rfl

/-- The type of a bool field is `bool`. -/
theorem typAt_bool (u : UProg) (t : Fin u.tabs.length)
    (fld : Fin (fieldCount u t)) (hb : boolFeldAt u t fld = true) :
    typAt u t fld = .bool := by
  unfold typAt
  rw [hb]
  rfl

/-! ## Generic lowering: field search, variables -/

/-- Position of the first field with a name. -/
def fieldPos : List (String × (Int × Int)) → String → Nat
  | [], _ => 0
  | (m, _) :: rest, n => if m == n then 0 else fieldPos rest n + 1

/-- Range of the first field with a name. -/
def fieldAtPos : List (String × (Int × Int)) → String → Option (Int × Int)
  | [], _ => none
  | (m, w) :: rest, n => if m == n then some w else fieldAtPos rest n

/-- A found field is inside the list. -/
theorem fieldPos_lt (fs : List (String × (Int × Int))) (n : String)
    (w : Int × Int) (h : fieldAtPos fs n = some w) :
    fieldPos fs n < fs.length := by
  induction fs with
  | nil => simp only [fieldAtPos, reduceCtorEq] at h
  | cons hd tl ih =>
    cases he : (hd.1 == n) with
    | true =>
      have h1 : fieldPos (hd :: tl) n = 0 := by simp only [fieldPos, he, ↓reduceIte]
      rw [h1]
      exact Nat.zero_lt_succ _
    | false =>
      have h1 : fieldPos (hd :: tl) n = fieldPos tl n + 1 := by
        simp only [fieldPos, he, Bool.false_eq_true, ↓reduceIte, Nat.add_left_cancel_iff]
      have h2 : fieldAtPos (hd :: tl) n = fieldAtPos tl n := by
        simp only [fieldAtPos, he, Bool.false_eq_true, ↓reduceIte]
      rw [h2] at h
      have hi := ih h
      rw [h1]
      show fieldPos tl n + 1 < tl.length + 1
      omega

/-- The range at the found position is the found range. -/
theorem fieldAtPos_get (fs : List (String × (Int × Int))) (n : String)
    (w : Int × Int) (h : fieldAtPos fs n = some w) :
    (fs[fieldPos fs n]?).map (·.2) = some w := by
  induction fs with
  | nil => simp only [fieldAtPos, reduceCtorEq] at h
  | cons hd tl ih =>
    cases he : (hd.1 == n) with
    | true =>
      have h1 : fieldPos (hd :: tl) n = 0 := by simp only [fieldPos, he, ↓reduceIte]
      have h2 : fieldAtPos (hd :: tl) n = some hd.2 := by
        simp only [fieldAtPos, he, ↓reduceIte]
      rw [h2] at h
      rw [h1]
      have g0 : (((hd :: tl)[0]?).map (·.2)) = some hd.2 := rfl
      rw [g0]
      exact h
    | false =>
      have h1 : fieldPos (hd :: tl) n = fieldPos tl n + 1 := by
        simp only [fieldPos, he, Bool.false_eq_true, ↓reduceIte, Nat.add_left_cancel_iff]
      have h2 : fieldAtPos (hd :: tl) n = fieldAtPos tl n := by
        simp only [fieldAtPos, he, Bool.false_eq_true, ↓reduceIte]
      rw [h2] at h
      have ih' := ih h
      rw [h1]
      have g1 : ((hd :: tl)[fieldPos tl n + 1]?) = (tl[fieldPos tl n]?) := rfl
      rw [g1]
      exact ih'

/-- A field hit: the index, its range, and the lookup equation. -/
structure FieldHit (u : UProg) (t : Fin u.tabs.length) where
  idx : Fin (fieldCount u t)
  range : Int × Int
  hit : fieldRangeO u t idx = some range
  /-- The field is a number: its type is the recorded range. -/
  hint : typAt u t idx = .int range.1 range.2

/-- A bool field hit: the index and the fact that its type is `bool`. -/
structure BoolHit (u : UProg) (t : Fin u.tabs.length) where
  idx : Fin (fieldCount u t)
  hbool : typAt u t idx = .bool

/-- Find a field of a table by name. -/
def fieldHit (u : UProg) (t : Fin u.tabs.length) (fname : String) :
    Except String (FieldHit u t) :=
  match h : fieldAtPos (tabAt u t).cols fname with
  | none => .error "field unknown"
  | some w =>
    have hlt : fieldPos (tabAt u t).cols fname < fieldCount u t :=
      fieldPos_lt _ _ _ h
    if hb : boolFeldAt u t ⟨fieldPos (tabAt u t).cols fname, hlt⟩ = false then
      if ho : optFeldAt u t ⟨fieldPos (tabAt u t).cols fname, hlt⟩ = none then
        if hw : wertFeldAt u t ⟨fieldPos (tabAt u t).cols fname, hlt⟩ = none then
          .ok ⟨⟨fieldPos (tabAt u t).cols fname, hlt⟩, w, fieldAtPos_get _ _ _ h,
            typAt_of u t _ w (fieldAtPos_get _ _ _ h) hb ho hw⟩
        else .error "aggregate field as a number"
      else .error "option field as a number"
    else .error "bool field as a number"

/-- An aggregate field hit: the index and its type (`typAt` is the aggregate). -/
def fieldHitW (u : UProg) (t : Fin u.tabs.length) (fname : String) : Option (Fin (fieldCount u t)) :=
  match h : fieldAtPos (tabAt u t).cols fname with
  | none => none
  | some w =>
    have hlt : fieldPos (tabAt u t).cols fname < fieldCount u t := fieldPos_lt _ _ _ h
    if (wertFeldAt u t ⟨fieldPos (tabAt u t).cols fname, hlt⟩).isSome then some ⟨fieldPos (tabAt u t).cols fname, hlt⟩
    else none

/-- An option field hit: the index, the count `n` of its table and the fact that its type is `opt n`. -/
structure OptHit (u : UProg) (t : Fin u.tabs.length) where
  idx : Fin (fieldCount u t)
  n : Int
  hopt : typAt u t idx = .opt n
  /-- The table the option indexes, and that its count is `n`. -/
  tnum : Nat
  hlt : tnum < u.tabs.length
  hcnt : (declOf u).count ⟨tnum, hlt⟩ = n

/-- Find an OPTION field of a table by name. -/
def fieldHitO (u : UProg) (t : Fin u.tabs.length) (fname : String) :
    Except String (OptHit u t) :=
  match h : fieldAtPos (tabAt u t).cols fname with
  | none => .error "field unknown"
  | some _ =>
    have hlt : fieldPos (tabAt u t).cols fname < fieldCount u t :=
      fieldPos_lt _ _ _ h
    if hb : boolFeldAt u t ⟨fieldPos (tabAt u t).cols fname, hlt⟩ = false then
      match ho : optFeldAt u t ⟨fieldPos (tabAt u t).cols fname, hlt⟩ with
      | some n =>
        match optNumAt u t ⟨fieldPos (tabAt u t).cols fname, hlt⟩ with
        | none => .error "option table unknown"
        | some tnum =>
          if hl : tnum < u.tabs.length then
            if hc : (declOf u).count ⟨tnum, hl⟩ = n then
              .ok ⟨⟨fieldPos (tabAt u t).cols fname, hlt⟩, n, typAt_opt u t _ n hb ho, tnum, hl, hc⟩
            else .error "option table count foreign"
          else .error "option table unknown"
      | none => .error "number field as an option"
    else .error "bool field as an option"

/-- Find a BOOL field of a table by name. -/
def fieldHitB (u : UProg) (t : Fin u.tabs.length) (fname : String) :
    Except String (BoolHit u t) :=
  match h : fieldAtPos (tabAt u t).cols fname with
  | none => .error "field unknown"
  | some w =>
    have hlt : fieldPos (tabAt u t).cols fname < fieldCount u t :=
      fieldPos_lt _ _ _ h
    if hb : boolFeldAt u t ⟨fieldPos (tabAt u t).cols fname, hlt⟩ = true then
      .ok ⟨⟨fieldPos (tabAt u t).cols fname, hlt⟩, typAt_bool u t _ hb⟩
    else .error "number field as a truth value"

/-- A variable by position and expected type (the `beq` re-checks the
    context, so a divergent caller is an explicit error). -/
def lowVar : (Γ : Ctx) → (j : Nat) → (τ : Ty) → Except String (Var Γ τ)
  | [], _, _ => .error "parameter outside"
  | σ :: Γ, 0, τ =>
    if h : σ = τ then by rw [h]; exact .ok Var.here
    else .error "parameter shape foreign"
  | _ :: Γ, j + 1, τ =>
    match lowVar Γ j τ with
    | .error e => .error e
    | .ok v => .ok (Var.there v)

/-- Position of a parameter name. -/
def paramPos : List (String × Ty) → String → Except String Nat
  | [], p => .error ("name unknown: " ++ p)
  | (q, _) :: rest, p =>
    if q == p then .ok 0
    else
      match paramPos rest p with
      | .error e => .error e
      | .ok k => .ok (k + 1)

/-! ## Generic lowering: indices, sides, contracts -/

/-- An index into a table: a literal inside `count`, or an index
    parameter of a table of the same count (`sh` shifts parameter positions:
    `0` in a body, `1` in an `ensures` context with a result, where
    the result rides first). -/
def lowIdx (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (t : Fin u.tabs.length) : UIdx →
    Except String (Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
  | .lit n =>
    if h1 : 0 ≤ n then
      if h2 : n ≤ (declOf u).count t - 1 then
        .ok (Expr.widen h1 h2 (Expr.lit n))
      else .error "index outside count"
    else .error "index outside count"
  | .param p =>
    match paramPos fn.params p with
    | .error e => .error e
    | .ok j =>
      match fn.kinds[j]? with
      | some (.index _) =>
        -- an index into a table of the same count is an index into `t` (the model's `Ty.index` is the count)
        match lowVar Γ (sh + j) (.index ((declOf u).count t)) with
        | .error _ => .error "index of foreign table"
        | .ok v => .ok (Expr.var v)
      | some .int =>
        match fn.params[j]? with
        | some (_, .int lo hi) =>
          if h1 : 0 ≤ lo then
            if h2 : hi ≤ (declOf u).count t - 1 then
              match lowVar Γ (sh + j) (.int lo hi) with
              | .error e => .error e
              | .ok v => .ok (Expr.widen h1 h2 (Expr.var v))
            else .error "index outside count"
          else .error "index outside count"
        | _ => .error "index without G form"
      | _ => .error "index without G form"

/-- A sided term with its range. -/
structure LowSide (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) where
  range : Int × Int
  term : Expr (declOf u) Γ Λ (.int range.1 range.2)

/-- Arithmetic on sided terms: the range is what `Expr.add`/`sub`/`mul` carry in their type. -/
def LowSide.plus {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    LowSide u Γ Λ :=
  { range := (x.range.1 + y.range.1, x.range.2 + y.range.2), term := Expr.add x.term y.term }

def LowSide.minus {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    LowSide u Γ Λ :=
  { range := (x.range.1 - y.range.2, x.range.2 - y.range.1), term := Expr.sub x.term y.term }

def LowSide.times {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    LowSide u Γ Λ :=
  { range := (imin (imin (x.range.1 * y.range.1) (x.range.1 * y.range.2))
                  (imin (x.range.2 * y.range.1) (x.range.2 * y.range.2)),
             imax (imax (x.range.1 * y.range.1) (x.range.1 * y.range.2))
                  (imax (x.range.2 * y.range.1) (x.range.2 * y.range.2))),
    term := Expr.mul x.term y.term }

/-- The integer conversion `T(e)`: the widening `Expr.weiter` to the target range, when the
    operand's range fits (as M1 decides it); otherwise the lowering REFUSES. -/
def LowSide.conv {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (lo hi : Int)
    (x : LowSide u Γ Λ) : Except String (LowSide u Γ Λ) :=
  if h1 : lo ≤ x.range.1 then
    if h2 : x.range.2 ≤ hi then .ok { range := (lo, hi), term := Expr.widen h1 h2 x.term }
    else .error "conversion outside target range"
  else .error "conversion outside target range"

/-- `a & b` over non-negative ranges (M137): `Expr.band`, range `0 .. hi(a)`. -/
def LowSide.and {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  if h0 : 0 ≤ x.range.1 then
    if h0' : 0 ≤ y.range.1 then
      .ok { range := (0, x.range.2), term := Expr.band h0 h0' x.term y.term }
    else .error "bit operation over a negative range"
  else .error "bit operation over a negative range"

/-- The number of bits that holds every value up to `m`: `m < 2 ^ bitsFuer m`. -/
def bitsFuer (m : Int) : Nat := Nat.log2 m.toNat + 1

/-- `a | b` over non-negative ranges: `Expr.bor` at the smallest width holding both. The
    result range `0 .. 2^w - 1` contains every value of the bitwise or whatever the width, so the
    narrowest one is sound. -/
def LowSide.or {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  if h0 : 0 ≤ x.range.1 then
    if h0' : 0 ≤ y.range.1 then
      if hw1 : x.range.2 < (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2) then
        if hw2 : y.range.2 < (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2) then
          .ok { range := (0, (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2) - 1),
                term := Expr.bor (bitsFuer (imax x.range.2 y.range.2)) h0 h0' hw1 hw2 x.term y.term }
        else .error "bit operation outside its width"
      else .error "bit operation outside its width"
    else .error "bit operation over a negative range"
  else .error "bit operation over a negative range"

/-- `a ^ b` over non-negative ranges: `Expr.bxor`, like `oder`. -/
def LowSide.xoder {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  if h0 : 0 ≤ x.range.1 then
    if h0' : 0 ≤ y.range.1 then
      if hw1 : x.range.2 < (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2) then
        if hw2 : y.range.2 < (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2) then
          .ok { range := (0, (2 : Int) ^ bitsFuer (imax x.range.2 y.range.2) - 1),
                term := Expr.bxor (bitsFuer (imax x.range.2 y.range.2)) h0 h0' hw1 hw2 x.term y.term }
        else .error "bit operation outside its width"
      else .error "bit operation outside its width"
    else .error "bit operation over a negative range"
  else .error "bit operation over a negative range"

/-- `a / b` (M102): `Expr.div` for a non-negative numerator over a denominator from `1`, else the signed
    `Expr.sdiv` when the denominator excludes zero; a denominator that may be zero has no term. -/
def LowSide.durch {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  if h0 : 0 ≤ x.range.1 then
    if h1 : 1 ≤ y.range.1 then
      .ok { range := (0, x.range.2), term := Expr.div h0 h1 x.term y.term }
    else
      if hb : 1 ≤ y.range.1 ∨ y.range.2 ≤ -1 then
        .ok { range := (-(betragMax x.range.1 x.range.2), betragMax x.range.1 x.range.2),
              term := Expr.sdiv hb x.term y.term }
      else .error "division by a denominator that may be zero"
  else
    if hb : 1 ≤ y.range.1 ∨ y.range.2 ≤ -1 then
      .ok { range := (-(betragMax x.range.1 x.range.2), betragMax x.range.1 x.range.2),
            term := Expr.sdiv hb x.term y.term }
    else .error "division by a denominator that may be zero"

/-- `a % b`: `Expr.rem`, or the signed `Expr.srem`, under the same conditions as `/`. -/
def LowSide.rest {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  if h0 : 0 ≤ x.range.1 then
    if h1 : 1 ≤ y.range.1 then
      .ok { range := (0, y.range.2 - 1), term := Expr.rem h0 h1 x.term y.term }
    else
      if hb : 1 ≤ y.range.1 ∨ y.range.2 ≤ -1 then
        .ok { range := (-(betragMax y.range.1 y.range.2 - 1), betragMax y.range.1 y.range.2 - 1),
              term := Expr.srem hb x.term y.term }
      else .error "division by a denominator that may be zero"
  else
    if hb : 1 ≤ y.range.1 ∨ y.range.2 ≤ -1 then
      .ok { range := (-(betragMax y.range.1 y.range.2 - 1), betragMax y.range.1 y.range.2 - 1),
            term := Expr.srem hb x.term y.term }
    else .error "division by a denominator that may be zero"

/-- The width a shift of `x` by `y` names: the smallest that holds the operand and exceeds the amount. -/
def schiebeBreite (x y : Int × Int) : Nat := max (bitsFuer x.2) (y.2.toNat + 1)

/-- `a << b` over non-negative ranges (M137): `Expr.shl` at the width `schiebeBreite`. A shift amount beyond 4096
    gives a result range no type holds (and `2 ^ n` would not be computed): refused as a value outside any range. -/
def LowSide.links {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  if 4096 < y.range.2 then .error "value outside range"
  else if h0 : 0 ≤ x.range.1 then
    if h0' : 0 ≤ y.range.1 then
      if hw1 : x.range.2 < (2 : Int) ^ schiebeBreite x.range y.range then
        if hw2 : y.range.2 < ((schiebeBreite x.range y.range : Nat) : Int) then
          .ok { range := (0, x.range.2 * 2 ^ y.range.2.toNat),
                term := Expr.shl (schiebeBreite x.range y.range) hw1 hw2 h0 h0' x.term y.term }
        else .error "shift outside its width"
      else .error "shift outside its width"
    else .error "bit operation over a negative range"
  else .error "bit operation over a negative range"

/-- `a >> b`: `Expr.shr`, range `0 .. hi(a)`. -/
def LowSide.rechts {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  if 4096 < y.range.2 then .error "value outside range"
  else if h0 : 0 ≤ x.range.1 then
    if h0' : 0 ≤ y.range.1 then
      if hw1 : x.range.2 < (2 : Int) ^ schiebeBreite x.range y.range then
        if hw2 : y.range.2 < ((schiebeBreite x.range y.range : Nat) : Int) then
          .ok { range := (0, x.range.2),
                term := Expr.shr (schiebeBreite x.range y.range) hw1 hw2 h0 h0' x.term y.term }
        else .error "shift outside its width"
      else .error "shift outside its width"
    else .error "bit operation over a negative range"
  else .error "bit operation over a negative range"

end Gabbro.Grammatik.Parser.UebersetzeAllg
