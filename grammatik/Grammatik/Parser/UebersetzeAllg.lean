/-
  File:      Grammatik/Parser/UebersetzeAllg.lean
  Subject:   T3 PART 5: generic lowering from source to the G program.

  Lane 160 (`Parser/Uebersetze.lean`) elaborates the parsed surface tree
  to plain data (`UProg`) generically, but lowers only onto the 104
  declaration universe (`G104_referenz.gD`). This file builds the
  declaration from the `UProg` itself, with index carriers (`Fin n`
  for tables, locks, fields and functions): `declOf : UProg ->
  Deklaration` and `lowerAllg : (u : UProg) -> Except String
  (Programm (declOf u) x List (declOf u).Fn)`.

  The 104 and 108 instances pin the fragment and footprint checks on
  the generically lowered programs (`by decide`), the data agreement
  with the exporter programs, the real-text lexer pin (comments lex
  away, no lexer change was needed), and one theorem chaining all
  stages for 104.
-/
import Grammatik.Parser.Uebersetze

namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Gabbro.Grammatik.Parser.Uebersetze

/-! ## Declaration data looked up from `UProg` -/

/-- The table at an index. -/
def tabAt (u : UProg) (t : Fin u.tabellen.length) : UTab :=
  u.tabellen.get t

/-- The lock at an index. -/
def lockAt (u : UProg) (l : Fin u.sperren.length) : ULock :=
  u.sperren.get l

/-- The function at an index. -/
def fnAt (u : UProg) (f : Fin u.fns.length) : UFn :=
  u.fns.get f

/-- The field count of a table. -/
def fieldCount (u : UProg) (t : Fin u.tabellen.length) : Nat :=
  (tabAt u t).felder.length

/-- A table index by name (structural, so the `Fin` proof is free). -/
def tabIdx : (tabs : List UTab) → (n : String) → Except String (Fin tabs.length)
  | [], n => .error ("table unknown: " ++ n)
  | t :: rest, n =>
    if t.name == n then .ok 0
    else match tabIdx rest n with
      | .error e => .error e
      | .ok j => .ok j.succ

/-- A lock index by name. -/
def lockIdx : (locks : List ULock) → (n : String) → Except String (Fin locks.length)
  | [], n => .error ("lock unknown: " ++ n)
  | l :: rest, n =>
    if l.name == n then .ok 0
    else match lockIdx rest n with
      | .error e => .error e
      | .ok j => .ok j.succ

/-- A function index by name. -/
def fnIdx : (fns : List UFn) → (n : String) → Except String (Fin fns.length)
  | [], n => .error ("function unknown: " ++ n)
  | f :: rest, n =>
    if f.name == n then .ok 0
    else match fnIdx rest n with
      | .error e => .error e
      | .ok j => .ok j.succ

/-- A field range by table and field index (`some` always: the
    index is inside the table's field list). -/
def fieldRangeO (u : UProg) (t : Fin u.tabellen.length)
    (f : Fin (fieldCount u t)) : Option (Int × Int) :=
  ((tabAt u t).felder[f.val]?).map (·.2)

/-- The field type: the recorded range, or `.int 0 0` off the table
    (unreachable through `fieldRangeO`, kept for totality). -/
def typAt (u : UProg) (t : Fin u.tabellen.length)
    (f : Fin (fieldCount u t)) : Ty :=
  match fieldRangeO u t f with
  | some w => .int w.1 w.2
  | none => .int 0 0

/-- The guards of a table: the locks whose `schutz` names it. -/
def needsAt (u : UProg) (t : Fin u.tabellen.length) :
    List (Fin u.sperren.length ⊕ (Empty × Nat)) :=
  List.finRange u.sperren.length |>.filterMap fun l =>
    if (lockAt u l).schutz.any (· == (tabAt u t).name) then some (.inl l)
    else none

/-- The held locks of a function, as indices (names the declaration
    does not know are dropped; `elabU` output never has them). -/
def heldAt (u : UProg) (f : UFn) : List (Fin u.sperren.length) :=
  f.held.filterMap fun n => (lockIdx u.sperren n).toOption

/-- The write flag of a function at a table. -/
def writesAt (u : UProg) (f : UFn) (t : Fin u.tabellen.length) : Bool :=
  f.schreibt.any (· == (tabAt u t).name)

/-- The signature of an elaborated function. -/
def mkSig (u : UProg) (f : UFn) :
    Signatur (Fin u.tabellen.length) Empty (Fin u.sperren.length) Empty where
  params := f.params.map (·.2)
  erg := f.ergebnis.map fun r => .int r.1 r.2
  gruende := 0
  haelt := heldAt u f
  schreibt := writesAt u f
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The dummy signature: no parameters, no rights. -/
def dummySig (u : UProg) :
    Signatur (Fin u.tabellen.length) Empty (Fin u.sperren.length) Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun e => nomatch e
  konsumiert := []
  produziert := []

/-- The `n`th signature, or the dummy (an out-of-range number names
    no function). -/
def sigAt (u : UProg) (n : Nat) :
    Signatur (Fin u.tabellen.length) Empty (Fin u.sperren.length) Empty :=
  if h : n < u.fns.length then mkSig u (u.fns.get ⟨n, h⟩) else dummySig u

/-- A non-empty emptiness test means a non-empty list. -/
theorem notEmpty_ne_nil (l : List α) (h : (!l.isEmpty) = true) :
    l ≠ [] := by
  cases l with
  | nil => simp at h
  | cons _ _ => simp

/-- The declaration built from the elaborated program itself: index
    carriers (`Fin`) for tables, locks, fields and functions; no
    globals, marks, invariants, axioms, registers or assumptions. -/
def declOf (u : UProg) : Deklaration where
  Tab := Fin u.tabellen.length
  decTab := inferInstance
  count := fun t => (tabAt u t).count
  Feld := fun t => Fin (fieldCount u t)
  decFeld := fun _ => inferInstance
  typ := typAt u
  erlaubt := fun _ _ _ _ => false
  tabNr := fun n => if h : n < u.tabellen.length then some ⟨n, h⟩ else none
  Glob := Empty
  decGlob := inferInstance
  gtyp := fun e => nomatch e
  nutzlast := fun e => nomatch e
  atomar := fun e => nomatch e
  geteilt := fun t => (!((needsAt u t).isEmpty))
  ggeteilt := fun e => nomatch e
  Lock := Fin u.sperren.length
  decLock := inferInstance
  rang := fun l => (lockAt u l).rank
  maskiert := fun _ => false
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := needsAt u
  gbraucht := fun e => nomatch e
  eigner := fun _ => []
  Fn := Fin u.fns.length
  sig := fun f => f.val
  sigNr := sigAt u
  eigner_nie_erzeugt :=
    fun _ _ _ _ h => (List.not_mem_nil (show _ ∈ ([] : List Empty) from h)).elim
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht :=
    fun t h => notEmpty_ne_nil _ (show ((!((needsAt u t).isEmpty)) = true) from h)
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun e => nomatch e

/-! ## Bridge lemmas: the computed declaration meets the U data -/

/-- `sigAt` at a live index is the elaborated signature. -/
theorem sigAt_get (u : UProg) (i : Fin u.fns.length) :
    sigAt u i.val = mkSig u (fnAt u i) := by
  unfold sigAt fnAt
  rw [dif_pos i.isLt, Fin.eta i i.isLt]

/-- Projections of `sigAt` at a live index. -/
theorem sigAt_params (u : UProg) (i : Fin u.fns.length) :
    (sigAt u i.val).params = (fnAt u i).params.map (·.2) := by
  rw [sigAt_get]; rfl

theorem sigAt_erg (u : UProg) (i : Fin u.fns.length) :
    (sigAt u i.val).erg = (fnAt u i).ergebnis.map fun r => .int r.1 r.2 := by
  rw [sigAt_get]; rfl

theorem sigAt_haelt (u : UProg) (i : Fin u.fns.length) :
    (sigAt u i.val).haelt = heldAt u (fnAt u i) := by
  rw [sigAt_get]; rfl

theorem sigAt_konsumiert (u : UProg) (i : Fin u.fns.length) :
    (sigAt u i.val).konsumiert = [] := by
  rw [sigAt_get]; rfl

theorem sigAt_produziert (u : UProg) (i : Fin u.fns.length) :
    (sigAt u i.val).produziert = [] := by
  rw [sigAt_get]; rfl

/-- Parameters through the declaration. -/
theorem params_eq (u : UProg) (i : Fin u.fns.length) :
    (declOf u).params i = (fnAt u i).params.map (·.2) := by
  simp [Deklaration.params, Deklaration.signatur, declOf, sigAt_params]

/-- Result through the declaration. -/
theorem erg_eq (u : UProg) (i : Fin u.fns.length) :
    (declOf u).erg i =
      (fnAt u i).ergebnis.map fun r => .int r.1 r.2 := by
  simp [Deklaration.erg, Deklaration.signatur, declOf, sigAt_erg]

/-- Held locks through the declaration. -/
theorem haelt_eq (u : UProg) (i : Fin u.fns.length) :
    (declOf u).haelt i = heldAt u (fnAt u i) := by
  simp [Deklaration.haelt, Deklaration.signatur, declOf, sigAt_haelt]

/-- The contract end: held locks only (no marks travel). -/
theorem ende_eq (u : UProg) (f : Fin u.fns.length) :
    (vertragVon (declOf u) f).ende =
      (heldAt u (fnAt u f)).map (Res.held (D := declOf u)) := by
  simp only [vertragVon, Vertrag.vonSig, Vertrag.ende, Deklaration.signatur,
    declOf, sigAt_haelt, sigAt_produziert]
  exact List.append_nil _

/-- Every field index has its recorded range. -/
theorem rangeO_some (u : UProg) (t : Fin u.tabellen.length)
    (fld : Fin (fieldCount u t)) :
    ∃ w, fieldRangeO u t fld = some w := by
  unfold fieldRangeO
  have hlt : fld.val < (tabAt u t).felder.length := fld.isLt
  rw [List.getElem?_eq_getElem hlt]
  exact ⟨_, rfl⟩

/-- The field type is the recorded range. -/
theorem typAt_of (u : UProg) (t : Fin u.tabellen.length)
    (fld : Fin (fieldCount u t)) (w : Int × Int)
    (h : fieldRangeO u t fld = some w) :
    typAt u t fld = .int w.1 w.2 := by
  unfold typAt
  rw [h]

/-- `tabNr` at a live number. -/
theorem tabNr_some (u : UProg) (num : Nat) (h : num < u.tabellen.length) :
    (declOf u).tabNr num = some (⟨num, h⟩ : Fin u.tabellen.length) := by
  show (if h' : num < u.tabellen.length then
    (some ⟨num, h'⟩ : Option (Fin u.tabellen.length)) else none) = _
  rw [dif_pos h]

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
  | nil => simp [fieldAtPos] at h
  | cons hd tl ih =>
    cases he : (hd.1 == n) with
    | true =>
      have h1 : fieldPos (hd :: tl) n = 0 := by simp [fieldPos, he]
      rw [h1]
      exact Nat.zero_lt_succ _
    | false =>
      have h1 : fieldPos (hd :: tl) n = fieldPos tl n + 1 := by
        simp [fieldPos, he]
      have h2 : fieldAtPos (hd :: tl) n = fieldAtPos tl n := by
        simp [fieldAtPos, he]
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
  | nil => simp [fieldAtPos] at h
  | cons hd tl ih =>
    cases he : (hd.1 == n) with
    | true =>
      have h1 : fieldPos (hd :: tl) n = 0 := by simp [fieldPos, he]
      have h2 : fieldAtPos (hd :: tl) n = some hd.2 := by
        simp [fieldAtPos, he]
      rw [h2] at h
      rw [h1]
      have g0 : (((hd :: tl)[0]?).map (·.2)) = some hd.2 := rfl
      rw [g0]
      exact h
    | false =>
      have h1 : fieldPos (hd :: tl) n = fieldPos tl n + 1 := by
        simp [fieldPos, he]
      have h2 : fieldAtPos (hd :: tl) n = fieldAtPos tl n := by
        simp [fieldAtPos, he]
      rw [h2] at h
      have ih' := ih h
      rw [h1]
      have g1 : ((hd :: tl)[fieldPos tl n + 1]?) = (tl[fieldPos tl n]?) := rfl
      rw [g1]
      exact ih'

/-- A field hit: the index, its range, and the lookup equation. -/
structure FieldHit (u : UProg) (t : Fin u.tabellen.length) where
  idx : Fin (fieldCount u t)
  weit : Int × Int
  hit : fieldRangeO u t idx = some weit

/-- Find a field of a table by name. -/
def fieldHit (u : UProg) (t : Fin u.tabellen.length) (fname : String) :
    Except String (FieldHit u t) :=
  match h : fieldAtPos (tabAt u t).felder fname with
  | none => .error "field unknown"
  | some w =>
    have hlt : fieldPos (tabAt u t).felder fname < fieldCount u t :=
      fieldPos_lt _ _ _ h
    .ok ⟨⟨fieldPos (tabAt u t).felder fname, hlt⟩, w,
      fieldAtPos_get _ _ _ h⟩

/-- A variable by position and expected type (the `beq` re-checks the
    context, so a divergent caller is an explicit error). -/
def lowVar : (Γ : Ctx) → (j : Nat) → (τ : Ty) → Except String (Var Γ τ)
  | [], _, _ => .error "parameter outside"
  | σ :: Γ, 0, τ =>
    if h : σ = τ then by rw [h]; exact .ok Var.hier
    else .error "parameter shape foreign"
  | _ :: Γ, j + 1, τ =>
    match lowVar Γ j τ with
    | .error e => .error e
    | .ok v => .ok (Var.dort v)

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
    parameter for the same table (`sh` shifts parameter positions:
    `0` in a body, `1` in an `ensures` context with a result, where
    the result rides first). -/
def lowIdx (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (t : Fin u.tabellen.length) : UIdx →
    Except String (Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
  | .lit n =>
    if h1 : 0 ≤ n then
      if h2 : n ≤ (declOf u).count t - 1 then
        .ok (Expr.weiter h1 h2 (Expr.lit n))
      else .error "index outside count"
    else .error "index outside count"
  | .param p =>
    match paramPos fn.params p with
    | .error e => .error e
    | .ok j =>
      match fn.parten[j]? with
      | some (.index m) =>
        if m == t.val then
          match lowVar Γ (sh + j) (.index ((declOf u).count t)) with
          | .error e => .error e
          | .ok v => .ok (Expr.var v)
        else .error "index of foreign table"
      | _ => .error "index without G form"

/-- A sided term with its range. -/
structure LowSide (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u))) where
  weit : Int × Int
  term : Expr (declOf u) Γ Λ (.int weit.1 weit.2)

/-- The table a basis names: a pointer parameter's target, or a
    table (for `old`, where both spellings travel). -/
def lowBasisTab (u : UProg) (fn : UFn) (b : String) :
    Except String (Fin u.tabellen.length) :=
  match paramPos fn.params b with
  | .ok j =>
    match fn.parten[j]? with
    | some (.ptr num _) =>
      if h : num < u.tabellen.length then .ok ⟨num, h⟩
      else .error "pointer table unknown"
    | _ => .error "place without G form"
  | .error _ =>
    match tabIdx u.tabellen b with
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
    match fn.parten[j]? with
    | some (.ptr _ _) => .error "pointer as value without G form"
    | some _ =>
      match fn.params[j]? with
      | some (_, .int a b) =>
        match lowVar Γ (sh + j) (.int a b) with
        | .error e => .error e
        | .ok v => .ok { weit := (a, b), term := Expr.var v }
      | _ => .error "parameter without G form"
    | none => .error "parameter without G form"

/-- A `durch` term at its recorded range (the `rw` turns the
    goal into the field type, where the constructor fits). -/
def durchTerm (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (num : Nat) (w : Bool) (h : num < u.tabellen.length)
    (fh : FieldHit u ⟨num, h⟩) (v : Var Γ (.ptr num w))
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count ⟨num, h⟩)))
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
      Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.weit.1 fh.weit.2) := by
  rw [← typAt_of u ⟨num, h⟩ fh.idx fh.weit fh.hit]
  exact Expr.durch (D := declOf u) (Expr.var v) ⟨num, h⟩
    (tabNr_some u num h) fh.idx i hL

/-- A `slot` term at its recorded range. -/
def slotTerm (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (t : Fin u.tabellen.length) (fh : FieldHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.weit.1 fh.weit.2) := by
  rw [← typAt_of u t fh.idx fh.weit fh.hit]
  exact Expr.slot (D := declOf u) t fh.idx i hL

/-- An `altSlot` term at its recorded range. -/
def altTerm (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (t : Fin u.tabellen.length) (fh : FieldHit u t)
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count t)))
    (hL : ∀ wdd ∈ (declOf u).braucht t, Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.weit.1 fh.weit.2) := by
  rw [← typAt_of u t fh.idx fh.weit fh.hit]
  exact Expr.altSlot (D := declOf u) t fh.idx i hL

/-- A slot read through a pointer parameter (positions shift
    by `sh`, see `lowIdx`). -/
def lowDurch (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (b fname : String) (ix : UIdx) :
    Except String (LowSide u Γ Λ) :=
  match paramPos fn.params b with
  | .error e => .error e
  | .ok j =>
    match fn.parten[j]? with
    | some (.ptr num w) =>
      if h : num < u.tabellen.length then
        match fieldHit u ⟨num, h⟩ fname with
        | .error e => .error e
        | .ok fh =>
          match lowVar Γ (sh + j) (.ptr num w) with
          | .error e => .error e
          | .ok v =>
            match lowIdx u Γ Λ fn sh ⟨num, h⟩ ix with
            | .error e => .error e
            | .ok i =>
              if hL : (∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
                  Res.von (declOf u) wdd ∈ Λ) then
                .ok { weit := fh.weit, term := durchTerm u Γ Λ num w h fh v i hL }
              else .error "access without held guard"
      else .error "pointer table unknown"
    | _ => .error "place without G form"

/-- A slot read at a table (positions shift by `sh`). -/
def lowTabRead (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (b fname : String) (ix : UIdx) :
    Except String (LowSide u Γ Λ) :=
  match tabIdx u.tabellen b with
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
          .ok { weit := fh.weit, term := slotTerm u Γ Λ t fh i hL }
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
          .ok { weit := fh.weit, term := altTerm u Γ Λ t fh i hL }
        else .error "access without held guard"

/-- A value side in a body: a literal, a numeric parameter or a
    slot read (`result` and `old` have no G form here). -/
def lowSideVal (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) : USide → Except String (LowSide u Γ Λ)
  | .lit n => .ok { weit := (n, n), term := Expr.lit n }
  | .param p => lowParamSide u Γ Λ fn 0 p
  | .slot b f ix => lowDurch u Γ Λ fn 0 b f ix
  | .tab b f ix => lowTabRead u Γ Λ fn 0 b f ix
  | _ => .error "side in body without G form"

/-- A comparison side in `ensures`: literals, numeric parameters,
    slot reads, `old` and `result` travel. -/
def lowSideEns (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option (Int × Int)) :
    USide → Except String (LowSide u Γ Λ)
  | .lit n => .ok { weit := (n, n), term := Expr.lit n }
  | .param p =>
    lowParamSide u Γ Λ fn (if er.isSome then 1 else 0) p
  | .slot b f ix =>
    lowDurch u Γ Λ fn (if er.isSome then 1 else 0) b f ix
  | .tab b f ix =>
    lowTabRead u Γ Λ fn (if er.isSome then 1 else 0) b f ix
  | .alt b f ix =>
    lowAltRead u Γ Λ fn (if er.isSome then 1 else 0) b f ix
  | .erg =>
    match er with
    | some (a, b) =>
      match lowVar Γ 0 (.int a b) with
      | .error e => .error e
      | .ok v => .ok { weit := (a, b), term := Expr.var v }
    | none => .error "result without result"

/-- One comparison in `ensures` (G folds all but `lt`/`le`/`eq`). -/
def lowCmp (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option (Int × Int)) :
    String → USide → USide → Except String (Expr (declOf u) Γ Λ .bool)
  | op, a, b =>
    match lowSideEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok s1 =>
      match lowSideEns u Γ Λ fn er b with
      | .error e => .error e
      | .ok s2 =>
        match op with
        | "==" => .ok (Expr.eq s1.term s2.term)
        | "!=" => .ok (Expr.nicht (Expr.eq s1.term s2.term))
        | "<" => .ok (Expr.lt s1.term s2.term)
        | "<=" => .ok (Expr.le s1.term s2.term)
        | ">" => .ok (Expr.lt s2.term s1.term)
        | ">=" => .ok (Expr.le s2.term s1.term)
        | _ => .error "operator without G form"

/-- One `ensures` predicate. -/
def lowEns (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option (Int × Int)) :
    UEns → Except String (Expr (declOf u) Γ Λ .bool)
  | .cmp op a b => lowCmp u Γ Λ fn er op a b
  | .wahr => .ok Expr.wahr
  | .falsch => .ok Expr.falsch
  | .und a b =>
    match lowEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x =>
      match lowEns u Γ Λ fn er b with
      | .error e => .error e
      | .ok y => .ok (Expr.und x y)
  | .oder a b =>
    match lowEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x =>
      match lowEns u Γ Λ fn er b with
      | .error e => .error e
      | .ok y => .ok (Expr.oder x y)
  | .nicht a =>
    match lowEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x => .ok (Expr.nicht x)

/-- The `ensures` conjunction (empty is `.wahr`). -/
def lowEnsList (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option (Int × Int)) :
    List UEns → Except String (Expr (declOf u) Γ Λ .bool)
  | [] => .ok Expr.wahr
  | e :: rest =>
    match lowEns u Γ Λ fn er e with
    | .error err => .error err
    | .ok x =>
      match lowEnsList u Γ Λ fn er rest with
      | .error err => .error err
      | .ok y =>
        match y with
        | Expr.wahr => .ok x
        | _ => .ok (Expr.und x y)

end Gabbro.Grammatik.Parser.UebersetzeAllg

/-
  CUTS: what is not proved here.

  1. This file builds the generic declaration `declOf` (Fin carriers)
     and lowers sides and `ensures` (`lowIdx` through `lowEnsList`).
     NOT yet built: statement lowering (`assign`/`call`), `RufPasst`
     assembly, bodies, `lowerAllg`, the 104/108 fragment and footprint
     pins, the data agreement, the real-text lexer pin and the chaining
     theorem. Those remain open work.
  2. `beq`-style soundness is proved for nothing here; there are no
     `beq` lemmas in this file.
  3. Elaboration lessons (for the lane that continues): pin `D`
     explicitly on every constructor over the Fin carriers
     (`Expr.slot (D := declOf u)` etc.), since `D` never unifies out
     of a stuck `(declOf u).Tab` projection; keep struct literals on
     one line (a trailing comma at end of line misparses); a term
     continuation line must not start with `(` (it parses as a tactic).
-/

#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.notEmpty_ne_nil
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.sigAt_get
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.params_eq
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.erg_eq
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.haelt_eq
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.ende_eq
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.rangeO_some
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.typAt_of
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.tabNr_some
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.fieldPos_lt
#print axioms Gabbro.Grammatik.Parser.UebersetzeAllg.fieldAtPos_get
