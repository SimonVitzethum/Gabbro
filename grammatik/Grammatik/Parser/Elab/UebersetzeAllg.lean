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
import Grammatik.Parser.Elab.Uebersetze

namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Gabbro.Grammatik.Parser.Uebersetze

/-! ## Declaration data looked up from `UProg` -/

/-- The table at an index. -/
def tabAt (u : UProg) (t : Fin u.tabs.length) : UTab :=
  u.tabs.get t

/-- The lock at an index. -/
def lockAt (u : UProg) (l : Fin u.locks.length) : ULock :=
  u.locks.get l

/-- The function at an index. -/
def fnAt (u : UProg) (f : Fin u.fns.length) : UFn :=
  u.fns.get f

/-- The field count of a table. -/
def fieldCount (u : UProg) (t : Fin u.tabs.length) : Nat :=
  (tabAt u t).cols.length

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
def fieldRangeO (u : UProg) (t : Fin u.tabs.length)
    (f : Fin (fieldCount u t)) : Option (Int × Int) :=
  ((tabAt u t).cols[f.val]?).map (·.2)

/-- The field is a `bool` field (named in `bools`). -/
def boolFeldAt (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) : Bool :=
  match (tabAt u t).cols[f.val]? with
  | some q => (tabAt u t).bools.contains q.1
  | none => false

/-- The number of the table an option field points at (`none` for a field that is no option). -/
def optNumAt (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) : Option Nat :=
  match (tabAt u t).cols[f.val]? with
  | some q => ((tabAt u t).opts.find? (fun p => p.1 == q.1)).map (·.2)
  | none => none

/-- The count of the table an option field points at: the `n` of its type `Ty.opt n`. -/
def optFeldAt (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) : Option Int :=
  (optNumAt u t f).bind fun num => (u.tabs[num]?).map (·.count)

/-- The field type: `bool` for a bool field, `opt` for an option field, else the recorded range, or `.int 0 0`
    off the table (unreachable through `fieldRangeO`, kept for totality). -/
def typAt (u : UProg) (t : Fin u.tabs.length)
    (f : Fin (fieldCount u t)) : Ty :=
  if boolFeldAt u t f then .bool else
  match optFeldAt u t f with
  | some n => .opt n
  | none =>
    match fieldRangeO u t f with
    | some w => .int w.1 w.2
    | none => .int 0 0

/-- The guards of a table: the locks whose `schutz` names it. -/
def needsAt (u : UProg) (t : Fin u.tabs.length) :
    List (Fin u.locks.length ⊕ (Empty × Nat)) :=
  List.finRange u.locks.length |>.filterMap fun l =>
    if (lockAt u l).guard.any (· == (tabAt u t).name) then some (.inl l)
    else none

def globAt (u : UProg) (g : Fin u.globs.length) : UGlob := u.globs.get g

/-- The guards of a static: the locks whose `protects` list names it (`gbraucht`). -/
def gneedsAt (u : UProg) (g : Fin u.globs.length) :
    List (Fin u.locks.length ⊕ (Empty × Nat)) :=
  List.finRange u.locks.length |>.filterMap fun l =>
    if (lockAt u l).guard.any (· == (globAt u g).name) then some (.inl l)
    else none

/-- The foreign body at an index. -/
def uaxAt (u : UProg) (a : Fin u.axs.length) : UAx := u.axs.get a

/-- A foreign body by name. -/
def uaxIdx : (xs : List UAx) → (n : String) → Except String (Fin xs.length)
  | [], n => .error ("function unknown: " ++ n)
  | a :: rest, n =>
    if a.name == n then .ok 0
    else match uaxIdx rest n with
      | .error e => .error e
      | .ok j => .ok j.succ

/-- The held locks of a function, as indices (names the declaration
    does not know are dropped; `elabU` output never has them). -/
def heldAt (u : UProg) (f : UFn) : List (Fin u.locks.length) :=
  f.held.filterMap fun n => (lockIdx u.locks n).toOption

/-- A static by name. -/
def globIdx : (gs : List UGlob) → (n : String) → Except String (Fin gs.length)
  | [], n => .error ("static unknown: " ++ n)
  | g :: rest, n =>
    if g.name == n then .ok 0
    else match globIdx rest n with
      | .error e => .error e
      | .ok j => .ok j.succ

/-- The write flag of a function at a static. -/
def writesGAt (u : UProg) (f : UFn) (g : Fin u.globs.length) : Bool :=
  f.gputs.any (· == (globAt u g).name)

/-- The write flag of a function at a table. -/
def writesAt (u : UProg) (f : UFn) (t : Fin u.tabs.length) : Bool :=
  f.puts.any (· == (tabAt u t).name)

/-! ## Lock floors (`Signatur.boden`)

    The floor of a function is the lowest rank of any lock taken on a path from it (its own `locks L` blocks
    and, through its calls, the callees'); a function that takes none has the floor `hoch`, above every rank
    of the unit. A unit without locks has no floors. This is the rule of the exporter (`resolve_floors`):
    an extra lock held across a call ranks below the callee's floor (`RufPasst.hx`), so every lock the callee
    takes ranks above everything held (`H006` across the call boundary). -/

/-- The rank of a lock by name. -/
def lockRank (u : UProg) (n : String) : Option Int :=
  (u.locks.find? (fun l => l.name == n)).map (·.rank)

def optMin : Option Int → Option Int → Option Int
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

/-- The lowest rank a function takes directly (its `locks L { .. }` blocks). -/
def directFloor (u : UProg) (f : UFn) : Option Int :=
  f.body.foldl (fun acc st => match st with
    | .lockBeg n => optMin acc (lockRank u n)
    | _ => acc) none

/-- The functions a function calls directly. -/
def callNames (f : UFn) : List String :=
  f.body.filterMap fun st => match st with
    | .call c _ => some c
    | .bindCall _ c _ => some c
    | _ => none

/-- One round of the floor relation: the direct floor and the floors of the callees found so far. -/
def floorStep (u : UProg) (cur : List (String × Option Int)) : List (String × Option Int) :=
  u.fns.map fun f =>
    (f.name, (callNames f).foldl
      (fun acc c => optMin acc ((cur.find? (fun p => p.1 == c)).bind (·.2))) (directFloor u f))

/-- `n` rounds (a path through the call graph is at most as long as the number of functions). -/
def floorsN (u : UProg) : Nat → List (String × Option Int)
  | 0 => u.fns.map fun f => (f.name, directFloor u f)
  | n + 1 => floorStep u (floorsN u n)

/-- The floor of a function: `none` in a unit without locks, else the lowest rank on any path from it, or
    one above the highest rank of the unit when the paths take no lock. -/
def floorOf (u : UProg) (f : UFn) : Option Int :=
  if u.locks.isEmpty then none
  else some (match ((floorsN u u.fns.length).find? (fun p => p.1 == f.name)).bind (·.2) with
    | some c => c
    | none => (u.locks.map (·.rank)).foldl max 0 + 1)

/-- The signature of an elaborated function. -/
def mkSig (u : UProg) (f : UFn) :
    Signatur (Fin u.tabs.length) (Fin u.globs.length) (Fin u.locks.length) Empty where
  params := f.params.map (·.2)
  erg := f.ergTy
  gruende := 0
  haelt := heldAt u f
  schreibt := writesAt u f
  gschreibt := writesGAt u f
  konsumiert := []
  produziert := []
  boden := floorOf u f

/-- The dummy signature: no parameters, no rights. -/
def dummySig (u : UProg) :
    Signatur (Fin u.tabs.length) (Fin u.globs.length) (Fin u.locks.length) Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun _ => false
  konsumiert := []
  produziert := []

/-- The `n`th signature, or the dummy (an out-of-range number names
    no function). -/
def sigAt (u : UProg) (n : Nat) :
    Signatur (Fin u.tabs.length) (Fin u.globs.length) (Fin u.locks.length) Empty :=
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
  Tab := Fin u.tabs.length
  decTab := inferInstance
  count := fun t => (tabAt u t).count
  Feld := fun t => Fin (fieldCount u t)
  decFeld := fun _ => inferInstance
  typ := typAt u
  erlaubt := fun _ _ _ _ => false
  tabNr := fun n => if h : n < u.tabs.length then some ⟨n, h⟩ else none
  Glob := Fin u.globs.length
  decGlob := inferInstance
  gtyp := fun g => (globAt u g).ty.toTy
  nutzlast := fun _ => []
  atomar := fun g => (globAt u g).atomic
  geteilt := fun t => (!((needsAt u t).isEmpty))
  ggeteilt := fun g => (!((gneedsAt u g).isEmpty))
  Lock := Fin u.locks.length
  decLock := inferInstance
  rang := fun l => (lockAt u l).rank
  maskiert := fun l => (lockAt u l).masks
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := needsAt u
  gbraucht := gneedsAt u
  eigner := fun _ => []
  Fn := Fin u.fns.length
  sig := fun f => f.val
  sigNr := sigAt u
  eigner_nie_erzeugt :=
    fun _ _ _ _ h => (List.not_mem_nil (show _ ∈ ([] : List Empty) from h)).elim
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Fin u.axs.length
  aparams := fun a => (uaxAt u a).params
  aerg := fun a => (uaxAt u a).res
  aschreibt := fun _ _ => false
  agschreibt := fun _ _ => false
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Option (Fin u.annahmen.length)
  a10 := none
  geteilt_bewacht :=
    fun t h => notEmpty_ne_nil _ (show ((!((needsAt u t).isEmpty)) = true) from h)
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht :=
    fun g h => Or.inl (notEmpty_ne_nil _ (show ((!((gneedsAt u g).isEmpty)) = true) from h))

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
    (sigAt u i.val).erg = (fnAt u i).ergTy := by
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
    (declOf u).erg i = (fnAt u i).ergTy := by
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
    (ho : optFeldAt u t fld = none) :
    typAt u t fld = .int w.1 w.2 := by
  unfold typAt
  rw [hb, ho, h]
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

/-- `tabNr` at a live number. -/
theorem tabNr_some (u : UProg) (num : Nat) (h : num < u.tabs.length) :
    (declOf u).tabNr num = some (⟨num, h⟩ : Fin u.tabs.length) := by
  show (if h' : num < u.tabs.length then
    (some ⟨num, h'⟩ : Option (Fin u.tabs.length)) else none) = _
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
        .ok ⟨⟨fieldPos (tabAt u t).cols fname, hlt⟩, w, fieldAtPos_get _ _ _ h,
          typAt_of u t _ w (fieldAtPos_get _ _ _ h) hb ho⟩
      else .error "option field as a number"
    else .error "bool field as a number"

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
    parameter for the same table (`sh` shifts parameter positions:
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
      | some (.index m) =>
        if m == t.val then
          match lowVar Γ (sh + j) (.index ((declOf u).count t)) with
          | .error e => .error e
          | .ok v => .ok (Expr.var v)
        else .error "index of foreign table"
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

/-- `a << b` over non-negative ranges (M137): `Expr.shl` at the width `schiebeBreite`. -/
def LowSide.links {u : UProg} {Γ : Ctx} {Λ : List (Res (declOf u))} (x y : LowSide u Γ Λ) :
    Except String (LowSide u Γ Λ) :=
  if h0 : 0 ≤ x.range.1 then
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
  if h0 : 0 ≤ x.range.1 then
    if h0' : 0 ≤ y.range.1 then
      if hw1 : x.range.2 < (2 : Int) ^ schiebeBreite x.range y.range then
        if hw2 : y.range.2 < ((schiebeBreite x.range y.range : Nat) : Int) then
          .ok { range := (0, x.range.2),
                term := Expr.shr (schiebeBreite x.range y.range) hw1 hw2 h0 h0' x.term y.term }
        else .error "shift outside its width"
      else .error "shift outside its width"
    else .error "bit operation over a negative range"
  else .error "bit operation over a negative range"

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
    | some (.ptr num _) =>
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
    | some (.ptr _ _) => .error "pointer as value without G form"
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
    (fh : FieldHit u ⟨num, h⟩) (v : Var Γ (.ptr num w))
    (i : Expr (declOf u) Γ Λ (.index ((declOf u).count ⟨num, h⟩)))
    (hL : ∀ wdd ∈ (declOf u).braucht ⟨num, h⟩,
      Res.von (declOf u) wdd ∈ Λ) :
    Expr (declOf u) Γ Λ (.int fh.range.1 fh.range.2) := by
  rw [← fh.hint]
  exact Expr.thru (D := declOf u) (Expr.var v) ⟨num, h⟩
    (tabNr_some u num h) fh.idx i hL

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
    | some (.ptr num w) =>
      if h : num < u.tabs.length then
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
                .ok { range := fh.range, term := durchTerm u Γ Λ num w h fh v i hL }
              else .error "access without held guard"
      else .error "pointer table unknown"
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
    else .error "access without held guard"

/-- A `bool` slot read through a pointer parameter (positions shift by `sh`): the place's truth value. -/
def lowBoolDurch (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (sh : Nat) (b fname : String) (ix : UIdx) :
    Except String (Expr (declOf u) Γ Λ .bool) :=
  match paramPos fn.params b with
  | .error e => .error e
  | .ok j =>
    match fn.kinds[j]? with
    | some (.ptr num w) =>
      if h : num < u.tabs.length then
        match fieldHitB u ⟨num, h⟩ fname with
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
                .ok (by
                  rw [← fh.hbool]
                  exact Expr.thru (D := declOf u) (Expr.var v) ⟨num, h⟩
                    (tabNr_some u num h) fh.idx i hL)
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

/-- A comparison side in `ensures`: literals, numeric parameters,
    slot reads, `old` and `result` travel. -/
def lowSideEns (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option (Int × Int)) :
    USide → Except String (LowSide u Γ Λ)
  | .lit n => .ok { range := (n, n), term := Expr.lit n }
  | .param p =>
    lowParamSide u Γ Λ fn (if er.isSome then 1 else 0) p
  | .glob p => lowGlobSide u Γ Λ p
  | .slot b f ix =>
    lowDurch u Γ Λ fn (if er.isSome then 1 else 0) b f ix
  | .tab b f ix =>
    lowTabRead u Γ Λ fn (if er.isSome then 1 else 0) b f ix
  | .old b f ix =>
    lowAltRead u Γ Λ fn (if er.isSome then 1 else 0) b f ix
  | .add a b =>
    match lowSideEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x =>
      match lowSideEns u Γ Λ fn er b with
      | .error e => .error e
      | .ok y => .ok (LowSide.plus x y)
  | .sub a b =>
    match lowSideEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x =>
      match lowSideEns u Γ Λ fn er b with
      | .error e => .error e
      | .ok y => .ok (LowSide.minus x y)
  | .mul a b =>
    match lowSideEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x =>
      match lowSideEns u Γ Λ fn er b with
      | .error e => .error e
      | .ok y => .ok (LowSide.times x y)
  | .conv lo hi a =>
    match lowSideEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x => LowSide.conv lo hi x
  | .band a b => lowZwei LowSide.and (lowSideEns u Γ Λ fn er a) (lowSideEns u Γ Λ fn er b)
  | .bor a b => lowZwei LowSide.or (lowSideEns u Γ Λ fn er a) (lowSideEns u Γ Λ fn er b)
  | .bxor a b => lowZwei LowSide.xoder (lowSideEns u Γ Λ fn er a) (lowSideEns u Γ Λ fn er b)
  | .div a b => lowZwei LowSide.durch (lowSideEns u Γ Λ fn er a) (lowSideEns u Γ Λ fn er b)
  | .rem a b => lowZwei LowSide.rest (lowSideEns u Γ Λ fn er a) (lowSideEns u Γ Λ fn er b)
  | .shl a b => lowZwei LowSide.links (lowSideEns u Γ Λ fn er a) (lowSideEns u Γ Λ fn er b)
  | .shr a b => lowZwei LowSide.rechts (lowSideEns u Γ Λ fn er a) (lowSideEns u Γ Λ fn er b)
  | .neg a =>
    match lowSideEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x => .ok (LowSide.minusEins x)
  | .erg =>
    match er with
    | some (a, b) =>
      match lowVar Γ 0 (.int a b) with
      | .error e => .error e
      | .ok v => .ok { range := (a, b), term := Expr.var v }
    | none => .error "result without result"

/-- A value side in a body: the sides of an `ensures` without `old` and `result` (a body reads neither). -/
def lowSideVal (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (s : USide) : Except String (LowSide u Γ Λ) :=
  if seiteAltErg s then .error "side in body without G form"
  else lowSideEns u Γ Λ fn none s

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
        | "!=" => .ok (Expr.not (Expr.eq s1.term s2.term))
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
  | .tru => .ok Expr.tru
  | .fls => .ok Expr.fls
  | .and a b =>
    match lowEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x =>
      match lowEns u Γ Λ fn er b with
      | .error e => .error e
      | .ok y => .ok (Expr.and x y)
  | .or a b =>
    match lowEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x =>
      match lowEns u Γ Λ fn er b with
      | .error e => .error e
      | .ok y => .ok (Expr.or x y)
  | .not a =>
    match lowEns u Γ Λ fn er a with
    | .error e => .error e
    | .ok x => .ok (Expr.not x)
  | .globB p => lowGlobBool u Γ Λ p
  | .var p =>
    match paramPos fn.params p with
    | .error e => .error e
    | .ok j =>
      match lowVar Γ ((if er.isSome then 1 else 0) + j) .bool with
      | .error e => .error e
      | .ok v => .ok (Expr.var v)
  | .slotB b f ix => lowBoolDurch u Γ Λ fn (if er.isSome then 1 else 0) b f ix
  | .tabB b f ix => lowBoolTab u Γ Λ fn (if er.isSome then 1 else 0) b f ix

/-- The `ensures` conjunction (empty is `.tru`). -/
def lowEnsList (u : UProg) (Γ : Ctx) (Λ : List (Res (declOf u)))
    (fn : UFn) (er : Option (Int × Int)) :
    List UEns → Except String (Expr (declOf u) Γ Λ .bool)
  | [] => .ok Expr.tru
  | e :: rest =>
    match lowEns u Γ Λ fn er e with
    | .error err => .error err
    | .ok x =>
      match lowEnsList u Γ Λ fn er rest with
      | .error err => .error err
      | .ok y =>
        match y with
        | Expr.tru => .ok x
        | _ => .ok (Expr.and x y)

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
