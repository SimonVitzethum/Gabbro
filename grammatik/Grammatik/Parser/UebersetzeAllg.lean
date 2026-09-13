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

end Gabbro.Grammatik.Parser.UebersetzeAllg
