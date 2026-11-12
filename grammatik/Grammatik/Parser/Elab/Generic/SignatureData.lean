module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil12

public import Grammatik.Parser.Elab.Signatur.SignatureLookup
@[expose] public section



namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Gabbro.Grammatik.Parser.Uebersetze

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

/-- The type of an aggregate field (`none` for any other field). -/
def wertFeldAt (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) : Option Ty :=
  match (tabAt u t).cols[f.val]? with
  | some q => ((tabAt u t).werte.find? (fun p => p.1 == q.1)).map (·.2)
  | none => none

/-- The field type: `bool` for a bool field, `opt` for an option field, the aggregate of an aggregate field, else
    the recorded range, or `.int 0 0` off the table (unreachable through `fieldRangeO`, kept for totality). -/
def typAt (u : UProg) (t : Fin u.tabs.length)
    (f : Fin (fieldCount u t)) : Ty :=
  if boolFeldAt u t f then .bool else
  match optFeldAt u t f with
  | some n => .opt n
  | none =>
    match wertFeldAt u t f with
    | some τ => τ
    | none =>
    match fieldRangeO u t f with
    | some w => .int w.1 w.2
    | none => .int 0 0

/-- The guards of a table: the locks whose `schutz` names it. -/
def needsAt (u : UProg) (t : Fin u.tabs.length) :
    List (Fin u.locks.length ⊕ (Fin u.marken.length × Nat)) :=
  List.finRange u.locks.length |>.filterMap fun l =>
    if (lockAt u l).guard.any (· == (tabAt u t).name) then some (.inl l)
    else none

def globAt (u : UProg) (g : Fin u.globs.length) : UGlob := u.globs.get g

/-- The guards of a static: the locks whose `protects` list names it (`gbraucht`). -/
def gneedsAt (u : UProg) (g : Fin u.globs.length) :
    List (Fin u.locks.length ⊕ (Fin u.marken.length × Nat)) :=
  List.finRange u.locks.length |>.filterMap fun l =>
    if (lockAt u l).guard.any (· == (globAt u g).name) then some (.inl l)
    else none

/-- The owner guard of a table as declaration marks (C12): the `owner` mark resolved
    against the unit's mark table, at stage 0. An unresolvable owner gives no mark that
    could ever be held, so the table stays inaccessible. -/
def eignerAt (u : UProg) (t : Fin u.tabs.length) : List (Fin u.marken.length) :=
  match (tabAt u t).owner with
  | none => []
  | some m => match markFin u.marken m with | none => [] | some i => [i]

/-- Membership in a table's owner list names that table's owner mark. -/
theorem mem_eignerAt (u : UProg) (t : Fin u.tabs.length) (m : Fin u.marken.length)
    (h : m ∈ eignerAt u t) :
    ∃ o, (tabAt u t).owner = some o ∧ markFin u.marken o = some m := by
  cases ho : (tabAt u t).owner with
  | none =>
    simp only [eignerAt, ho, List.not_mem_nil] at h
  | some o =>
    refine ⟨o, rfl, ?_⟩
    cases hm : markFin u.marken o with
    | none =>
      simp only [eignerAt, ho, hm, List.not_mem_nil] at h
    | some j =>
      have hj : m = j := by simpa only [eignerAt, ho, hm, List.mem_singleton] using h
      exact congrArg some hj.symm

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

/-- The payload of an atomic (`D.nutzlast`): its declared statics, by name. -/
def nutzAt (u : UProg) (g : Fin u.globs.length) : List (Fin u.globs.length) :=
  (globAt u g).nutzlast.filterMap fun n => (globIdx u.globs n).toOption

/-- `D.erlaubt`: the field is governed by a state (a `transition` statement applies it there) whose
    `transition` lines allow `von -> nach` (stage numbers). -/
def erlaubtAt (u : UProg) (t : Fin u.tabs.length) (f : Fin (fieldCount u t)) (von nach : Int) : Bool :=
  match (tabAt u t).cols[f.val]? with
  | none => false
  | some (fname, _) =>
    u.regiert.any fun (tb, fld, s) => tb == (tabAt u t).name && fld == fname &&
      (u.zustaende.find? (fun z => z.name == s)).any fun z =>
        z.paare.any fun (a, c) => decide ((a : Int) = von) && decide ((c : Int) = nach)

/-- The register at an index. -/
def regAt (u : UProg) (r : Fin u.regs.length) : UReg := u.regs.get r

/-- A register by device and name. -/
def regIdx : (rs : List UReg) → (d n : String) → Except String (Fin rs.length)
  | [], _, n => .error ("register unknown: " ++ n)
  | g :: rest, d, n =>
    if g.dev == d && g.name == n then .ok 0
    else match regIdx rest d n with
      | .error e => .error e
      | .ok j => .ok j.succ

/-- The first entry of a name among the numbered functions is the function `fnIdx` finds. -/
theorem fnIdx_zipIdx (n : String) : ∀ (fns : List UFn) (k : Nat) (p : UFn × Nat),
    (fns.zipIdx k).find? (fun q => strEq q.1.name n) = some p →
    ∃ h : p.2 - k < fns.length, k ≤ p.2 ∧ fnIdx fns n = .ok ⟨p.2 - k, h⟩
  | [], k, p, hf => by
    simp only [List.zipIdx_nil, List.find?_nil] at hf
    exact absurd hf (by simp only [reduceCtorEq, not_false_eq_true])
  | f :: rest, k, p, hf => by
    by_cases hs : strEq f.name n = true
    · simp only [List.zipIdx_cons, List.find?_cons, hs, Option.some.injEq] at hf
      subst hf
      have hb : (f.name == n) = true := by
        rw [(strEq_eq _ _).mp hs]
        exact beq_self_eq_true _
      refine ⟨by simp only [Nat.sub_self, List.length_cons]; omega, Nat.le_refl _, ?_⟩
      simp only [fnIdx, hb, if_true]
      exact congrArg Except.ok (Fin.ext (by simp only [Fin.val_zero, Nat.sub_self]))
    · have hs' : strEq f.name n = false := Bool.eq_false_iff.mpr hs
      simp only [List.zipIdx_cons, List.find?_cons, hs'] at hf
      obtain ⟨h, hk, he⟩ := fnIdx_zipIdx n rest (k + 1) p hf
      have hb : (f.name == n) = false := by
        cases hb : f.name == n
        · rfl
        · exact absurd ((strEq_eq _ _).mpr (eq_of_beq hb)) hs
      refine ⟨by simp only [List.length_cons]; omega, by omega, ?_⟩
      simp only [fnIdx, hb, he, Bool.false_eq_true, if_false]
      exact congrArg Except.ok (Fin.ext (by simp only [Fin.val_succ]; omega))

/-- A function's number by name in a unit (`fnIdx` on the unit's functions). -/
@[reducible] def fnNr (u : UProg) (n : String) : Except String (Fin u.fns.length) :=
  fnIdx u.fns n

/-- `fnNr` from a cache of the unit's functions: one lookup in its name table; an unknown name takes
    the scan and its error. -/
def fnNrAus (u : UProg) (n : String) (c : UMerk) (h1 : c.fns = u.fns) :
    Except String (Fin u.fns.length) :=
  match hf : c.namen.tafel.finde n with
  | some p => .ok ⟨p.2, by
      rw [c.namen.finde_eq, h1] at hf
      obtain ⟨h, -, -⟩ := fnIdx_zipIdx n u.fns 0 p hf
      exact h⟩
  | none => fnIdx u.fns n

theorem fnNrAus_eq (u : UProg) (n : String) (c : UMerk) (h1 : c.fns = u.fns) :
    fnNrAus u n c h1 = fnIdx u.fns n := by
  unfold fnNrAus
  split
  · next p hf =>
    rw [c.namen.finde_eq, h1] at hf
    obtain ⟨h, -, he⟩ := fnIdx_zipIdx n u.fns 0 p hf
    exact he.symm
  · rfl

/-- `fnNr` by the unit's cache. -/
def fnNrSchnell (u : UProg) (n : String) : Except String (Fin u.fns.length) :=
  u.mitMerk (fun c h1 _ => fnNrAus u n c h1) (fun _ => fnIdx u.fns n)
    (fun c h1 _ => fnNrAus_eq u n c h1)

/-- **The table names the same number.** -/
@[csimp] theorem fnNr_eq_schnell : @fnNr = @fnNrSchnell := by
  funext u n
  unfold fnNrSchnell
  rw [UProg.mitMerk_eq]
  try rfl

/-- The mirror of a register (`mirrors R from M`): a register of the same device. -/
def spiegelAt (u : UProg) (r : Fin u.regs.length) : Option (Fin u.regs.length) :=
  (regAt u r).spiegel.bind fun m => (regIdx u.regs (regAt u r).dev m).toOption

/-- The carriers a register's answer rests on (`depends { .. }`): tables first by name, else statics. -/
def rtraegerAt (u : UProg) (r : Fin u.regs.length) : List (Fin u.tabs.length ⊕ Fin u.globs.length) :=
  (regAt u r).traeger.filterMap fun n =>
    match (tabIdx u.tabs n).toOption with
    | some t => some (.inl t)
    | none => (globIdx u.globs n).toOption.map .inr

/-- The write flag of a function at a static. -/
def writesGAt (u : UProg) (f : UFn) (g : Fin u.globs.length) : Bool :=
  f.gputs.any (· == (globAt u g).name)

/-- The write flag of a function at a table. -/
def writesAt (u : UProg) (f : UFn) (t : Fin u.tabs.length) : Bool :=
  f.puts.any (· == (tabAt u t).name)

/-- The invariant at an index. -/
def invAt (u : UProg) (i : Fin u.invs.length) : UInv := u.invs.get i

/-- The carriers of an invariant, by name: a table, else a static (C05). `uInv` resolves every name to exactly
    one carrier, so for an elaborated unit nothing is dropped. -/
def invTraeger (u : UProg) (i : Fin u.invs.length) : List (Fin u.tabs.length ⊕ Fin u.globs.length) :=
  (invAt u i).traeger.filterMap fun n =>
    match (tabIdx u.tabs n).toOption with
    | some t => some (.inl t)
    | none => (globIdx u.globs n).toOption.map .inr

/-- `U003` at an invariant, decided over the elaborated functions: a writer of a carrier (a table through
    `writesAt`, a static through `writesGAt`) holds every lock that guards a carrier (the elaborator refuses a
    unit where it fails, `uU003`, and so does the lowering, `lowerInvAt`). -/
def invOkB (u : UProg) (i : Fin u.invs.length) : Bool :=
  (u.fns ++ u.ptrs).all fun f =>
    !((invTraeger u i).any (Sum.elim (writesAt u f) (writesGAt u f))) ||
    (invTraeger u i).all fun c => (Sum.elim (needsAt u) (gneedsAt u) c).all fun w =>
      match w with
      | .inl L => decide (L ∈ heldAt u f)
      | .inr _ => true

/-- The carriers of an invariant in the declaration: its carriers where `U003` holds (always, for a lowered
    unit: `lowerInvAt` refuses otherwise), none otherwise -- so `invarianten_gehalten` holds for every `UProg`.
    The fallback is never reached by a unit that lowers (`traegerD_of_ok`, `lowerInvAt_facts`). -/
def traegerD (u : UProg) (i : Fin u.invs.length) : List (Fin u.tabs.length ⊕ Fin u.globs.length) :=
  if invOkB u i then invTraeger u i else []

/-- Where `U003` holds, the declared carriers are ALL the invariant's carriers. -/
theorem traegerD_of_ok (u : UProg) (i : Fin u.invs.length) (h : invOkB u i = true) :
    traegerD u i = invTraeger u i := by
  unfold traegerD
  rw [if_pos h]

end Gabbro.Grammatik.Parser.UebersetzeAllg
