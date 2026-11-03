module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil12

@[expose] public section



namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Gabbro.Grammatik.Parser.Uebersetze

/-- `strEq` is sound (local copy: `Rundlauf` is outside the import closure here). -/
theorem strEq_klingt {a b : String} (h : strEq a b = true) : a = b := by
  unfold strEq at h
  have h2 : a.toList = b.toList := beq_iff_eq.mp h
  have h3 := congrArg String.ofList h2
  rwa [String.ofList_toList, String.ofList_toList] at h3

/-- A mark name resolves to its declaration mark (C12). -/
theorem markFin_get (marken : List String) (m : String) (i : Fin marken.length)
    (h : markFin marken m = some i) : marken.get i = m := by
  unfold markFin at h
  have hp : strEq (marken.get i) m = true := List.find?_some h
  exact strEq_klingt hp

/-- The owner index map (C12, lead decision (a)): the `DataRights.owner` number of a
    capability is an index into `u.eigner`; this resolves it to the declaration mark
    (`Fin u.marken.length`) of the same name, if declared. The lowering gates resolve
    owned capabilities through it; unresolvable owners never satisfy a guard. -/
def eignerMarke (u : UProg) (n : Nat) : Option (Fin u.marken.length) :=
  u.eigner[n]?.bind (markFin u.marken)

/-- The map lands on the named mark: the resolved index names the same entry. -/
theorem eignerMarke_nennt (u : UProg) (n : Nat) (i : Fin u.marken.length)
    (h : eignerMarke u n = some i) :
    ∃ m, u.eigner[n]? = some m ∧ markFin u.marken m = some i ∧ u.marken.get i = m := by
  unfold eignerMarke at h
  obtain ⟨m, hmn, hmi⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨m, hmn, hmi, markFin_get u.marken m i hmi⟩

/-- The resolved mark is held in the owner namespace. For an elaborated unit every
    member of `u.eigner` is a declared linear mark (the `linear` types by construction,
    the table owners by `uPruefEigner`), so the map lands on linear marks. -/
theorem eignerMarke_mem (u : UProg) (n : Nat) (i : Fin u.marken.length)
    (h : eignerMarke u n = some i) : u.marken.get i ∈ u.eigner := by
  obtain ⟨m, hmn, _, hmi⟩ := eignerMarke_nennt u n i h
  rw [hmi]
  exact List.mem_of_getElem? hmn

/-- The map is injective over a duplicate-free owner namespace: two eigner indices
    resolving to one mark are one index. -/
theorem eignerMarke_inj (u : UProg) (hN : u.eigner.Nodup)
    (a b : Nat) (i : Fin u.marken.length)
    (ha : eignerMarke u a = some i) (hb : eignerMarke u b = some i) : a = b := by
  obtain ⟨m, hma, _, hmi⟩ := eignerMarke_nennt u a i ha
  obtain ⟨k, hmb, _, hki⟩ := eignerMarke_nennt u b i hb
  have hmk : m = k := by rw [← hmi, ← hki]
  rw [hmk] at hma
  obtain ⟨haL, haE⟩ := List.getElem?_eq_some_iff.mp hma
  obtain ⟨hbL, hbE⟩ := List.getElem?_eq_some_iff.mp hmb
  exact hN.eq_of_getElem_eq haL hbL (by rw [haE, hbE])

/-! ## C16 ordinary mark flow: `nimmt`/`gibt` through the mark table -/

/-- The consumed ordinary marks of a function (C16): its `nimmt` names resolved
    against the unit's mark table at stage 0 (`uMarkenPruef` guarantees every name
    resolves for an elaborated unit). -/
def nimmtAt (u : UProg) (f : UFn) : List (Fin u.marken.length × Nat) :=
  f.nimmt.filterMap fun m => (markFin u.marken m).map (·, 0)

/-- The produced ordinary marks of a function (C16): its `gibt` names resolved
    against the unit's mark table at stage 0, EXCEPT owner marks: signatures never
    produce owners (`eigner_nie_erzeugt`), so a `gibt` naming a table's owner mark
    resolves to nothing here (the front end refuses it loudly via `uGibtPruef`). -/
def gibtAt (u : UProg) (f : UFn) : List (Fin u.marken.length × Nat) :=
  f.gibt.filterMap fun m =>
    match markFin u.marken m with
    | none => none
    | some i => if u.tabs.all (fun t => decide (t.owner ≠ some m)) then some (i, 0) else none

/-- A resolved production names no table owner. -/
theorem gibtAt_keinEigner (u : UProg) (f : UFn) (i : Fin u.marken.length) (s : Nat)
    (h : (i, s) ∈ gibtAt u f) :
    u.tabs.all (fun t => decide (t.owner ≠ some (u.marken.get i))) = true := by
  unfold gibtAt at h
  obtain ⟨m, _, hmi⟩ := List.mem_filterMap.mp h
  cases hm : markFin u.marken m with
  | none =>
    simp only [hm, reduceCtorEq] at hmi
  | some j =>
    simp only [hm] at hmi
    cases hall : (u.tabs.all (fun t => decide (t.owner ≠ some m))) with
    | false =>
      simp only [hall, reduceCtorEq] at hmi
    | true =>
      simp only [hall, Option.some_injEq] at hmi
      obtain ⟨rfl, rfl⟩ := hmi
      rw [markFin_get u.marken m i hm]
      exact hall

/-- Every resolved production is a stage-0 mark. -/
theorem gibtAt_stufe (u : UProg) (f : UFn) (i : Fin u.marken.length) (s : Nat)
    (h : (i, s) ∈ gibtAt u f) : s = 0 := by
  unfold gibtAt at h
  obtain ⟨m, _, hmi⟩ := List.mem_filterMap.mp h
  cases hm : markFin u.marken m with
  | none =>
    simp only [hm, reduceCtorEq] at hmi
  | some j =>
    cases hall : (u.tabs.all (fun t => decide (t.owner ≠ some m))) with
    | false =>
      simp only [hm, hall, reduceCtorEq] at hmi
    | true =>
      simp only [hm, hall, Option.some_injEq] at hmi
      obtain ⟨_, hs⟩ := hmi
      exact hs.symm

/-! ## C12 loan flow: `leiht` through the mark table -/

/-- The call-scoped owner loans of a function (C12): its `leiht` names resolved
    against the unit's mark table at stage 0, keeping ONLY table owners: a loan
    is an `OwnerFlow.loans` entry, so a non-owner resolves to nothing here (the
    front end refuses it loudly via `uLeihtPruef`). -/
def leihtAt (u : UProg) (f : UFn) : List (Fin u.marken.length × Nat) :=
  f.leiht.filterMap fun m =>
    match markFin u.marken m with
    | none => none
    | some i => if u.tabs.any (fun t => decide (t.owner = some m)) then some (i, 0) else none

/-- A resolved loan names a table owner: the named table's `owner` is the same name. -/
theorem leihtAt_eigner (u : UProg) (f : UFn) (i : Fin u.marken.length) (s : Nat)
    (h : (i, s) ∈ leihtAt u f) :
    ∃ t : Fin u.tabs.length, (tabAt u t).owner = some (u.marken.get i) := by
  unfold leihtAt at h
  obtain ⟨m, _, hmi⟩ := List.mem_filterMap.mp h
  cases hm : markFin u.marken m with
  | none =>
    simp only [hm, reduceCtorEq] at hmi
  | some j =>
    cases hall : (u.tabs.any (fun t => decide (t.owner = some m))) with
    | false =>
      simp only [hm, hall, reduceCtorEq] at hmi
    | true =>
      simp only [hm, hall, Option.some_injEq] at hmi
      obtain ⟨rfl, rfl⟩ := hmi
      obtain ⟨x, hxu, hx⟩ := List.any_eq_true.mp hall
      have hxown : x.owner = some m := of_decide_eq_true hx
      obtain ⟨n, hn, hxn⟩ := List.mem_iff_get.mp hxu
      refine ⟨⟨n, hn⟩, ?_⟩
      have htab : tabAt u ⟨n, hn⟩ = x := by unfold tabAt; rw [hxn]
      rw [htab, hxown, markFin_get u.marken m i hm]

/-- Every resolved loan is a stage-0 mark. -/
theorem leihtAt_stufe (u : UProg) (f : UFn) (i : Fin u.marken.length) (s : Nat)
    (h : (i, s) ∈ leihtAt u f) : s = 0 := by
  unfold leihtAt at h
  obtain ⟨m, _, hmi⟩ := List.mem_filterMap.mp h
  cases hm : markFin u.marken m with
  | none =>
    simp only [hm, reduceCtorEq] at hmi
  | some j =>
    cases hall : (u.tabs.any (fun t => decide (t.owner = some m))) with
    | false =>
      simp only [hm, hall, reduceCtorEq] at hmi
    | true =>
      simp only [hm, hall, Option.some_injEq] at hmi
      obtain ⟨_, hs⟩ := hmi
      exact hs.symm

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
    have he : eignerAt u t = [] := by unfold eignerAt; rw [ho]
    rw [he] at h
    exact (List.not_mem_nil h).elim
  | some o =>
    refine ⟨o, ho, ?_⟩
    cases hm : markFin u.marken o with
    | none =>
      have he : eignerAt u t = [] := by unfold eignerAt; rw [ho, hm]
      rw [he] at h
      exact (List.not_mem_nil h).elim
    | some j =>
      have he : eignerAt u t = [j] := by unfold eignerAt; rw [ho, hm]
      rw [he] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      subst h
      exact hm

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
