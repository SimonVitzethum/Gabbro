module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil12

@[expose] public section



namespace Gabbro.Grammatik.Parser.UebersetzeAllg

open Gabbro.Grammatik.Parser.Uebersetze

/-- The table at an index. -/
def tabAt (u : UProg) (t : Fin u.tabs.length) : UTab :=
  u.tabs.get t

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
  have hp : strEq (marken.get i) m = true :=
    List.find?_some (p := fun j : Fin marken.length => strEq (marken.get j) m) h
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

/-- The consumed ordinary marks (C16), at stage 0. Owner consumption travels
    through `terminalMovesAt` instead, with the C09 escrow and `after := none`. -/
def nimmtAt (u : UProg) (f : UFn) : List (Fin u.marken.length × Nat) :=
  f.nimmt.filterMap fun m =>
    match markFin u.marken m with
    | none => none
    | some i => if u.tabs.all (fun t => decide (t.owner ≠ some m)) then some (i, 0) else none

/-- The produced ordinary marks of a function (C16): its `gibt` names resolved
    against the unit's mark table at stage 0, EXCEPT owner marks: signatures never
    produce owners (`eigner_nie_erzeugt`), so a `gibt` naming a table's owner mark
    resolves to nothing here (the front end refuses it loudly via `uGibtPruef`). -/
def gibtAt (u : UProg) (f : UFn) : List (Fin u.marken.length × Nat) :=
  f.gibt.filterMap fun m =>
    match markFin u.marken m with
    | none => none
    | some i => if u.tabs.all (fun t => decide (t.owner ≠ some m)) then some (i, 0) else none

/-- A filtered mark flow retains the resolving name, its guard and stage zero. -/
private theorem markFlow_origin (marken names : List String) (keep : String → Bool)
    {i : Fin marken.length} {s : Nat}
    (h : (i, s) ∈ names.filterMap (fun m =>
      match markFin marken m with
      | none => none
      | some j => if keep m then some (j, 0) else none)) :
    ∃ m ∈ names, markFin marken m = some i ∧ keep m = true ∧ s = 0 := by
  obtain ⟨m, hmem, hmi⟩ := List.mem_filterMap.mp h
  cases hm : markFin marken m with
  | none => simp only [hm, reduceCtorEq] at hmi
  | some j =>
    by_cases hk : keep m = true
    · have hpair : (j, 0) = (i, s) := by simpa [hm, hk] using hmi
      have hi := congrArg Prod.fst hpair
      have hs := congrArg Prod.snd hpair
      cases hi
      exact ⟨m, hmem, hm, hk, hs.symm⟩
    · simp [hm, hk] at hmi

/-- A resolved production names no table owner. -/
theorem gibtAt_keinEigner (u : UProg) (f : UFn) (i : Fin u.marken.length) (s : Nat)
    (h : (i, s) ∈ gibtAt u f) :
    u.tabs.all (fun t => decide (t.owner ≠ some (u.marken.get i))) = true := by
  unfold gibtAt at h
  obtain ⟨m, _, hm, hall, _⟩ := markFlow_origin u.marken f.gibt
    (fun m => u.tabs.all (fun t => decide (t.owner ≠ some m))) (i := i) (s := s) (by
      obtain ⟨m, member, value⟩ := List.mem_filterMap.mp h
      refine List.mem_filterMap.mpr ⟨m, member, ?_⟩
      cases resolved : markFin u.marken m <;> simpa only [resolved] using value)
  rw [markFin_get u.marken m i hm]
  exact hall

/-- Every resolved production is a stage-0 mark. -/
theorem gibtAt_stufe (u : UProg) (f : UFn) (i : Fin u.marken.length) (s : Nat)
    (h : (i, s) ∈ gibtAt u f) : s = 0 := by
  unfold gibtAt at h
  obtain ⟨_, _, _, _, hs⟩ := markFlow_origin u.marken f.gibt
    (fun m => u.tabs.all (fun t => decide (t.owner ≠ some m))) (i := i) (s := s) (by
      obtain ⟨m, member, value⟩ := List.mem_filterMap.mp h
      refine List.mem_filterMap.mpr ⟨m, member, ?_⟩
      cases resolved : markFin u.marken m <;> simpa only [resolved] using value)
  exact hs

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
  obtain ⟨m, _, hm, hall, _⟩ := markFlow_origin u.marken f.leiht
    (fun m => u.tabs.any (fun t => decide (t.owner = some m))) (i := i) (s := s) (by
      obtain ⟨m, member, value⟩ := List.mem_filterMap.mp h
      refine List.mem_filterMap.mpr ⟨m, member, ?_⟩
      cases resolved : markFin u.marken m <;> simpa only [resolved] using value)
  obtain ⟨x, hxu, hx⟩ := List.any_eq_true.mp hall
  have hxown : x.owner = some m := of_decide_eq_true hx
  obtain ⟨t, ht⟩ := List.mem_iff_get.mp hxu
  refine ⟨t, ?_⟩
  change (u.tabs.get t).owner = some (u.marken.get i)
  rw [ht, hxown, markFin_get u.marken m i hm]

/-- Every resolved loan is a stage-0 mark. -/
theorem leihtAt_stufe (u : UProg) (f : UFn) (i : Fin u.marken.length) (s : Nat)
    (h : (i, s) ∈ leihtAt u f) : s = 0 := by
  unfold leihtAt at h
  obtain ⟨_, _, _, _, hs⟩ := markFlow_origin u.marken f.leiht
    (fun m => u.tabs.any (fun t => decide (t.owner = some m))) (i := i) (s := s) (by
      obtain ⟨m, member, value⟩ := List.mem_filterMap.mp h
      refine List.mem_filterMap.mpr ⟨m, member, ?_⟩
      cases resolved : markFin u.marken m <;> simpa only [resolved] using value)
  exact hs

/-- The lock at an index. -/
def lockAt (u : UProg) (l : Fin u.locks.length) : ULock :=
  u.locks.get l

/-- The `n`th signature source of a unit: its functions, then its pointer types. -/
def sigEintrag (u : UProg) (n : Nat) : Option UFn := (u.fns ++ u.ptrs)[n]?

/-- `sigEintrag` from the unit's cache: one index, no walk of the lists. -/
def sigEintragSchnell (u : UProg) (n : Nat) : Option UFn :=
  u.mitMerk (fun c _ _ => c.sig[n]?) (fun _ => (u.fns ++ u.ptrs)[n]?)
    (fun c h1 h2 => by rw [c.sigTreu, h1, h2, List.getElem?_toArray])

/-- **The cache holds the same entry.** -/
@[csimp] theorem sigEintrag_eq_schnell : @sigEintrag = @sigEintragSchnell := by
  funext u n
  unfold sigEintragSchnell
  rw [UProg.mitMerk_eq]
  try rfl

/-- The function at an index. -/
def fnAt (u : UProg) (f : Fin u.fns.length) : UFn :=
  u.fns.get f

/-- `fnAt` by the unit's signature entries: one index, no walk. -/
def fnAtSchnell (u : UProg) (f : Fin u.fns.length) : UFn :=
  match sigEintrag u f.val with
  | some g => g
  | none => u.fns.get f

/-- **The entry is the same function.** -/
@[csimp] theorem fnAt_eq_schnell : @fnAt = @fnAtSchnell := by
  funext u f
  unfold fnAt fnAtSchnell sigEintrag
  rw [List.getElem?_append_left f.isLt, List.getElem?_eq_getElem f.isLt, List.get_eq_getElem]

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


end Gabbro.Grammatik.Parser.UebersetzeAllg
