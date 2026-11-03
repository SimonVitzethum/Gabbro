module

public import Grammatik.Kern.Syntax.Zucker
public import Grammatik.Parser.Elab.Uebersetze

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

/-! ## Declaration index data and signatures (moved from `Teil1`, C16) -/

/-- The table at an index. -/
def tabAt (u : UProg) (t : Fin u.tabs.length) : UTab :=
  u.tabs.get t

/-- The lock at an index. -/
def lockAt (u : UProg) (l : Fin u.locks.length) : ULock :=
  u.locks.get l

def globAt (u : UProg) (g : Fin u.globs.length) : UGlob := u.globs.get g

/-- A lock index by name. -/
def lockIdx : (locks : List ULock) → (n : String) → Except String (Fin locks.length)
  | [], n => .error ("lock unknown: " ++ n)
  | l :: rest, n =>
    if l.name == n then .ok 0
    else match lockIdx rest n with
      | .error e => .error e
      | .ok j => .ok j.succ

/-- The held locks of a function, as indices (names the declaration
    does not know are dropped; `elabU` output never has them). -/
def heldAt (u : UProg) (f : UFn) : List (Fin u.locks.length) :=
  f.held.filterMap fun n => (lockIdx u.locks n).toOption

/-- The write flag of a function at a static. -/
def writesGAt (u : UProg) (f : UFn) (g : Fin u.globs.length) : Bool :=
  f.gputs.any (· == (globAt u g).name)

/-- The write flag of a function at a table. -/
def writesAt (u : UProg) (f : UFn) (t : Fin u.tabs.length) : Bool :=
  f.puts.any (· == (tabAt u t).name)

/-- The signature of an elaborated function (C16): the consumed/produced ordinary
    marks are the `nimmt`/`gibt` names resolved against the unit's mark table
    (`nimmtAt`/`gibtAt`); owner flows stay empty until the C09 handoff wires them. -/
def mkSig (u : UProg) (f : UFn) :
    Signatur (Fin u.tabs.length) (Fin u.globs.length) (Fin u.locks.length) (Fin u.marken.length) where
  params := f.params.map (·.2)
  erg := f.ergTy
  gruende := f.gruende
  haelt := heldAt u f
  schreibt := writesAt u f
  gschreibt := writesGAt u f
  konsumiert := nimmtAt u f
  produziert := gibtAt u f
  boden := f.boden

/-- The dummy signature: no parameters, no rights. -/
def dummySig (u : UProg) :
    Signatur (Fin u.tabs.length) (Fin u.globs.length) (Fin u.locks.length) (Fin u.marken.length) where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => false
  gschreibt := fun _ => false
  konsumiert := []
  produziert := []

/-- The signatures of the unit: the functions', then the pointer types' (`UProg.ptrs`). -/
def sigFns (u : UProg) : List UFn := u.fns ++ u.ptrs

/-- The `n`th signature, or the dummy (an out-of-range number names
    no function and no pointer type). -/
def sigAt (u : UProg) (n : Nat) :
    Signatur (Fin u.tabs.length) (Fin u.globs.length) (Fin u.locks.length) (Fin u.marken.length) :=
  if h : n < (sigFns u).length then mkSig u ((sigFns u).get ⟨n, h⟩) else dummySig u

/-- **Conformance, decided** (`SigPasst` over the finite carriers of an elaborated unit): the first
    signature fits the second, with the same owner flow (the C09 handoff is part of conformance). -/
def sigPasstB {a b c : Nat} {Marke : Type} [DecidableEq Marke] (rang : Fin c → Int) (S T : Signatur (Fin a) (Fin b) (Fin c) Marke) : Bool :=
  decide (S.params = T.params) && decide (S.erg = T.erg) && decide (S.gruende = T.gruende) &&
  (List.finRange a).all (fun t => !S.schreibt t || T.schreibt t) &&
  (List.finRange b).all (fun g => !S.gschreibt g || T.gschreibt g) &&
  decide (S.konsumiert = T.konsumiert) && decide (S.produziert = T.produziert) &&
  S.haelt.all (fun L => decide (L ∈ T.haelt)) &&
  T.haelt.all (fun L => decide (L ∈ S.haelt) ||
    (match S.boden with | some c => decide (rang L < c) | none => false)) &&
  (match T.boden with
    | none => true
    | some c => match S.boden with | some c' => decide (c ≤ c') | none => false) &&
  decide (S.owner = T.owner)

theorem sigPasstB_ok {a b c : Nat} {Marke : Type} [DecidableEq Marke] {rang : Fin c → Int} {S T : Signatur (Fin a) (Fin b) (Fin c) Marke}
    (h : sigPasstB rang S T = true) : SigPasst rang S T := by
  unfold sigPasstB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, he⟩, hg⟩, hw⟩, hgw⟩, hk⟩, hpr⟩, hh⟩, hx⟩, hb⟩, ho⟩ := h
  refine ⟨hp, he, hg, fun t ht => ?_, fun g' hg' => ?_, hk, hpr, fun L hL => hh L hL, fun L hL hn => ?_,
    fun c hc => ?_, of_decide_eq_true ho⟩
  · rcases hw t (List.mem_finRange t) with h1 | h1
    · rw [ht] at h1; cases h1
    · exact h1
  · rcases hgw g' (List.mem_finRange g') with h1 | h1
    · rw [hg'] at h1; cases h1
    · exact h1
  · rcases hx L hL with h1 | h1
    · exact absurd h1 hn
    · revert h1
      cases hS : S.boden with
      | none => intro h1; cases h1
      | some c => intro h1; exact ⟨c, rfl, of_decide_eq_true h1⟩
  · rw [hc] at hb
    revert hb
    cases hS : S.boden with
    | none => intro h1; cases h1
    | some c' => intro h1; exact ⟨c', rfl, of_decide_eq_true h1⟩

/-- `f` conforms to the signature number `n` of the unit: a live number, and the signatures fit. -/
def passtAt (u : UProg) (f : Fin u.fns.length) (n : Nat) : Bool :=
  decide (n < (sigFns u).length) && sigPasstB (fun l => (lockAt u l).rank) (sigAt u f.val) (sigAt u n)

theorem passtAt_ok (u : UProg) (f : Fin u.fns.length) (n : Nat) (h : passtAt u f n = true) :
    SigPasst (fun l => (lockAt u l).rank) (sigAt u f.val) (sigAt u n) :=
  sigPasstB_ok (Bool.and_eq_true_iff.mp h).2

theorem passtAt_lt (u : UProg) (f : Fin u.fns.length) (n : Nat) (h : passtAt u f n = true) :
    n < (sigFns u).length :=
  of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

end Gabbro.Grammatik.Parser.UebersetzeAllg
