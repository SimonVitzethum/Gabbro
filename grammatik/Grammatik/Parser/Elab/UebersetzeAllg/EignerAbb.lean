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

end Gabbro.Grammatik.Parser.UebersetzeAllg
