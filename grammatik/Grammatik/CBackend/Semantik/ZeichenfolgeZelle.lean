/-
  File:      Grammatik/ZeichenfolgeZelle.lean
  Subject:   A bounded string as the CELL of an aggregate (table slot field, record field,
             array element): the copy-in / copy-out discipline and its soundness.
             SPRACHE-EFFIZIENZ #13 -- design pinned in Lean BEFORE any checker rule.

  Today a `string max N` lives only in parameters, results and locals (`N465`), because the
  length facts (`N454` index below the length, `N455` copy fits) are flow facts about a NAME and
  die at every write and call. A cell in memory can be rewritten between a check and a use, so
  a fact about the cell itself would be unsound.

  The design is therefore VALUE-ONLY: a cell is read WHOLE into a local (copy-in) and written
  WHOLE from a string value (copy-out); every length fact is then a fact about the local, which
  the existing pass already follows. This file proves what that discipline needs, over every
  `max`, every cell index and every aggregate size:

  * `laden_speichern`      copy-out then copy-in at the same cell returns the stored live prefix;
  * `laden_speichern_ne`   copy-out at one cell leaves every other cell alone;
  * `laden_len`            a loaded string always satisfies `len <= max` (the local starts with
                           the fact the pass assumes of a `string max N` name);
  * `zelleBytes_le_C`      the native size of a cell (narrow length word + max bytes) is never
                           larger than the C layout (`4 + max`).
-/

import Grammatik.CBackend.Semantik.ZeichenfolgeC
import Grammatik.Speichermodell.Darstellung

namespace Gabbro.Grammatik

/-- An aggregate of `n` string cells of max `max`: one `CString max` per index. -/
def Zellen (max n : Nat) : Type := Fin n → CString max

/-- Copy-out: write the string `s` (of max `m`, `s.len <= max`, the `N455` copy rule) whole into
    cell `i`. -/
def speichern {max n m : Nat} (z : Zellen max n) (i : Fin n) (s : CString m) :
    Option (Zellen max n) :=
  match ckopie max s with
  | none => none
  | some r => some (fun j => if j = i then r else z j)

/-- Copy-in: read cell `i` whole into a local. -/
def laden {max n : Nat} (z : Zellen max n) (i : Fin n) : CString max := z i

/-- A loaded string satisfies the fact the pass assumes of a `string max N` name. -/
theorem laden_len {max n : Nat} (z : Zellen max n) (i : Fin n) : (laden z i).len ≤ max :=
  (z i).len_ok

/-- Copy-out then copy-in returns the stored live prefix, for every cell and every string that
    fits. -/
theorem laden_speichern {max n m : Nat} (z : Zellen max n) (i : Fin n) (s : CString m)
    (h : s.len ≤ max) :
    ∃ z' : Zellen max n, speichern z i s = some z' ∧ nimm (laden z' i) = nimm s := by
  obtain ⟨r, hr, hn⟩ := ckopie_nimm max s h
  refine ⟨fun j => if j = i then r else z j, ?_, ?_⟩
  · simp [speichern, hr]
  · simp [laden, hn]

/-- Copy-out at one cell leaves every other cell alone (the frame of the store). -/
theorem laden_speichern_ne {max n m : Nat} (z : Zellen max n) (i j : Fin n) (s : CString m)
    (hij : j ≠ i) (z' : Zellen max n) (h : speichern z i s = some z') :
    laden z' j = laden z j := by
  unfold speichern at h
  cases hk : ckopie max s with
  | none => simp [hk] at h
  | some r =>
      simp only [hk] at h
      have hz : z' = fun j => if j = i then r else z j := (Option.some.inj h).symm
      subst hz
      simp [laden, hij]

/-- A store of a string that does NOT fit is refused: nothing is written (the checker's `N455`
    has already ruled the case out). -/
theorem speichern_zu_lang {max n m : Nat} (z : Zellen max n) (i : Fin n) (s : CString m)
    (h : max < s.len) : speichern z i s = none := by
  unfold speichern ckopie
  have : ¬ s.len ≤ max := by omega
  simp [this]

/-! ### Native size of a cell -/

/-- Bytes of one string cell in the native layout: the narrowest length word that holds `max`,
    plus the `max` content bytes (no NUL terminator). -/
def zelleBytes (max : Nat) : Nat :=
  Grammatik.Speichermodell.Darstellung.zellBytes
    (Grammatik.Speichermodell.Darstellung.bits 0 (max : Int)) + max

/-- The C layout of lane 261 pays a four-byte length word whatever the max. -/
def zelleBytesC (max : Nat) : Nat := 4 + max

/-- The narrow cell is never larger than the C cell when `max < 2^32`. -/
theorem zelleBytes_le_C (max : Nat) (h : max < 2 ^ 32) : zelleBytes max ≤ zelleBytesC max := by
  unfold zelleBytes zelleBytesC
  have hb := Grammatik.Speichermodell.Darstellung.schmal_le_wort 0 (max : Int) 4 (by omega)
    (by omega) (by
      have : ((2 : Int) ^ (8 * 4)) = ((2 ^ 32 : Nat) : Int) := by simp
      omega)
  unfold Grammatik.Speichermodell.Darstellung.schmalBytes
    Grammatik.Speichermodell.Darstellung.wortBytes at hb
  omega

/-! ### Witnesses (non-degenerate) -/

/-- Two cells of max 8, both holding "hi" (length 2): a fixture with live data. -/
def zelleFix2 : Zellen 8 2 :=
  fun _ => ⟨2, [104, 105, 0, 0, 0, 0, 0, 0], rfl, by decide, by decide⟩

/-- A five-byte string stored into cell 1 of the fixture. -/
def zelleFixS : CString 5 :=
  ⟨5, [104, 101, 108, 108, 111], rfl, by decide, by decide⟩

example : ∃ z', speichern zelleFix2 ⟨1, by decide⟩ zelleFixS = some z'
    ∧ nimm (laden z' ⟨1, by decide⟩) = [104, 101, 108, 108, 111] := by
  obtain ⟨z', h1, h2⟩ := laden_speichern zelleFix2 ⟨1, by decide⟩ zelleFixS (by decide)
  exact ⟨z', h1, by rw [h2]; rfl⟩

/-- Cell 0 is untouched by the store into cell 1. -/
example : ∀ z', speichern zelleFix2 ⟨1, by decide⟩ zelleFixS = some z' →
    nimm (laden z' ⟨0, by decide⟩) = [104, 105] := by
  intro z' h
  rw [laden_speichern_ne zelleFix2 ⟨1, by decide⟩ ⟨0, by decide⟩ zelleFixS (by decide) z' h]
  rfl

example : zelleBytes 5 = 6 := by decide
example : zelleBytes 100 = 101 := by decide
example : zelleBytes 300 = 302 := by decide
example : zelleBytesC 5 = 9 := by decide

#print axioms laden_speichern
#print axioms laden_speichern_ne
#print axioms zelleBytes_le_C

/- CUTS: the model has no `Ty` form for strings and the exporter still refuses a string
   (`LG002`), so a program with a string cell stays UNCERTIFIED; this file justifies the
   checker rule, it does not put strings into the goal theorem. Concurrent writers to a cell
   are the weak-memory model's business (a whole-cell copy is not atomic); a string cell
   shared between threads needs the same lock discipline as any other carrier. -/

end Gabbro.Grammatik
