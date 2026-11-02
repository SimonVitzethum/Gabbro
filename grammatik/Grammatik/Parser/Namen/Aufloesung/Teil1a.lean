module

public import Grammatik.Parser.Elab.Uebersetze.Teil.Teil2
public import Grammatik.Parser.Namen.Namensraum

import all Init.Data.Repr
import all Init.Data.String.Basic
import all Init.Data.String.Bootstrap
import all Init.Data.String.Decode
import all Init.Data.String.Defs
import all Init.Data.String.Extra
import all Init.Data.String.FindPos
import all Init.Data.String.Hashable
import all Init.Data.String.Iter
import all Init.Data.String.Iter.Basic
import all Init.Data.String.Iter.Intercalate
import all Init.Data.String.Iterate
import all Init.Data.String.Iterator
import all Init.Data.String.Legacy
import all Init.Data.String.Length
import all Init.Data.String.Modify
import all Init.Data.String.OrderInstances
import all Init.Data.String.Pattern
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Pattern.Pred
import all Init.Data.String.Pattern.String
import all Init.Data.String.PosRaw
import all Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Stream
import all Init.Data.String.Subslice
import all Init.Data.String.Substring
import all Init.Data.String.TakeDrop
import all Init.Data.String.Termination
import all Init.Data.String.ToSlice

@[expose] public section



/-!
  File:      Grammatik/Parser/Namen/Aufloesung.lean
  Subject:   **Qualified names of a unit**: every item is named by its full path, and every written
             name is resolved by the name-space rule (`Namensraum.aufloeseK`) before the elaborator
             sees the unit. Two modules may therefore declare items of the same short name -- two
             carriers, two functions, two types -- and stay two items.

  The language rule (SYNTAX.md `usedecl`, `place`), modelled here before the Rust checker follows:

  * **The identity of an item is its path** (module path and name). Short names need not be unique in
    a unit; two items of one path in one module stay a duplicate.
  * **A written name is resolved** where it stands: a local (parameter, `let`, binder) first, else the
    first candidate of `Namensraum.kandidaten` that names a declared item -- the using module and every
    enclosing one, innermost first, then the `use` lines of these modules. A name that resolves to
    nothing but is the short name of some item is refused (it names something not visible from here).
  * **A place head may be a path** (`writes a::C`, `a::C = 1`, `Held(m::L)`): a two-segment path that is
    no reason ground and every longer path names the item it resolves to.
  * After resolution each item carries its **key** (`schluessel`): its short name when no other item of
    the unit has that short name, else its full path joined by `::`. Every resolved reference carries
    the key of its item, so the elaborator, which looks names up by text, sees one text per item and
    the same text at every use. Keys of distinct paths are distinct texts: a short key has no `::`
    (identifiers never contain `:`), a joined key has at least one, and a short key is used only for a
    short name no other item has.
  * `use` items have done their work once the names are resolved and are dropped; module wrappers are
    opened and `pub` marks dropped (as `Uebersetze.uMembers` does; what `pub` demands is checked before,
    `Oeffentlich.lean`).

  A unit without `use` items and with at most one module wrapper (every unit of the corpus models before
  this change) is resolved by `uMembers` alone (`loese_einfach`): there every name is its own key.

  Positions read: every expression, type, effect, contract clause, statement and the item heads of the
  item kinds the elaborator gives a G form. A name at a position the pass does not rewrite keeps its
  text; if it is ambiguous, no item carries that text any more and the elaborator refuses the unit, so a
  missed position can refuse a unit, never bind a name to the wrong item.

  Theorems:
  * `loese_einfach` -- a unit with one name space is resolved as before.
  * `segmente_name` -- a plain name (no `:`) is the one-segment path.
  * `segmente_verbinde` -- a joined path splits back into its segments.
  * **`schluessel_injektiv`** -- distinct items carry distinct keys (segments are identifiers), so the
    elaborator never merges two items.
  * `ref_lokal`, `ref_aufgeloest`, `ref_unsichtbar` -- what a written name becomes: a local stays, a
    resolved name becomes its item's key, a name of an item not visible from here is poisoned.
  * `schluessel_kurz` -- an item whose short name is unique in the unit keeps its short name.
-/

namespace Gabbro.Grammatik.Parser.Aufloesung

open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Namensraum (Pfad Quelle Platz aufloeseK)

set_option maxRecDepth 100000

/-- The segments of a character list split at `::` (`acc` holds the current segment, reversed). -/
def zerlegeZ : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | ':' :: ':' :: rest, acc => acc.reverse :: zerlegeZ rest []
  | c :: rest, acc => zerlegeZ rest (c :: acc)

/-- The segments of a written path (`a::b::c`; a plain name is one segment). Structural over the
    characters, so the kernel reduces it (`String.splitOn` does not). -/
def segmente (s : String) : Pfad := (zerlegeZ s.toList []).map String.ofList

/-- One character other than `:` joins the current segment. -/
theorem zerlegeZ_cons {c : Char} (l acc : List Char) (hc : c ≠ ':') :
    zerlegeZ (c :: l) acc = zerlegeZ l (c :: acc) := by
  conv => lhs; rw [zerlegeZ.eq_def]
  split <;> simp_all

/-- Characters without `:` are one segment. -/
theorem zerlegeZ_ohne (l acc : List Char) (h : ':' ∉ l) : zerlegeZ l acc = [acc.reverse ++ l] := by
  induction l generalizing acc with
  | nil => simp only [zerlegeZ, List.append_nil]
  | cons c rest ih =>
    have hc : c ≠ ':' := fun e => h (e ▸ List.mem_cons_self)
    have hr : ':' ∉ rest := fun m => h (List.mem_cons_of_mem _ m)
    rw [zerlegeZ_cons _ _ hc, ih _ hr]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

/-- **A plain name is one segment**: an identifier (no `:`) resolves as the one-segment path. -/
theorem segmente_name {s : String} (h : ':' ∉ s.toList) : segmente s = [s] := by
  simp only [segmente, zerlegeZ_ohne _ _ h, List.reverse_nil, List.nil_append, List.map_cons,
  String.ofList_toList, List.map_nil]

/-- A segment without `:` followed by `::` closes the segment. -/
theorem zerlegeZ_trenner (l rest acc : List Char) (h : ':' ∉ l) :
    zerlegeZ (l ++ ':' :: ':' :: rest) acc = (acc.reverse ++ l) :: zerlegeZ rest [] := by
  induction l generalizing acc with
  | nil => simp only [↓Char.isValue, List.nil_append, zerlegeZ, List.append_nil]
  | cons c l ih =>
    have hc : c ≠ ':' := fun e => h (e ▸ List.mem_cons_self)
    have hr : ':' ∉ l := fun m => h (List.mem_cons_of_mem _ m)
    rw [List.cons_append, zerlegeZ_cons _ _ hc, ih _ hr]
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

/-- Segments without `:`, joined by `::`, split back into themselves. -/
theorem zerlegeZ_verbinde : ∀ (p : List (List Char)), p ≠ [] → (∀ s ∈ p, ':' ∉ s) →
    zerlegeZ ([':', ':'].intercalate p) [] = p
  | [], h, _ => absurd rfl h
  | [x], _, hs => by
    rw [List.intercalate_singleton, zerlegeZ_ohne _ _ (hs x List.mem_cons_self)]
    simp only [List.reverse_nil, List.nil_append]
  | x :: y :: zs, _, hs => by
    rw [List.intercalate_cons_cons, List.append_assoc]
    rw [show [':', ':'] ++ [':', ':'].intercalate (y :: zs) = ':' :: ':' :: [':', ':'].intercalate (y :: zs)
      from rfl]
    rw [zerlegeZ_trenner _ _ _ (hs x List.mem_cons_self),
      zerlegeZ_verbinde (y :: zs) (List.cons_ne_nil _ _) (fun s m => hs s (List.mem_cons_of_mem _ m))]
    simp only [List.reverse_nil, List.nil_append]

/-- **A joined path splits back into its segments** when no segment contains `:` (identifiers never
    do): `segmente` is the inverse of the joined key. -/
theorem segmente_verbinde {p : Pfad} (hp : p ≠ []) (h : ∀ s ∈ p, ':' ∉ s.toList) :
    segmente ("::".intercalate p) = p := by
  have hz : "::".toList = [':', ':'] := by decide
  simp only [segmente, String.toList_intercalate, hz]
  rw [zerlegeZ_verbinde (p.map String.toList) (by simpa using hp)
    (by simpa using h)]
  simp only [List.map_map, String.ofList_comp_toList, List.map_id_fun, id_eq]


/-- The last segment of a path: the short name. -/
def letzter (p : Pfad) : String := p.getLast?.getD ""

/-- The declared name of an item, if it declares one. -/
def itemName : SItemTief → Option String
  | .taggedByT decl _ => itemName decl
  | .specGroupT n _ _ _ => some n
  | .typeT _ n _ _ _ => some n
  | .constT n _ _ => some n
  | .globT _ n _ _ _ _ _ => some n
  | .fnT s _ => some s.name
  | .protoT s => some s.name
  | .specT s _ => some s.name
  | .asmT s _ => some s.name
  | .formatT n _ _ _ => some n
  | .tableT n _ _ _ _ _ _ => some n
  | .arenaT n _ _ _ _ _ => some n
  | .whyT n _ _ => some n
  | .stateT n _ => some n
  | .devT n _ _ _ => some n
  | .assumT n _ _ _ => some n
  | .axiomT n _ _ _ _ _ => some n
  | .checkT c => some c.cname
  | .atomT n _ _ _ _ => some n
  | .lockT n _ _ _ _ _ _ => some n
  | .rcuT n _ _ => some n
  | .groupT n _ _ => some n
  | .accT n _ _ _ => some n
  | .walkT w => some w.name
  | .entryT e => some e.name
  | .callT c => some c.name
  | .varT n => some n
  | .transT _ s _ => some s.name
  | .gateT it => itemName it
  | .pubT it => itemName it
  | .adaptT s _ _ _ => some s.name
  | _ => none

mutual
/-- **What a unit declares and uses**: the full path of every named item, and every `use` line with the
    module it stands in. -/
def sammleI (von : Pfad) : SItemTief → List Pfad × List (Pfad × Pfad)
  | .modT p b => sammleL (von ++ segmente p) b
  | .useT p => ([], [(von, p)])
  | .pubT it => sammleI von it
  | it => match itemName it with
    | some n => ([von ++ [n]], [])
    | none => ([], [])
def sammleL (von : Pfad) : List SItemTief → List Pfad × List (Pfad × Pfad)
  | [] => ([], [])
  | it :: rest =>
    let a := sammleI von it
    let b := sammleL von rest
    (a.1 ++ b.1, a.2 ++ b.2)
end

/-- The source of a unit for the name-space rule. -/
def quelle (items : List SItemTief) : Quelle :=
  let s := sammleL [] items
  ⟨s.1, s.2⟩

/-- **The key of an item**: its short name when no other declared path ends in it, else its path. -/
def schluessel (namen : List Pfad) (c : Pfad) : String :=
  if (namen.filter fun q => strEq (letzter q) (letzter c)).length == 1 then letzter c
  else "::".intercalate c

/-- The short name of a non-empty path is one of its segments. -/
theorem letzter_mem {c : Pfad} (h : c ≠ []) : letzter c ∈ c := by
  unfold letzter
  cases hl : c.getLast? with
  | none => exact absurd (List.getLast?_eq_none_iff.mp hl) h
  | some x => exact List.mem_of_getLast? hl

/-- **Distinct items carry distinct keys.** Paths are non-empty and their segments are identifiers
    (no `:`): two items with one key are one item. So the elaborator, which looks names up by text,
    never merges two items of a unit. -/
theorem schluessel_injektiv {namen : List Pfad}
    (hok : ∀ p ∈ namen, p ≠ [] ∧ ∀ s ∈ p, ':' ∉ s.toList) {c d : Pfad} (hc : c ∈ namen)
    (hd : d ∈ namen) (h : schluessel namen c = schluessel namen d) : c = d := by
  obtain ⟨hc0, hcs⟩ := hok c hc
  obtain ⟨hd0, hds⟩ := hok d hd
  have hself : ∀ x : String, strEq x x = true := fun x => by simp only [strEq, BEq.rfl]
  -- One short name, one filter.
  have hfil : letzter c = letzter d →
      (namen.filter fun q => strEq (letzter q) (letzter c)) =
        (namen.filter fun q => strEq (letzter q) (letzter d)) := fun e => by rw [e]
  -- A short key is one of the path's segments, so it splits into itself.
  have kurz : ∀ x : Pfad, x ≠ [] → (∀ s ∈ x, ':' ∉ s.toList) → segmente (letzter x) = [letzter x] :=
    fun x h0 hs => segmente_name (hs _ (letzter_mem h0))
  unfold schluessel at h
  split at h <;> split at h
  · -- both short: one filter of length one holds both
    rename_i h1 h2
    have e := hfil h
    have hl : (namen.filter fun q => strEq (letzter q) (letzter c)).length = 1 := beq_iff_eq.mp h1
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl
    have mc : c ∈ namen.filter fun q => strEq (letzter q) (letzter c) := by simp only [List.mem_filter, hc, hself, and_self]
    have md : d ∈ namen.filter fun q => strEq (letzter q) (letzter c) := by
      rw [e]; simp only [List.mem_filter, hd, hself, and_self]
    rw [hx] at mc md
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mc md
    rw [mc, md]
  · -- c short, d joined: d splits into the one segment `letzter c`, so it has c's filter
    rename_i h1 h2
    have sd := segmente_verbinde hd0 hds
    rw [← h, kurz c hc0 hcs] at sd
    have hdl : letzter d = letzter c := by rw [← sd]; rfl
    exact (h2 (by rw [← hfil hdl.symm]; exact h1)).elim
  · -- c joined, d short: symmetric
    rename_i h1 h2
    have sc := segmente_verbinde hc0 hcs
    rw [h, kurz d hd0 hds] at sc
    have hcl : letzter c = letzter d := by rw [← sc]; rfl
    exact (h1 (by rw [hfil hcl]; exact h2)).elim
  · -- both joined: split both
    have := congrArg segmente h
    rwa [segmente_verbinde hc0 hcs, segmente_verbinde hd0 hds] at this


end Gabbro.Grammatik.Parser.Aufloesung
