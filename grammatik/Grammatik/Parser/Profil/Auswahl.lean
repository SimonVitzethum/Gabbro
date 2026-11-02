module

public import Grammatik.Parser.Item.ElementTief

@[expose] public section

/-!
  File:      Grammatik/Parser/Profil/Auswahl.lean
  Subject:   **C14: build selection.** `when TESTBUILD` over the ORIGINAL parsed items, in an explicit
             build mode, interpreted recursively through modules and `pub` wrappers BEFORE any name,
             constant, target, start or profile extraction.

  * `BauModus` -- the shipping build (default; a gated item contributes nothing) and the test build (every
    item present, the gate removed);
  * `waehleL` -- the selection: a function of the original tree and the mode, nothing else; module scopes are
    kept (a module wrapper stays around its selected members), so name resolution and `Aufloesung.loese` see
    the same scopes the source wrote;
  * `Selection` -- the certificate: the original items, the mode, and the selected items with the proof that
    they ARE the selection of the original (the relation the unit adapter and `Prepared` carry, replacing
    "selected = original");
  * `waehleL_gatefrei` -- the selected tree has no gate left, in either mode; `waehleL_id` -- a tree without
    a gate is its own selection in either mode (the unit of before);
  * `reserviertL` -- the reserved identifier (`G003`): `TESTBUILD` declared as a name is refused.

  Closure of the selected tree (`G001`: shipping code calling a gated function) is not a second check: the
  selected tree goes through name resolution and the elaborator, which refuse a name no selected item
  declares. `G002` (a `when` condition other than `TESTBUILD`) is refused by the parser (`parseItemTief`).
  Function-tail gates have no canonical parse (`FnSig` carries no gate field): the parser refuses them and
  that refusal is retained.
-/

namespace Gabbro.Grammatik.Parser.Auswahl

/-- Which build is generated. The shipping build is the default of every caller that does not ask for the
    test build, so that forgetting the flag loses test code loudly rather than shipping it silently. -/
inductive BauModus where
  | auslieferung
  | pruefbau
  deriving DecidableEq, Repr

mutual
/-- The selection of one item: a gate keeps its item in the test build and removes it in the shipping build;
    a module keeps its wrapper around its selected members; `pub` stays on what stays. -/
def waehleI (m : BauModus) : SItemTief → List SItemTief
  | .modT n b => [.modT n (waehleL m b)]
  | .pubT it => (waehleI m it).map SItemTief.pubT
  | .gateT it =>
    match m with
    | .auslieferung => []
    | .pruefbau => waehleI m it
  | it => [it]
/-- The selection of an item list, in order. -/
def waehleL (m : BauModus) : List SItemTief → List SItemTief
  | [] => []
  | it :: rest => waehleI m it ++ waehleL m rest
end

mutual
/-- No gate stands anywhere in the item: not under a module, not under `pub`. -/
def gatefreiI : SItemTief → Bool
  | .modT _ b => gatefreiL b
  | .pubT it => gatefreiI it
  | .gateT _ => false
  | _ => true
/-- No gate stands anywhere in the list. -/
def gatefreiL : List SItemTief → Bool
  | [] => true
  | it :: rest => gatefreiI it && gatefreiL rest
end

/-- The gate of an item in the shipping build removes it. -/
theorem waehleI_gate_auslieferung (it : SItemTief) :
    waehleI .auslieferung (.gateT it) = [] := by
  first | rfl | simp only [waehleI]

/-- The gate of an item in the test build is the selection of its item. -/
theorem waehleI_gate_pruefbau (it : SItemTief) :
    waehleI .pruefbau (.gateT it) = waehleI .pruefbau it := by
  first | rfl | simp only [waehleI]

/-- Selection distributes over concatenation. -/
theorem waehleL_append (m : BauModus) (xs ys : List SItemTief) :
    waehleL m (xs ++ ys) = waehleL m xs ++ waehleL m ys := by
  induction xs with
  | nil => simp only [List.nil_append, waehleL]
  | cons x xs ih => simp only [List.cons_append, waehleL, ih, List.append_assoc]

theorem gatefreiL_map_pub (l : List SItemTief) :
    gatefreiL (l.map SItemTief.pubT) = gatefreiL l := by
  induction l with
  | nil => simp only [List.map_nil, gatefreiL]
  | cons x xs ih => simp only [List.map_cons, gatefreiL, gatefreiI, ih]

theorem gatefreiL_append (l1 l2 : List SItemTief) (a : gatefreiL l1 = true) (b : gatefreiL l2 = true) :
    gatefreiL (l1 ++ l2) = true := by
  induction l1 with
  | nil => simpa only [List.nil_append] using b
  | cons y ys ih =>
      simp only [gatefreiL, Bool.and_eq_true] at a
      simp only [List.cons_append, gatefreiL, Bool.and_eq_true]
      exact ⟨a.1, ih a.2⟩

mutual
/-- **The selection of a tree without gates is the tree**, in either mode. -/
theorem waehleI_id (m : BauModus) (it : SItemTief) (h : gatefreiI it = true) :
    waehleI m it = [it] := by
  cases it with
  | modT n b =>
      have ih := waehleL_id m b (by simpa only [gatefreiI] using h)
      simp only [waehleI, ih]
  | pubT x =>
      have ih := waehleI_id m x (by simpa only [gatefreiI] using h)
      simp only [waehleI, ih, List.map_cons, List.map_nil]
  | gateT x => simp only [gatefreiI, Bool.false_eq_true] at h
  | _ => simp [waehleI]
/-- The list form. -/
theorem waehleL_id (m : BauModus) (its : List SItemTief) (h : gatefreiL its = true) :
    waehleL m its = its := by
  cases its with
  | nil => simp only [waehleL]
  | cons x xs =>
      simp only [gatefreiL, Bool.and_eq_true] at h
      simp only [waehleL, waehleI_id m x h.1, waehleL_id m xs h.2, List.singleton_append]
end

mutual
/-- **The selection of an item has no gate left**, in either mode. -/
theorem waehleI_gatefrei (m : BauModus) (it : SItemTief) : gatefreiL (waehleI m it) = true := by
  cases it with
  | modT n b =>
      have ih := waehleL_gatefrei m b
      simp only [waehleI, gatefreiL, gatefreiI, ih, Bool.and_true]
  | pubT x =>
      have ih := waehleI_gatefrei m x
      simp only [waehleI, gatefreiL_map_pub]
      exact ih
  | gateT x =>
      cases m with
      | auslieferung => simp only [waehleI, gatefreiL]
      | pruefbau =>
          have ih := waehleI_gatefrei BauModus.pruefbau x
          simpa only [waehleI] using ih
  | _ => simp [waehleI, gatefreiL, gatefreiI]
/-- The list form. -/
theorem waehleL_gatefrei (m : BauModus) (its : List SItemTief) :
    gatefreiL (waehleL m its) = true := by
  cases its with
  | nil => simp only [waehleL, gatefreiL]
  | cons x xs =>
      have h1 := waehleI_gatefrei m x
      have h2 := waehleL_gatefrei m xs
      simp only [waehleL]
      exact gatefreiL_append _ _ h1 h2
end

/-! ## The reserved identifier -/

/-- The name an item declares, for the kinds a program names; every other kind declares none here. -/
def deklName : SItemTief → Option String
  | .typeT _ n _ _ _ => some n
  | .constT n _ _ => some n
  | .globT _ n _ _ _ _ _ => some n
  | .fnT s _ => some s.name
  | .protoT s => some s.name
  | .specT s _ => some s.name
  | .asmT s _ => some s.name
  | .tableT n _ _ _ _ _ _ => some n
  | .arenaT n _ _ _ _ _ => some n
  | .whyT n _ _ => some n
  | .assumT n _ _ _ => some n
  | .atomT n _ _ _ _ => some n
  | .lockT n _ _ _ _ _ _ => some n
  | _ => none

mutual
/-- `TESTBUILD` is declared as a name somewhere in the item (`G003`): it is the reserved gate word. -/
def reserviertI : SItemTief → Bool
  | .modT _ b => reserviertL b
  | .pubT it => reserviertI it
  | .gateT it => reserviertI it
  | it =>
    match deklName it with
    | some n => strEq n "TESTBUILD"
    | none => false
/-- The list form. -/
def reserviertL : List SItemTief → Bool
  | [] => false
  | it :: rest => reserviertI it || reserviertL rest
end

/-! ## The certificate -/

/-- **The selection certificate**: the original parsed items, the explicit build mode, and the selected items
    with the proof that they are the selection of the original. Everything downstream (name resolution, the
    elaborator, start/target extraction, profile binding) reads `ausgewaehlt`; the original stays as the
    evidence of the lex/parse that produced it. -/
structure Selection where
  modus : BauModus
  original : List SItemTief
  ausgewaehlt : List SItemTief
  gewaehlt : ausgewaehlt = waehleL modus original

/-- The certificate of an original tree and a mode. -/
def Selection.von (m : BauModus) (items : List SItemTief) : Selection :=
  ⟨m, items, waehleL m items, rfl⟩

/-- A selection is admitted when the original declares no reserved name. -/
def Selection.zulaessig (s : Selection) : Bool := !reserviertL s.original

/-- The selected tree of any certificate has no gate. -/
theorem Selection.gatefrei (s : Selection) : gatefreiL s.ausgewaehlt = true := by
  rw [s.gewaehlt]
  exact waehleL_gatefrei s.modus s.original

/-- A tree without gates is its own selection in either mode. -/
theorem Selection.von_gatefrei (m : BauModus) {items : List SItemTief}
    (h : gatefreiL items = true) : (Selection.von m items).ausgewaehlt = items :=
  waehleL_id m items h

end Gabbro.Grammatik.Parser.Auswahl
