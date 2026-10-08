/-
  File:      Grammatik/GabbroV/GvParserFragment4.lean
  Subject:   GabbroV bridge: two more elaboration cases (agent 02,
             second follow-up).

  After inert items (108), prototypes and bound normalization
  (`GvParserFragment3.lean`), the remaining elaboration blockers over
  all 157 corpus files are measured in REPORT-02.md. Of those, the two
  most common actionable ones are dropped here, cumulatively on
  `elabU04`: grounds (`grundT`: proof facts with no elaborable
  content, 5 first-offense) and formats (`formatT`: byte layouts, 2
  first-offense). Uses of either fail loudly downstream (unknown
  names); unreferenced ones are inert, like dropped statics. Everything
  else still refused is proved refused. `Parser/` untouched.
-/
import Grammatik.GabbroV.GvParserFragment3
import Grammatik.Parser.Uebersetze

namespace Gabbro.Grammatik.GabbroV.GvParserFragment4

open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.GabbroV.GvParserFragment
open Gabbro.Grammatik.GabbroV.GvParserFragment3

/-- **Is this a ground definition?** (`grundT`: named proof facts,
    `ElementTief.lean`). -/
def istGrund : SItemTief → Bool
  | .grundT .. => true
  | _ => false

/-- **Drop top-level grounds.** -/
def dropGrund : List SItemTief → List SItemTief
  | [] => []
  | it :: rest =>
    if istGrund it then dropGrund rest else it :: dropGrund rest

/-- **Elaborate like `elabU04` after dropping grounds.** -/
def elabU05 (items : List SItemTief) : Except String UProg :=
  elabU04 (dropGrund (uMembers items))

/-- **Dropping changes nothing on ground-free lists.** -/
theorem dropGrund_id (l : List SItemTief)
    (h : ∀ it ∈ l, istGrund it = false) :
    dropGrund l = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : istGrund hd = false :=
      h hd (List.mem_cons.mpr (Or.inl rfl))
    have htl : ∀ it ∈ tl, istGrund it = false := fun it hm =>
      h it (List.mem_cons.mpr (Or.inr hm))
    simp [dropGrund, hhd, ih htl]

/-- **On units whose unwrapped items are ground-free the new
    elaborator IS `elabU04`.** -/
theorem elabU05_stimmt (items : List SItemTief)
    (h : dropGrund (uMembers items) = uMembers items) :
    elabU05 items = elabU04 (uMembers items) := by
  show elabU04 (dropGrund (uMembers items)) = elabU04 (uMembers items)
  rw [h]

/-- **Joint witness for `elabU05_stimmt`**: 104's items are
    ground-free and both elaborators agree on them. -/
theorem elabU05_stimmt_zeuge :
    dropGrund (uMembers items104) = uMembers items104 ∧
    elabU05 items104 = elabU04 items104 :=
  ⟨rfl, rfl⟩

/-- **Units that still carry an off-fragment item are still refused.**
    Only inert items, prototypes and grounds are forgiven. -/
theorem elabU05_verweigert_noch (items : List SItemTief)
    (h : ∃ it ∈ uMembers (ohneInert (uMembers (normProg (dropGrund (uMembers items))))),
      istGegenstand it = true) :
    ∃ e, elabU05 items = .error e := by
  have hR := uRestFehler_faellt _ h
  exact ⟨_, elabU_bei_RestFehler _ _ hR⟩

/-- **Synthetic witness items**: one table, one unreferenced ground,
    one clean function. -/
def wGrundItems : List SItemTief :=
  [.modulT "beispiel::zeuge"
    [.tabelleT "T" (.some (.lit 1)) .none .none false
      [.tPlatz [{ fname := "v", ftyp := .atom "u32",
                  pos := .none, bezug := .none, wo := .none,
                  reserviert := false, byOps := false }]],
    .grundT "g" [("x", .lit 0, "t")] false,
    .funktionT
      { art := "impl", name := "f", params := [],
        ergebnis := .none, fehler := .none, klauseln := [] }
      (.block [] .none)]]

/-- **Refused before**: `elabU04` stops at the ground. -/
theorem wGrund_vorher :
    beqElabU (elabU04 wGrundItems)
      (.error "Gegenstand ohne G-Form") = true := by
  decide

/-- **Elaborates now**: `elabU05` yields the table and the function. -/
theorem wGrund_jetzt :
    beqElabU (elabU05 wGrundItems) (.ok wProtoProg) = true := by
  decide

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment4.dropGrund_id
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment4.elabU05_stimmt
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment4.elabU05_stimmt_zeuge
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment4.elabU05_verweigert_noch
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment4.wGrund_vorher
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment4.wGrund_jetzt

/-- **Is this a format declaration?** (`formatT`: byte layouts,
    `ElementTief.lean`). -/
def istFormat : SItemTief → Bool
  | .formatT .. => true
  | _ => false

/-- **Drop top-level formats.** -/
def dropFormat : List SItemTief → List SItemTief
  | [] => []
  | it :: rest =>
    if istFormat it then dropFormat rest else it :: dropFormat rest

/-- **Elaborate like `elabU05` after dropping formats.** -/
def elabU06 (items : List SItemTief) : Except String UProg :=
  elabU05 (dropFormat (uMembers items))

/-- **Dropping changes nothing on format-free lists.** -/
theorem dropFormat_id (l : List SItemTief)
    (h : ∀ it ∈ l, istFormat it = false) :
    dropFormat l = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : istFormat hd = false :=
      h hd (List.mem_cons.mpr (Or.inl rfl))
    have htl : ∀ it ∈ tl, istFormat it = false := fun it hm =>
      h it (List.mem_cons.mpr (Or.inr hm))
    simp [dropFormat, hhd, ih htl]

/-- **On units whose unwrapped items are format-free the new
    elaborator IS `elabU05`.** -/
theorem elabU06_stimmt (items : List SItemTief)
    (h : dropFormat (uMembers items) = uMembers items) :
    elabU06 items = elabU05 (uMembers items) := by
  show elabU05 (dropFormat (uMembers items)) = elabU05 (uMembers items)
  rw [h]

/-- **Joint witness for `elabU06_stimmt`**: 104's items are
    format-free and both elaborators agree on them. -/
theorem elabU06_stimmt_zeuge :
    dropFormat (uMembers items104) = uMembers items104 ∧
    elabU06 items104 = elabU05 items104 :=
  ⟨rfl, rfl⟩

/-- **Units that still carry an off-fragment item are still refused.**
    Only inert items, prototypes, grounds and formats are forgiven. -/
theorem elabU06_verweigert_noch (items : List SItemTief)
    (h : ∃ it ∈ uMembers (ohneInert (uMembers (normProg (dropGrund (uMembers (dropFormat (uMembers items))))))),
      istGegenstand it = true) :
    ∃ e, elabU06 items = .error e := by
  have hR := uRestFehler_faellt _ h
  exact ⟨_, elabU_bei_RestFehler _ _ hR⟩

/-- **Synthetic witness items**: one table, one unreferenced format,
    one clean function. -/
def wFormatItems : List SItemTief :=
  [.modulT "beispiel::zeuge"
    [.tabelleT "T" (.some (.lit 1)) .none .none false
      [.tPlatz [{ fname := "v", ftyp := .atom "u32",
                  pos := .none, bezug := .none, wo := .none,
                  reserviert := false, byOps := false }]],
    .formatT "F" .none .none
      [{ fname := "v", ftyp := .atom "u32",
         pos := .none, bezug := .none, wo := .none,
         reserviert := false, byOps := false }],
    .funktionT
      { art := "impl", name := "f", params := [],
        ergebnis := .none, fehler := .none, klauseln := [] }
      (.block [] .none)]]

/-- **Refused before**: `elabU05` stops at the format. -/
theorem wFormat_vorher :
    beqElabU (elabU05 wFormatItems)
      (.error "Gegenstand ohne G-Form") = true := by
  decide

/-- **Elaborates now**: `elabU06` yields the table and the function. -/
theorem wFormat_jetzt :
    beqElabU (elabU06 wFormatItems) (.ok wProtoProg) = true := by
  decide

/-- **108 survives the whole chain**: the tip elaborator still yields
    the pasted program (108 carries no grounds or formats). -/
theorem w108_tip :
    beqElabU (elabU06 w108items) (.ok w108prog) = true := by
  decide

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment4.dropFormat_id
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment4.elabU06_stimmt
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment4.elabU06_stimmt_zeuge
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment4.elabU06_verweigert_noch
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment4.wFormat_vorher
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment4.wFormat_jetzt
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment4.w108_tip

/-
  CUTS (agent 02, second follow-up -- grounds and formats):
  1. PROVED here (pending green check: apparatus blocked, see
     REPORT-02.md): ground-drop (`istGrund`, `dropGrund`, `elabU05`)
     with identity, agreement (`dropGrund_id`, `elabU05_stimmt`, 104),
     refusal (`elabU05_verweigert_noch`) and a synthetic witness pair
     (`wGrund_vorher`, `wGrund_jetzt` reusing `wProtoProg`); format-drop
     (`istFormat`, `dropFormat`, `elabU06`) with the same package
     (`dropFormat_id`, `elabU06_stimmt`, `elabU06_verweigert_noch`,
     `wFormat_vorher`, `wFormat_jetzt`); and the 108 tip witness
     (`w108_tip`: the cumulative elaborator still yields `w108prog`).
     Every shape mirrors the green-reviewed `GvParserFragment3`
     protoT package.
  2. NOT proved: anything beyond the elaborator; no corpus unit flips
     on either case (measured: grundT-drop moves 11a/133/169/170/48
     deeper, formatT-drop moves 03/24; all stay refused for other
     missing forms); `SAnw`-internal positions; nested modules
     re-unwrap (as before).
-/

end Gabbro.Grammatik.GabbroV.GvParserFragment4
