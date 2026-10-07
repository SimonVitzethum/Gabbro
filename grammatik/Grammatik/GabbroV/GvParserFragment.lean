/-
  File:      Grammatik/GabbroV/GvParserFragment.lean
  Subject:   GabbroV bridge: measure and widen the elaborated fragment (agent 02).

  The bridge from GabbroV duties to premise (b) is closed only for the
  fragment the Lean parser elaborates (`elabU` accepts 2 of 146 corpus
  units). This module measures the first rejection per corpus file
  (`ErstAblehnung`, `erstAblehnung`) and widens the fragment by ONE
  elaboration case, with its correctness theorem and refusal theorems.
  It never edits `Parser/`; other agents' work arrives only by merge.
-/
import Grammatik.Parser.Uebersetze

namespace Gabbro.Grammatik.GabbroV.GvParserFragment

open Gabbro.Grammatik.Parser
open Gabbro.Grammatik.Parser.Uebersetze

/-- **First-rejection class of an elaboration outcome**: either the unit
    elaborates (`ok`) or it stops with the elaborator's message
    (`fehler`), which names the construct that stopped it. -/
inductive ErstAblehnung where
  | ok : ErstAblehnung
  | fehler : String → ErstAblehnung
  deriving DecidableEq, Repr

/-- **Classify an elaboration outcome by its first rejection.** Every
    premise (both arms) is used: the classifier is total. -/
def erstAblehnung : Except String UProg → ErstAblehnung
  | .ok _ => .ok
  | .error e => .fehler e

/-- **The classifier accepts the 104 elaboration.** -/
theorem erstAblehnung_104 : erstAblehnung (.ok uExp104) = .ok := rfl

/-- **Joint witness for `erstAblehnung_104`**: 104 elaborates and has
    two functions -- a non-degenerate fixture, not vacuity. -/
theorem erstAblehnung_104_zeuge :
    erstAblehnung (.ok uExp104) = .ok ∧ uExp104.fns.length = 2 :=
  ⟨rfl, rfl⟩

/-
  CUTS (agent 02 -- widen the elaborated fragment):
  1. PROVED here: the first-rejection classifier (`ErstAblehnung`,
     `erstAblehnung`, 104-acceptance, no axioms); the inert-item skip
     (`istStatik`, `istNeben`, `istInert`, `ohneInert`, `elabU02`) with
     correctness (`ohneInert_id`, `elabU02_stimmt`, 104-agreement) and
     refusal (`uRestFehler_kopf`, `kopf_gut`, `schritt`, `faellt`,
     `elabU_bei_RestFehler`, `elabU02_verweigert_noch` with a synthetic
     `use` witness); and the corpus witness pair for 108
     (`w108_vorher`, `w108_jetzt`: refused by `elabU`, elaborated by
     `elabU02`; `lowerAllg` also succeeds per probe #3).
  2. NOT proved: anything beyond the elaborator -- no duty, bridge,
     start-duty or TSO statement; no case for the other 24 off-fragment
     item kinds (each still refused; distribution measured in probe
     #2); no body-level widening (`if`/`let`/mid-`return` have no G
     form); nested modules re-unwrap once more under `elabU02` than
     under `elabU` (the refusal theorem reads the re-unwrapped list,
     so nothing is wrongly accepted; the inner-content case is
     unanalyzed).
  3. Elaboration lesson (for the next lane): write pasted surface
     literals in the tree's dotted style (`.tabelleT`, `.atom`, like
     `items104`); pasting `repr` output with fully-qualified
     constructors failed to parse here ("unexpected identifier;
     expected '}'" at the second struct field).
-/

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.erstAblehnung_104
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.erstAblehnung_104_zeuge

/-! ## Step 2: elaborate past `static` items -/

/-- **Is this a `static` item?** (`statikT`, `SItemTief`,
    `ElementTief.lean`): named storage with an initializer. The measured
    most common FIRST blocker (probe tally 2026-10-07: 22 of 157 corpus
    files stop at a `statikT` in `uRestFehler`, more than any other item
    kind). -/
def istStatik : SItemTief → Bool
  | .statikT .. => true
  | _ => false

/-- **Is this a `concurrent` item?** (`nebenT`, `SItemTief`,
    `ElementTief.lean`): thread-set names. The accepted `pre108`
    (`UebersetzeAllg2.lean`) strips them: they have no G form. -/
def istNeben : SItemTief → Bool
  | .nebenT .. => true
  | _ => false

/-- **Is this item inert for the elaborated fragment?** A `static`
    denotes storage the fragment cannot name; a `concurrent` item names
    thread sets the fragment cannot see. Neither contributes a table, a
    lock, a function or a root -- and a use of a dropped static fails
    loudly downstream ("Name unbekannt" at the body). -/
def istInert (it : SItemTief) : Bool :=
  istStatik it || istNeben it

/-- **Drop inert top-level items (`static`, `concurrent`).** Like the
    accepted `stripTopNeben` and the silent skip of non-literal
    `const`s (`uConsts`): what is dropped denotes nothing the fragment
    can name, so on the elaborated fragment the projection refuses
    nothing silently. -/
def ohneInert : List SItemTief → List SItemTief
  | [] => []
  | it :: rest =>
    if istInert it then ohneInert rest else it :: ohneInert rest

/-- **Elaborate like `elabU` after dropping inert items.** `uMembers`
    unwraps the single module layer exactly as `elabU` does. -/
def elabU02 (items : List SItemTief) : Except String UProg :=
  elabU (ohneInert (uMembers items))

/-- **Dropping changes nothing on inert-free lists.** Every premise is
    used: `h` gives both the head fact and the tail fact. -/
theorem ohneInert_id (l : List SItemTief)
    (h : ∀ it ∈ l, istInert it = false) :
    ohneInert l = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hhd : istInert hd = false :=
      h hd (List.mem_cons.mpr (Or.inl rfl))
    have htl : ∀ it ∈ tl, istInert it = false := fun it hm =>
      h it (List.mem_cons.mpr (Or.inr hm))
    simp [ohneInert, hhd, ih htl]

/-- **On units whose unwrapped items are inert-free the new elaborator
    IS the old one.** -/
theorem elabU02_stimmt (items : List SItemTief)
    (h : ohneInert (uMembers items) = uMembers items) :
    elabU02 items = elabU (uMembers items) := by
  show elabU (ohneInert (uMembers items)) = elabU (uMembers items)
  rw [h]

/-- **Joint witness for `elabU02_stimmt`**: 104's items are inert-free
    and both elaborators agree on them -- a non-degenerate two-function
    program, not vacuity. -/
theorem elabU02_stimmt_zeuge :
    ohneInert (uMembers items104) = uMembers items104 ∧
    elabU02 items104 = elabU items104 :=
  ⟨rfl, rfl⟩

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.ohneInert_id
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.elabU02_stimmt
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.elabU02_stimmt_zeuge

/-! ## Step 2 (refusal): what is still rejected -/

/-- **Is this item outside the elaborated fragment?** True for every
    `SItemTief` kind `uRestFehler` refuses (everything but `konstT`,
    `typT`, `tabelleT`, `sperreT`, `funktionT`, `eingangT`) except the
    inert kinds `elabU02` forgives (`static`, `concurrent`). -/
def istGegenstand : SItemTief → Bool
  | .konstT .. => false
  | .typT .. => false
  | .tabelleT .. => false
  | .sperreT .. => false
  | .funktionT .. => false
  | .eingangT .. => false
  | .statikT .. => false
  | .nebenT .. => false
  | _ => true

/-- **One off-fragment item fails the item check.** By cases over all
    33 surface-item kinds: the six accepted ones contradict the premise,
    the rest reduce to the refusal arm. -/
theorem uRestFehler_kopf (hd : SItemTief) (tl : List SItemTief)
    (he : istGegenstand hd = true) :
    uRestFehler (hd :: tl) = .error "Gegenstand ohne G-Form" := by
  cases hd with
  | konstT _ _ _ => simp [istGegenstand] at he
  | typT _ _ _ _ _ => simp [istGegenstand] at he
  | tabelleT _ _ _ _ _ _ => simp [istGegenstand] at he
  | sperreT _ _ _ _ _ _ => simp [istGegenstand] at he
  | funktionT _ _ => simp [istGegenstand] at he
  | eingangT _ => simp [istGegenstand] at he
  | modulT _ _ => rfl
  | useT _ => rfl
  | statikT _ _ _ _ _ _ => simp [istGegenstand] at he
  | protoT _ => rfl
  | specT _ _ => rfl
  | asmT _ _ => rfl
  | formatT _ _ _ _ => rfl
  | arenaT _ _ _ _ => rfl
  | grundT _ _ _ => rfl
  | zustandT _ _ => rfl
  | geraetT _ _ _ _ => rfl
  | annahmeT _ _ _ _ => rfl
  | axiomaT _ _ _ _ _ _ => rfl
  | pruefungT _ => rfl
  | atomarT _ _ _ _ _ => rfl
  | rcuT _ _ _ => rfl
  | gruppeT _ _ _ => rfl
  | nebenT _ => simp [istGegenstand] at he
  | akkumT _ _ _ _ => rfl
  | wegT _ => rfl
  | anvertrautT _ _ _ _ _ _ => rfl
  | startT _ _ _ _ => rfl
  | sysrufT _ => rfl
  | uebersetzerT _ _ _ => rfl
  | profilT _ _ => rfl
  | torT _ => rfl

/-- **Is this item accepted by the item check?** Exactly the six kinds
    `uRestFehler` recurses on (accepted heads step past; inert heads and
    off-fragment heads refuse at once). -/
def istAngenommen : SItemTief → Bool
  | .konstT .. => true
  | .typT .. => true
  | .tabelleT .. => true
  | .sperreT .. => true
  | .funktionT .. => true
  | .eingangT .. => true
  | _ => false

/-- **An accepted head steps past the item check.** The mirror of
    `uRestFehler_kopf`: the six accepted kinds recurse, everything else
    contradicts the premise. -/
theorem uRestFehler_kopf_gut (hd : SItemTief) (tl : List SItemTief)
    (he : istAngenommen hd = true) :
    uRestFehler (hd :: tl) = uRestFehler tl := by
  cases hd with
  | konstT _ _ _ => rfl
  | typT _ _ _ _ _ => rfl
  | tabelleT _ _ _ _ _ _ => rfl
  | sperreT _ _ _ _ _ _ => rfl
  | funktionT _ _ => rfl
  | eingangT _ => rfl
  | modulT _ _ => simp [istAngenommen] at he
  | useT _ => simp [istAngenommen] at he
  | statikT _ _ _ _ _ _ => simp [istAngenommen] at he
  | protoT _ => simp [istAngenommen] at he
  | specT _ _ => simp [istAngenommen] at he
  | asmT _ _ => simp [istAngenommen] at he
  | formatT _ _ _ _ => simp [istAngenommen] at he
  | arenaT _ _ _ _ => simp [istAngenommen] at he
  | grundT _ _ _ => simp [istAngenommen] at he
  | zustandT _ _ => simp [istAngenommen] at he
  | geraetT _ _ _ _ => simp [istAngenommen] at he
  | annahmeT _ _ _ _ => simp [istAngenommen] at he
  | axiomaT _ _ _ _ _ _ => simp [istAngenommen] at he
  | pruefungT _ => simp [istAngenommen] at he
  | atomarT _ _ _ _ _ => simp [istAngenommen] at he
  | rcuT _ _ _ => simp [istAngenommen] at he
  | gruppeT _ _ _ => simp [istAngenommen] at he
  | nebenT _ => simp [istAngenommen] at he
  | akkumT _ _ _ _ => simp [istAngenommen] at he
  | wegT _ => simp [istAngenommen] at he
  | anvertrautT _ _ _ _ _ _ => simp [istAngenommen] at he
  | startT _ _ _ _ => simp [istAngenommen] at he
  | sysrufT _ => simp [istAngenommen] at he
  | uebersetzerT _ _ _ => simp [istAngenommen] at he
  | profilT _ _ => simp [istAngenommen] at he
  | torT _ => simp [istAngenommen] at he

/-- **A head that is neither accepted nor excused fails at once.** With
    no fragment excuse (`istGegenstand` false) and no accepted shape
    (`istAngenommen` false) the head is inert (`static`, `concurrent`)
    or worse, and `uRestFehler` refuses it without looking at the tail. -/
theorem uRestFehler_schritt (hd : SItemTief) (tl : List SItemTief)
    (he : istGegenstand hd = false) (ha : istAngenommen hd = false) :
    uRestFehler (hd :: tl) = .error "Gegenstand ohne G-Form" := by
  cases hd with
  | konstT _ _ _ => simp [istAngenommen] at ha
  | typT _ _ _ _ _ => simp [istAngenommen] at ha
  | tabelleT _ _ _ _ _ _ => simp [istAngenommen] at ha
  | sperreT _ _ _ _ _ _ => simp [istAngenommen] at ha
  | funktionT _ _ => simp [istAngenommen] at ha
  | eingangT _ => simp [istAngenommen] at ha
  | modulT _ _ => simp [istGegenstand] at he
  | useT _ => simp [istGegenstand] at he
  | statikT _ _ _ _ _ _ => rfl
  | protoT _ => simp [istGegenstand] at he
  | specT _ _ => simp [istGegenstand] at he
  | asmT _ _ => simp [istGegenstand] at he
  | formatT _ _ _ _ => simp [istGegenstand] at he
  | arenaT _ _ _ _ => simp [istGegenstand] at he
  | grundT _ _ _ => simp [istGegenstand] at he
  | zustandT _ _ => simp [istGegenstand] at he
  | geraetT _ _ _ _ => simp [istGegenstand] at he
  | annahmeT _ _ _ _ => simp [istGegenstand] at he
  | axiomaT _ _ _ _ _ _ => simp [istGegenstand] at he
  | pruefungT _ => simp [istGegenstand] at he
  | atomarT _ _ _ _ _ => simp [istGegenstand] at he
  | rcuT _ _ _ => simp [istGegenstand] at he
  | gruppeT _ _ _ => simp [istGegenstand] at he
  | nebenT _ => rfl
  | akkumT _ _ _ _ => simp [istGegenstand] at he
  | wegT _ => simp [istGegenstand] at he
  | anvertrautT _ _ _ _ _ _ => simp [istGegenstand] at he
  | startT _ _ _ _ => simp [istGegenstand] at he
  | sysrufT _ => simp [istGegenstand] at he
  | uebersetzerT _ _ _ => simp [istGegenstand] at he
  | profilT _ _ => simp [istGegenstand] at he
  | torT _ => simp [istGegenstand] at he

/-- **An off-fragment item anywhere fails the item check.** Induction:
    empty lists hold no witness; a bad head fails at once, otherwise the
    witness sits in the tail. -/
theorem uRestFehler_faellt (l : List SItemTief)
    (h : ∃ it ∈ l, istGegenstand it = true) :
    uRestFehler l = .error "Gegenstand ohne G-Form" := by
  induction l with
  | nil =>
    cases h with
    | intro w hw =>
      cases hw with
      | intro hmem hbad => simp at hmem
  | cons hd tl ih =>
    cases h with
    | intro w hw =>
      cases hw with
      | intro hmem hbad =>
        cases he : istGegenstand hd with
        | true => exact uRestFehler_kopf hd tl he
        | false =>
          cases ha : istAngenommen hd with
          | true =>
            have hmem' : w ∈ tl := by
              simp only [List.mem_cons] at hmem
              cases hmem with
              | inl heq =>
                cases heq
                rw [he] at hbad
                simp at hbad
              | inr hm => exact hm
            rw [uRestFehler_kopf_gut hd tl ha]
            exact ih ⟨w, hmem', hbad⟩
          | false => exact uRestFehler_schritt hd tl he ha

/-- **A failing item check fails the elaboration.** `elabU` runs
    `uRestFehler` first; a refused item list refuses the unit. -/
theorem elabU_bei_RestFehler (ms : List SItemTief) (e : String)
    (hR : uRestFehler (uMembers ms) = .error e) :
    elabU ms = .error e := by
  simp [elabU, hR]

/-- **Units that still carry an off-fragment item are still refused.**
    The refusal half of the widening: only inert items (`static`,
    `concurrent`) are forgiven. The premise is read after stripping and
    re-unwrapping, exactly where `elabU` checks (nested modules
    re-unwrap; see CUTS). -/
theorem elabU02_verweigert_noch (items : List SItemTief)
    (h : ∃ it ∈ uMembers (ohneInert (uMembers items)),
      istGegenstand it = true) :
    ∃ e, elabU02 items = .error e := by
  have hR := uRestFehler_faellt _ h
  exact ⟨_, elabU_bei_RestFehler _ _ hR⟩

/-- **Witness for `elabU02_verweigert_noch`**: a lone `use` item is
    still refused -- minimal synthetic fixture; corpus-scale refusal is
    measured by probe #2 (81 `Gegenstand` files). -/
theorem elabU02_verweigert_noch_zeuge :
    ∃ e, elabU02 [.useT ["x"]] = .error e :=
  ⟨_, rfl⟩

/-! ## Step 2 (witness): 108 elaborates now -/

/-- **108's parsed items** (`beispiele/108-disjoint-start-locks.gab`,
    printed by `.tmp/probe_repr108.lean`, pasted in the tree's dotted
    style like `items104`): one table, two readers, and the single
    blocking `concurrent` item. -/
def w108items : List SItemTief :=
  [.modulT "beispiel::disjoint_start_locks"
    [.tabelleT "T" (.some (.lit 4)) .none .none false
      [.tPlatz [{ fname := "v", ftyp := .atom "u32",
                  pos := .none, bezug := .none, wo := .none,
                  reserviert := false, byOps := false }]],
    .funktionT
      { art := "impl", name := "read_a", params := [],
        ergebnis := .some (.atom "u32"), fehler := .none,
        klauseln := [.wirkung [.liest (.feld (.variable "T") "slots")],
                     .kosten (.lit 4)] }
      (.block []
        (.some (.ret (.some (.feld
          (.index (.feld (.variable "T") "slots") (.lit 0)) "v"))))),
    .funktionT
      { art := "impl", name := "read_c", params := [],
        ergebnis := .some (.atom "u32"), fehler := .none,
        klauseln := [.wirkung [.liest (.feld (.variable "T") "slots")],
                     .kosten (.lit 4)] }
      (.block []
        (.some (.ret (.some (.feld
          (.index (.feld (.variable "T") "slots") (.lit 1)) "v"))))),
    .nebenT [["read_a"], ["read_c"]]]]

/-- **108's elaborated program** under `elabU02` (same probe, pasted):
    the table and both readers, the `concurrent` names gone. -/
def w108prog : UProg :=
  { tabellen := [{ name := "T", count := 4, felder := [("v", 0, 4294967295)], bools := [] }],
    sperren := [],
    fns := [{ name := "read_a", params := [], parten := [],
              ergebnis := .some (0, 4294967295), ergBool := false,
              held := [], schreibt := [], sichert := [], saetze := [],
              rueck := .wert (.tab "T" "v" (.lit 0)) },
            { name := "read_c", params := [], parten := [],
              ergebnis := .some (0, 4294967295), ergBool := false,
              held := [], schreibt := [], sichert := [], saetze := [],
              rueck := .wert (.tab "T" "v" (.lit 1)) }],
    wurzeln := [] }

/-- **108 was refused before**: `elabU` stops at the `concurrent`
    item with "Gegenstand ohne G-Form" (probe #1, measured). Stated with
    `beqElabU` like `u104elab` (`UProg` has no `DecidableEq` instance). -/
theorem w108_vorher :
    beqElabU (elabU w108items) (.error "Gegenstand ohne G-Form") = true := by
  decide

/-- **108 elaborates now**: `elabU02` yields exactly the pasted program
    (probe #3: elab *and* `lowerAllg` succeed on 108). -/
theorem w108_jetzt : beqElabU (elabU02 w108items) (.ok w108prog) = true := by
  decide

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.w108_vorher
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.w108_jetzt

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.uRestFehler_kopf
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.uRestFehler_kopf_gut
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.uRestFehler_schritt
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.uRestFehler_faellt
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.elabU_bei_RestFehler
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.elabU02_verweigert_noch
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.elabU02_verweigert_noch_zeuge

end Gabbro.Grammatik.GabbroV.GvParserFragment
