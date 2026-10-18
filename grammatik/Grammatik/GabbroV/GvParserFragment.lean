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
import Grammatik.Parser.Elab.Uebersetze

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
     (`istStatik`, `istInert`, `ohneInert`, `elabU02`) with
     correctness (`ohneInert_id`, `elabU02_stimmt`, 104-agreement) and
     refusal (`uRestFehler_kopf`, `kopf_gut`, `schritt`, `faellt`,
     `elabU_bei_RestFehler`, `elabU02_verweigert_noch` with a synthetic
     `use` witness); and the corpus witness pair for 108
     (`w108_jetzt`: elaborated by `elabU` itself since the `concurrent` roots
     are read; `lowerAllg` also succeeds per probe #3).
  2. NOT proved: anything beyond the elaborator -- no duty, bridge,
     start-duty or TSO statement; no case for the other 24 off-fragment
     item kinds (each still refused; distribution measured in probe
     #2); no body-level widening (`if`/`let`/mid-`return` have no G
     form); nested modules re-unwrap once more under `elabU02` than
     under `elabU` (the refusal theorem reads the re-unwrapped list,
     so nothing is wrongly accepted; the inner-content case is
     unanalyzed).
  3. Elaboration lesson (for the next lane): write pasted surface
     literals in the tree's dotted style (`.tableT`, `.atom`, like
     `items104`); pasting `repr` output with fully-qualified
     constructors failed to parse here ("unexpected identifier;
     expected '}'" at the second struct field).
-/

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.erstAblehnung_104
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.erstAblehnung_104_zeuge

/-! ## Step 2: elaborate past `static` items -/

/-- **Is this a `static` item?** (`globT`, `SItemTief`,
    `ElementTief.lean`): named storage with an initializer. The measured
    most common FIRST blocker (probe tally 2026-10-07: 22 of 157 corpus
    files stop at a `globT` in `uRestFehler`, more than any other item
    kind). -/
def istStatik : SItemTief → Bool
  | .globT .. => true
  | _ => false

/-- **Is this item inert for the elaborated fragment?** A `static` denotes storage the fragment cannot
    name: it contributes no table, lock, function or root, and a use of a dropped static fails loudly
    downstream ("Name unbekannt" at the body). (`concurrent` items were inert here until 2026-10-18; the
    elaborator reads them into the thread roots now.) -/
def istInert (it : SItemTief) : Bool :=
  istStatik it

/-- **Drop inert top-level items (`static`).** Like the silent skip of non-literal
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
    `SItemTief` kind `uRestFehler` refuses (everything but `constT`,
    `typeT`, `tableT`, `lockT`, `fnT`, `entryT`, `concT`) except the
    inert kind `elabU02` forgives (`static`). -/
def istGegenstand : SItemTief → Bool
  | .constT .. => false
  | .typeT .. => false
  | .tableT .. => false
  | .lockT .. => false
  | .fnT .. => false
  | .entryT .. => false
  | .globT .. => false
  | .concT .. => false
  | _ => true

/-- **One off-fragment item fails the item check.** By cases over all
    33 surface-item kinds: the six accepted ones contradict the premise,
    the rest reduce to the refusal arm. -/
theorem uRestFehler_kopf (hd : SItemTief) (tl : List SItemTief)
    (he : istGegenstand hd = true) :
    uRestFehler (hd :: tl) = .error "Gegenstand ohne G-Form" := by
  cases hd with
  | constT _ _ _ => simp [istGegenstand] at he
  | typeT _ _ _ _ _ => simp [istGegenstand] at he
  | tableT _ _ _ _ _ _ => simp [istGegenstand] at he
  | lockT _ _ _ _ _ _ _ => simp [istGegenstand] at he
  | fnT _ _ => simp [istGegenstand] at he
  | entryT _ => simp [istGegenstand] at he
  | modT _ _ => rfl
  | useT _ => rfl
  | globT _ _ _ _ _ _ _ => simp [istGegenstand] at he
  | protoT _ => rfl
  | specT _ _ => rfl
  | asmT _ _ => rfl
  | formatT _ _ _ _ => rfl
  | arenaT _ _ _ _ _ _ => rfl
  | whyT _ _ _ => rfl
  | stateT _ _ => rfl
  | devT _ _ _ _ => rfl
  | assumT _ _ _ _ => rfl
  | axiomT _ _ _ _ _ _ => rfl
  | checkT _ => rfl
  | atomT _ _ _ _ _ => rfl
  | rcuT _ _ _ => rfl
  | groupT _ _ _ => rfl
  | concT _ => simp [istGegenstand] at he
  | accT _ _ _ _ => rfl
  | walkT _ => rfl
  | trustT _ _ _ _ _ _ => rfl
  | bootT _ _ _ _ => rfl
  | callT _ => rfl
  | varT _ => rfl
  | goalT _ _ => rfl
  | transT _ _ _ => rfl
  | profT _ _ => rfl
  | gateT _ => rfl

/-- **Is this item accepted by the item check?** Exactly the six kinds
    `uRestFehler` recurses on (accepted heads step past; inert heads and
    off-fragment heads refuse at once). -/
def istAngenommen : SItemTief → Bool
  | .constT .. => true
  | .typeT .. => true
  | .tableT .. => true
  | .lockT .. => true
  | .fnT .. => true
  | .entryT .. => true
  | .concT .. => true
  | _ => false

/-- **An accepted head steps past the item check.** The mirror of
    `uRestFehler_kopf`: the six accepted kinds recurse, everything else
    contradicts the premise. -/
theorem uRestFehler_kopf_gut (hd : SItemTief) (tl : List SItemTief)
    (he : istAngenommen hd = true) :
    uRestFehler (hd :: tl) = uRestFehler tl := by
  cases hd with
  | constT _ _ _ => rfl
  | typeT _ _ _ _ _ => rfl
  | tableT _ _ _ _ _ _ => rfl
  | lockT _ _ _ _ _ _ _ => rfl
  | fnT _ _ => rfl
  | entryT _ => rfl
  | modT _ _ => simp [istAngenommen] at he
  | useT _ => simp [istAngenommen] at he
  | globT _ _ _ _ _ _ _ => simp [istAngenommen] at he
  | protoT _ => simp [istAngenommen] at he
  | specT _ _ => simp [istAngenommen] at he
  | asmT _ _ => simp [istAngenommen] at he
  | formatT _ _ _ _ => simp [istAngenommen] at he
  | arenaT _ _ _ _ _ _ => simp [istAngenommen] at he
  | whyT _ _ _ => simp [istAngenommen] at he
  | stateT _ _ => simp [istAngenommen] at he
  | devT _ _ _ _ => simp [istAngenommen] at he
  | assumT _ _ _ _ => simp [istAngenommen] at he
  | axiomT _ _ _ _ _ _ => simp [istAngenommen] at he
  | checkT _ => simp [istAngenommen] at he
  | atomT _ _ _ _ _ => simp [istAngenommen] at he
  | rcuT _ _ _ => simp [istAngenommen] at he
  | groupT _ _ _ => simp [istAngenommen] at he
  | concT _ => rfl
  | accT _ _ _ _ => simp [istAngenommen] at he
  | walkT _ => simp [istAngenommen] at he
  | trustT _ _ _ _ _ _ => simp [istAngenommen] at he
  | bootT _ _ _ _ => simp [istAngenommen] at he
  | callT _ => simp [istAngenommen] at he
  | varT _ => simp [istAngenommen] at he
  | goalT _ _ => simp [istAngenommen] at he
  | transT _ _ _ => simp [istAngenommen] at he
  | profT _ _ => simp [istAngenommen] at he
  | gateT _ => simp [istAngenommen] at he

/-- **A head that is neither accepted nor excused fails at once.** With
    no fragment excuse (`istGegenstand` false) and no accepted shape
    (`istAngenommen` false) the head is inert (`static`)
    or worse, and `uRestFehler` refuses it without looking at the tail. -/
theorem uRestFehler_schritt (hd : SItemTief) (tl : List SItemTief)
    (he : istGegenstand hd = false) (ha : istAngenommen hd = false) :
    uRestFehler (hd :: tl) = .error "Gegenstand ohne G-Form" := by
  cases hd with
  | constT _ _ _ => simp [istAngenommen] at ha
  | typeT _ _ _ _ _ => simp [istAngenommen] at ha
  | tableT _ _ _ _ _ _ => simp [istAngenommen] at ha
  | lockT _ _ _ _ _ _ _ => simp [istAngenommen] at ha
  | fnT _ _ => simp [istAngenommen] at ha
  | entryT _ => simp [istAngenommen] at ha
  | modT _ _ => simp [istGegenstand] at he
  | useT _ => simp [istGegenstand] at he
  | globT _ _ _ _ _ _ _ => rfl
  | protoT _ => simp [istGegenstand] at he
  | specT _ _ => simp [istGegenstand] at he
  | asmT _ _ => simp [istGegenstand] at he
  | formatT _ _ _ _ => simp [istGegenstand] at he
  | arenaT _ _ _ _ _ _ => simp [istGegenstand] at he
  | whyT _ _ _ => simp [istGegenstand] at he
  | stateT _ _ => simp [istGegenstand] at he
  | devT _ _ _ _ => simp [istGegenstand] at he
  | assumT _ _ _ _ => simp [istGegenstand] at he
  | axiomT _ _ _ _ _ _ => simp [istGegenstand] at he
  | checkT _ => simp [istGegenstand] at he
  | atomT _ _ _ _ _ => simp [istGegenstand] at he
  | rcuT _ _ _ => simp [istGegenstand] at he
  | groupT _ _ _ => simp [istGegenstand] at he
  | concT _ => simp [istAngenommen] at ha
  | accT _ _ _ _ => simp [istGegenstand] at he
  | walkT _ => simp [istGegenstand] at he
  | trustT _ _ _ _ _ _ => simp [istGegenstand] at he
  | bootT _ _ _ _ => simp [istGegenstand] at he
  | callT _ => simp [istGegenstand] at he
  | varT _ => simp [istGegenstand] at he
  | goalT _ _ => simp [istGegenstand] at he
  | transT _ _ _ => simp [istGegenstand] at he
  | profT _ _ => simp [istGegenstand] at he
  | gateT _ => simp [istGegenstand] at he

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
    The refusal half of the widening: only inert items (`static`)
    are forgiven. The premise is read after stripping and
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
    `concurrent` item (the thread roots). -/
def w108items : List SItemTief :=
  [.modT "beispiel::disjoint_start_locks"
    [.tableT "T" (.some (.lit 4)) .none .none false
      [.tSlot [{ fname := "v", ftyp := .atom "u32",
                  pos := .none, bezug := .none, wo := .none,
                  reserviert := false, byOps := false }]],
    .fnT
      { art := "impl", name := "read_a", params := [],
        res := .some (.atom "u32"), fehler := .none,
        klauseln := [.effs [.reads (.field (.variable "T") "slots")],
                     .cost (.lit 4)] }
      (.block []
        (.some (.ret (.some (.field
          (.index (.field (.variable "T") "slots") (.lit 0)) "v"))))),
    .fnT
      { art := "impl", name := "read_c", params := [],
        res := .some (.atom "u32"), fehler := .none,
        klauseln := [.effs [.reads (.field (.variable "T") "slots")],
                     .cost (.lit 4)] }
      (.block []
        (.some (.ret (.some (.field
          (.index (.field (.variable "T") "slots") (.lit 1)) "v"))))),
    .concT [["read_a"], ["read_c"]]]]

/-- **108's elaborated program** under `elabU02` (same probe, pasted):
    the table and both readers, the `concurrent` members as thread roots. -/
def w108prog : UProg :=
  { tabellen := [{ name := "T", count := 4, felder := [("v", 0, 4294967295)], bools := [] }],
    sperren := [],
    fns := [{ name := "read_a", params := [], parten := [],
              res := .some (0, 4294967295), ergBool := false,
              held := [], schreibt := [], gives := [], saetze := [],
              rueck := .val (.tab "T" "v" (.lit 0)) },
            { name := "read_c", params := [], parten := [],
              res := .some (0, 4294967295), ergBool := false,
              held := [], schreibt := [], gives := [], saetze := [],
              rueck := .val (.tab "T" "v" (.lit 1)) }],
    wurzeln := ["read_a", "read_c"] }

/-- **108 elaborates**: `elabU` (and so `elabU02`) yields exactly the pasted program, the `concurrent`
    members as its thread roots (probe #3: elab *and* `lowerAllg` succeed on 108). -/
theorem w108_jetzt : beqElabU (elabU02 w108items) (.ok w108prog) = true := by
  decide

/-- The `concurrent` roots are not dropped: plain `elabU` agrees. -/
theorem w108_ohne_umweg : beqElabU (elabU w108items) (.ok w108prog) = true := by
  decide

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.w108_jetzt
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.w108_ohne_umweg

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.uRestFehler_kopf
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.uRestFehler_kopf_gut
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.uRestFehler_schritt
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.uRestFehler_faellt
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.elabU_bei_RestFehler
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.elabU02_verweigert_noch
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.elabU02_verweigert_noch_zeuge

end Gabbro.Grammatik.GabbroV.GvParserFragment
