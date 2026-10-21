/-
  File:      Grammatik/GabbroV/GvParserFragment.lean
  Subject:   GabbroV bridge: measure and widen the elaborated fragment (agent 02).

  The bridge from GabbroV duties to premise (b) is closed only for the
  fragment the Lean parser elaborates. This module classifies the first
  rejection of an elaboration (`ErstAblehnung`, `erstAblehnung`) and proves
  what the item check refuses (`uRestFehler_faellt`): an item of a kind the
  elaborator has no G form for refuses the whole unit.
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
  CUTS: PROVED here: the first-rejection classifier (`ErstAblehnung`, `erstAblehnung`, 104-acceptance, no
  axioms); the refusal of off-fragment items (`uRestFehler_kopf`, `kopf_gut`, `schritt`, `faellt`,
  `elabU_bei_RestFehler`, `elabU_verweigert_noch` with a synthetic `use` witness); the corpus witness 108
  (`w108_elab`). NOT proved: anything beyond the elaborator -- no duty, bridge, start-duty or TSO statement.
  The wrapper elaborators that dropped statics, prototypes, `format`/reason items or normalised bounds
  (`elabU02`..`elabU05`) are gone: the elaborator reads statics and concurrent items itself, and what it
  does not read it refuses.
-/

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.erstAblehnung_104
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.erstAblehnung_104_zeuge

/-! ## What is still refused -/

/-- **Is this item outside the elaborated fragment?** True for every
    `SItemTief` kind `uRestFehler` refuses (everything but `constT`,
    `typeT`, `tableT`, `lockT`, `fnT`, `entryT`, `concT`) except the
    kinds the unit may carry (`concurrent`, `static`, `atomic`, `arena`, `extern fn`, `assume`, `reason`, `syscall` gates and their bindings, `device`). -/
def istGegenstand : SItemTief → Bool
  | .constT .. => false
  | .typeT .. => false
  | .tableT .. => false
  | .lockT .. => false
  | .fnT .. => false
  | .entryT .. => false
  | .globT .. => false
  | .atomT .. => false
  | .arenaT .. => false
  | .protoT .. => false
  | .assumT .. => false
  | .whyT .. => false
  | .callT .. => false
  | .varT .. => false
  | .goalT .. => false
  | .concT .. => false
  | .devT .. => false
  | .groupT .. => false
  | .stateT .. => false
  | _ => true

/-- **One off-fragment item fails the item check.** By cases over all
    33 surface-item kinds: the accepted ones contradict the premise,
    the rest reduce to the refusal arm. -/
theorem uRestFehler_kopf (hd : SItemTief) (tl : List SItemTief)
    (he : istGegenstand hd = true) :
    uRestFehler (hd :: tl) = .error "item without G form" := by
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
  | protoT _ => simp [istGegenstand] at he
  | specT _ _ => rfl
  | asmT _ _ => rfl
  | formatT _ _ _ _ => rfl
  | arenaT _ _ _ _ _ _ => simp [istGegenstand] at he
  | whyT _ _ _ => simp [istGegenstand] at he
  | stateT _ _ => simp [istGegenstand] at he
  | devT _ _ _ _ => simp [istGegenstand] at he
  | assumT _ _ _ _ => simp [istGegenstand] at he
  | axiomT _ _ _ _ _ _ => rfl
  | checkT _ => rfl
  | atomT _ _ _ _ _ => simp [istGegenstand] at he
  | rcuT _ _ _ => rfl
  | groupT _ _ _ => simp [istGegenstand] at he
  | concT _ => simp [istGegenstand] at he
  | accT _ _ _ _ => rfl
  | walkT _ => rfl
  | trustT _ _ _ _ _ _ => rfl
  | bootT _ _ _ _ => rfl
  | callT _ => simp [istGegenstand] at he
  | varT _ => simp [istGegenstand] at he
  | goalT _ _ => simp [istGegenstand] at he
  | transT _ _ _ => rfl
  | profT _ _ => rfl
  | gateT _ => rfl

/-- **Is this item accepted by the item check?** Exactly the kinds `uRestFehler` recurses on (accepted
    heads step past; off-fragment heads refuse at once). -/
def istAngenommen : SItemTief → Bool
  | .constT .. => true
  | .typeT .. => true
  | .tableT .. => true
  | .lockT .. => true
  | .fnT .. => true
  | .entryT .. => true
  | .globT .. => true
  | .atomT .. => true
  | .arenaT .. => true
  | .protoT .. => true
  | .assumT .. => true
  | .whyT .. => true
  | .callT .. => true
  | .varT .. => true
  | .goalT .. => true
  | .concT .. => true
  | .devT .. => true
  | .groupT .. => true
  | .stateT .. => true
  | _ => false

/-- **An accepted head steps past the item check.** The mirror of
    `uRestFehler_kopf`: the accepted kinds recurse, everything else
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
  | globT _ _ _ _ _ _ _ => rfl
  | protoT _ => rfl
  | specT _ _ => simp [istAngenommen] at he
  | asmT _ _ => simp [istAngenommen] at he
  | formatT _ _ _ _ => simp [istAngenommen] at he
  | arenaT _ _ _ _ _ _ => rfl
  | whyT _ _ _ => rfl
  | stateT _ _ => rfl
  | devT _ _ _ _ => rfl
  | assumT _ _ _ _ => rfl
  | axiomT _ _ _ _ _ _ => simp [istAngenommen] at he
  | checkT _ => simp [istAngenommen] at he
  | atomT _ _ _ _ _ => rfl
  | rcuT _ _ _ => simp [istAngenommen] at he
  | groupT _ _ _ => rfl
  | concT _ => rfl
  | accT _ _ _ _ => simp [istAngenommen] at he
  | walkT _ => simp [istAngenommen] at he
  | trustT _ _ _ _ _ _ => simp [istAngenommen] at he
  | bootT _ _ _ _ => simp [istAngenommen] at he
  | callT _ => rfl
  | varT _ => rfl
  | goalT _ _ => rfl
  | transT _ _ _ => simp [istAngenommen] at he
  | profT _ _ => simp [istAngenommen] at he
  | gateT _ => simp [istAngenommen] at he

/-- **A head that is neither accepted nor excused fails at once.** With
    no fragment excuse (`istGegenstand` false) and no accepted shape
    (`istAngenommen` false) the head is off the fragment
    (a `use`, a `format`, ...), and `uRestFehler` refuses it without looking at the tail. -/
theorem uRestFehler_schritt (hd : SItemTief) (tl : List SItemTief)
    (he : istGegenstand hd = false) (ha : istAngenommen hd = false) :
    uRestFehler (hd :: tl) = .error "item without G form" := by
  cases hd with
  | constT _ _ _ => simp [istAngenommen] at ha
  | typeT _ _ _ _ _ => simp [istAngenommen] at ha
  | tableT _ _ _ _ _ _ => simp [istAngenommen] at ha
  | lockT _ _ _ _ _ _ _ => simp [istAngenommen] at ha
  | fnT _ _ => simp [istAngenommen] at ha
  | entryT _ => simp [istAngenommen] at ha
  | modT _ _ => simp [istGegenstand] at he
  | useT _ => simp [istGegenstand] at he
  | globT _ _ _ _ _ _ _ => simp [istAngenommen] at ha
  | protoT _ => simp [istAngenommen] at ha
  | specT _ _ => simp [istGegenstand] at he
  | asmT _ _ => simp [istGegenstand] at he
  | formatT _ _ _ _ => simp [istGegenstand] at he
  | arenaT _ _ _ _ _ _ => simp [istAngenommen] at ha
  | whyT _ _ _ => simp [istAngenommen] at ha
  | stateT _ _ => simp [istAngenommen] at ha
  | devT _ _ _ _ => simp [istAngenommen] at ha
  | assumT _ _ _ _ => simp [istAngenommen] at ha
  | axiomT _ _ _ _ _ _ => simp [istGegenstand] at he
  | checkT _ => simp [istGegenstand] at he
  | atomT _ _ _ _ _ => simp [istAngenommen] at ha
  | rcuT _ _ _ => simp [istGegenstand] at he
  | groupT _ _ _ => simp [istAngenommen] at ha
  | concT _ => simp [istAngenommen] at ha
  | accT _ _ _ _ => simp [istGegenstand] at he
  | walkT _ => simp [istGegenstand] at he
  | trustT _ _ _ _ _ _ => simp [istGegenstand] at he
  | bootT _ _ _ _ => simp [istGegenstand] at he
  | callT _ => simp [istAngenommen] at ha
  | varT _ => simp [istAngenommen] at ha
  | goalT _ _ => simp [istAngenommen] at ha
  | transT _ _ _ => simp [istGegenstand] at he
  | profT _ _ => simp [istGegenstand] at he
  | gateT _ => simp [istGegenstand] at he

/-- **An off-fragment item anywhere fails the item check.** Induction:
    empty lists hold no witness; a bad head fails at once, otherwise the
    witness sits in the tail. -/
theorem uRestFehler_faellt (l : List SItemTief)
    (h : ∃ it ∈ l, istGegenstand it = true) :
    uRestFehler l = .error "item without G form" := by
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

/-- **Units that carry an off-fragment item are refused.** The premise is read where `elabU` checks. -/
theorem elabU_verweigert_noch (items : List SItemTief)
    (h : ∃ it ∈ uMembers items, istGegenstand it = true) :
    ∃ e, elabU items = .error e := by
  have hR := uRestFehler_faellt _ h
  exact ⟨_, elabU_bei_RestFehler _ _ hR⟩

/-- **Witness for `elabU_verweigert_noch`**: a lone `use` item is
    still refused -- minimal synthetic fixture; corpus-scale refusal is
    measured by probe #2 (81 `Gegenstand` files). -/
theorem elabU_verweigert_noch_zeuge :
    ∃ e, elabU [.useT ["x"]] = .error e :=
  ⟨_, rfl⟩

/-! ## 108 elaborates -/

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

/-- **108's elaborated program** (same probe, pasted):
    the table and both readers, the `concurrent` members as thread roots. -/
def w108prog : UProg :=
  { tabs := [{ name := "T", count := 4, cols := [("v", 0, 4294967295)], bools := [] }],
    locks := [],
    fns := [{ name := "read_a", params := [], kinds := [],
              res := .some (0, 4294967295), resBool := false,
              held := [], puts := [], gives := [], body := [],
              ret := .val (.tab "T" "v" (.lit 0)) },
            { name := "read_c", params := [], kinds := [],
              res := .some (0, 4294967295), resBool := false,
              held := [], puts := [], gives := [], body := [],
              ret := .val (.tab "T" "v" (.lit 1)) }],
    roots := ["read_a", "read_c"] }

/-- **108 elaborates**: `elabU` yields exactly the pasted program, the `concurrent` members as its thread
    roots (and `lowerAllg` succeeds on it). -/
theorem w108_elab : beqElabU (elabU w108items) (.ok w108prog) = true := by
  decide

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.w108_elab

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.uRestFehler_kopf
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.uRestFehler_kopf_gut
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.uRestFehler_schritt
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.uRestFehler_faellt
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.elabU_bei_RestFehler
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.elabU_verweigert_noch
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.elabU_verweigert_noch_zeuge

end Gabbro.Grammatik.GabbroV.GvParserFragment
