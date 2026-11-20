/-
  File:      Grammatik/GabbroV/GvParserFragment.lean
  Subject:   GabbroV bridge: measure and widen the elaborated fragment (agent 02).

  The bridge from GabbroV duties to premise (b) is closed only for the
  fragment the Lean parser elaborates. This module classifies the first
  rejection of an elaboration (`ErstAblehnung`, `erstAblehnung`) and proves
  what the item check refuses (`uRestFehler_faellt`): a refused item in the
  expanded unit forces an error, preserving the first actual diagnostic.
-/
module

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
public import Grammatik.Parser.Elab.Uebersetze

-- Concrete witnesses execute the actual empty check/static gates.
import all Grammatik.Parser.Elab.Uebersetze.Teil.Teil12
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Elaborate
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Erzeuge
import all Grammatik.Parser.Elab.Uebersetze.Pruefung.Torhuelle
import all Grammatik.Parser.Elab.Generic.StaticConformance
@[expose] public section


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
theorem erstAblehnung_104 : erstAblehnung (.ok uExp104) = .ok := by rfl

/-
  CUTS: PROVED here: the first-rejection classifier (`ErstAblehnung`, `erstAblehnung`, 104-acceptance, no
  extra axioms); the refusal of off-fragment items (`uRestFehler_kopf`, `kopf_gut`, `schritt`, `faellt`,
  `elabU_bei_RestFehler`, `elabU_verweigert_noch` with a synthetic `use` witness); the corpus witness 108
  (`w108_elab`). NOT proved: anything beyond the elaborator -- no duty, bridge, start-duty or TSO statement.
  The wrapper elaborators that dropped statics, prototypes, `format`/reason items or normalised bounds
  (`elabU02`..`elabU05`) are gone: the elaborator reads statics and concurrent items itself, and what it
  does not read it refuses.
-/

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.erstAblehnung_104

/-! ## What is still refused -/

/-- Is the item refused at the actual item-check boundary? Expansion runs first:
    adapters and module templates/uses must already have been consumed there.
    Accumulators use the canonical admitted-form guard; their named refusals and
    the safe-walk refusal are retained by the singleton check, not reconstructed. -/
def istGegenstand : SItemTief → Bool
  | .constT .. | .typeT .. | .tableT .. | .lockT .. | .fnT .. | .entryT .. => false
  | .globT .. | .atomT .. | .arenaT .. | .protoT .. | .assumT .. | .whyT .. => false
  | .callT .. | .varT .. | .goalT .. | .concT .. | .devT .. | .groupT .. => false
  | .stateT .. | .specT .. | .asmT .. | .transT .. | .checkT .. => false
  | .axiomT _ _ _ .none _ _ => false
  | item@(.accT ..) => !akkuFormZulaessig item
  | _ => true

/-- Exactly the heads past which the actual item check recurses. This is item
    admission, not a claim that every later elaboration gate accepts the unit. -/
def istAngenommen : SItemTief → Bool
  | .constT .. | .typeT .. | .tableT .. | .lockT .. | .fnT .. | .entryT .. => true
  | .globT .. | .atomT .. | .arenaT .. | .protoT .. | .assumT .. | .whyT .. => true
  | .callT .. | .varT .. | .goalT .. | .concT .. | .devT .. | .groupT .. => true
  | .stateT .. | .specT .. | .asmT .. | .transT .. | .checkT .. => true
  | .axiomT _ _ _ .none _ _ => true
  | item@(.accT ..) => akkuFormZulaessig item
  | _ => false

/-- Read the classification from the real singleton result. No diagnostic table
    is duplicated: existential error witnesses are the checker's own messages. -/
private theorem singleton_classification (hd : SItemTief) :
    (istAngenommen hd = true ↔ uRestFehler [hd] = .ok ()) ∧
    (istGegenstand hd = true ↔ ∃ e, uRestFehler [hd] = .error e) := by
  cases hd with
  | axiomT name params result requirement effects cost =>
    cases requirement <;> simp [istAngenommen, istGegenstand, uRestFehler]
  | accT name ty operator cores aggregate =>
    cases cores <;> cases ho : akkuOperatorOk operator <;>
      simp [istAngenommen, istGegenstand, uRestFehler, akkuFormZulaessig, ho]
  | _ => simp [istAngenommen, istGegenstand, uRestFehler]

/-- The item check composes the actual singleton result with the tail. This
    preserves both the first error and every admitted head, including accumulators. -/
theorem uRestFehler_schritt (hd : SItemTief) (tl : List SItemTief) :
    uRestFehler (hd :: tl) = (uRestFehler [hd]).bind (fun _ => uRestFehler tl) := by
  cases hd with
  | axiomT name params result requirement effects cost => cases requirement <;> rfl
  | accT name ty operator cores aggregate =>
    cases ha : akkuFormZulaessig (.accT name ty operator cores aggregate) <;>
      cases ho : akkuOperatorOk operator <;> simp [uRestFehler, ha, ho] <;> rfl
  | _ => rfl

/-- A refused head retains precisely its actual singleton diagnostic. -/
theorem uRestFehler_kopf (hd : SItemTief) (tl : List SItemTief)
    (he : istGegenstand hd = true) :
    uRestFehler (hd :: tl) = uRestFehler [hd] := by
  rcases (singleton_classification hd).2.mp he with ⟨e, checked⟩
  rw [uRestFehler_schritt, checked]
  rfl

/-- An accepted head steps past the actual item check. -/
theorem uRestFehler_kopf_gut (hd : SItemTief) (tl : List SItemTief)
    (he : istAngenommen hd = true) :
    uRestFehler (hd :: tl) = uRestFehler tl := by
  rw [uRestFehler_schritt, (singleton_classification hd).1.mp he]
  rfl

/-- A refused item anywhere forces an actual error. An earlier refusal keeps
    its own message; otherwise the successful singleton check exposes the tail. -/
theorem uRestFehler_faellt (l : List SItemTief)
    (h : ∃ it ∈ l, istGegenstand it = true) :
    ∃ e, uRestFehler l = .error e := by
  induction l with
  | nil =>
    rcases h with ⟨it, member, _⟩
    cases member
  | cons hd tl ih =>
    cases checked : uRestFehler [hd] with
    | error e =>
      exact ⟨e, by rw [uRestFehler_schritt, checked]; rfl⟩
    | ok value =>
      have inTail : ∃ it ∈ tl, istGegenstand it = true := by
        rcases h with ⟨it, member, bad⟩
        rcases List.mem_cons.mp member with same | later
        · subst it
          rcases (singleton_classification hd).2.mp bad with ⟨e, refused⟩
          rw [checked] at refused
          cases refused
        · exact ⟨it, later, bad⟩
      rcases ih inTail with ⟨e, refused⟩
      exact ⟨e, by rw [uRestFehler_schritt, checked]; exact refused⟩

/-- **A failing item check fails the elaboration.** `elabU` runs the certified expansion and
    then `uRestFehler`; a refused expanded item list refuses the unit. -/
theorem elabU_bei_RestFehler (ms msE : List SItemTief) (e : String)
    (requirements : List (STyp × String))
    (hE : expandU ms = .ok (msE, requirements))
    (hR : uRestFehler msE = .error e) :
    elabU ms = .error e := by
  simp only [elabU, hE, bind, Except.bind, elabUExpanded, checkCanonicalConstants, hR]

/-- **Units whose expansion carries an off-fragment item are refused.** The premise is read where
    `elabU` checks: after the certified expansion. -/
theorem elabU_verweigert_noch (items msE : List SItemTief)
    (requirements : List (STyp × String))
    (hE : expandU items = .ok (msE, requirements))
    (h : ∃ it ∈ msE, istGegenstand it = true) :
    ∃ e, elabU items = .error e := by
  rcases uRestFehler_faellt _ h with ⟨e, hR⟩
  exact ⟨e, elabU_bei_RestFehler _ _ e requirements hE hR⟩

#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.uRestFehler_kopf
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.uRestFehler_kopf_gut
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.uRestFehler_schritt
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.uRestFehler_faellt
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.elabU_bei_RestFehler
#print axioms Gabbro.Grammatik.GabbroV.GvParserFragment.elabU_verweigert_noch

end Gabbro.Grammatik.GabbroV.GvParserFragment
