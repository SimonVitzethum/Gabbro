/-
  Audit 20, slice Ziel.lean lines 1200-end: standalone checkable facts about
  the SHAPES used in the slice. Nothing here modifies the slice; each theorem
  below demonstrates one structural point the report relies on.

  F1 (pattern e): `hsingle : forall st in M.lauf, st.faden = f` (needed by
  `kette_mit_zeugen_schritt`, Ziel.lean:1516) is unsatisfiable on any run that
  contains steps of two distinct threads. Concrete TestD witness below.

  F2 (pattern b): `hlen` (Ziel.lean:1542, 2016) is a derived length equation
  with no later consumer in either proof. The list-level fact below shows the
  derivation needs only `hJw` and `J.hKette` and its result is unused -- the
  on-file evidence (grep: `hlen` occurs exactly twice, both as `have`, never
  referenced) is in the report.

  F3 (pattern d): the section-10 header calls the `SerialLink` conclusion
  "UNCONDITIONAL", but `SerialLink` (InterferenzAllgemein.lean:1721) is an
  implication per chain step: a non-writing thread owes no witness event. The
  theorem below shows the vacuous leg: with no writing step, the link holds
  over ANY run, so the "unconditional" wording claims more than the Lean.

  F4 (pattern b): `hwitschritt_kleber_reuse` (Ziel.lean:1914) has exactly the
  callee `kette_mit_zeugen_schritt` premises and conclusion -- pure forwarding.
  The Prop-level fact below shows forwarding adds nothing (identity).

  F5 (pattern d): stale line references in the §11/§12 headers -- on-file
  evidence only, UNVERIFIED (no Lean demonstration possible).
-/
import Grammatik.Wettlauf
import Grammatik.InterferenzAllgemein
import Grammatik.Zeugnis

namespace MuseAudit20

open Gabbro.Grammatik

-- F1: a two-thread TestD run falsifies `hsingle` for every choice of `f`.
def twoThreadRun : Lauf TestD :=
  [Schritt.mk 0 (.zugriff () true [] []), Schritt.mk 1 (.zugriff () true [] [])]

theorem F1_two_threads_break_hsingle (f : Faden)
    (h : ∀ st ∈ twoThreadRun, st.faden = f) : False := by
  have h0 : (⟨0, (.zugriff () true [] [])⟩ : Schritt TestD) ∈ twoThreadRun := by
    simp [twoThreadRun]
  have h1 : (⟨1, (.zugriff () true [] [])⟩ : Schritt TestD) ∈ twoThreadRun := by
    simp [twoThreadRun]
  have e0 := h _ h0
  have e1 := h _ h1
  simp only [] at e0 e1
  have h01 : (0 : Faden) = 1 := e0.trans e1.symm
  simp at h01

#print axioms MuseAudit20.F1_two_threads_break_hsingle

-- F3: vacuous leg of `SerialLink`: a step whose code does not write the
-- carrier discharges the link implication without any run event.
theorem F3_link_needs_no_event_without_write (Nb : Nebeneinander)
    (J : GemeinsamerLauf (D := TestD) Nb) (run : Lauf TestD)
    (t₀ : TestD.Tab) (g : Faden)
    (hnowrite : TraegerSchreibt (J.code g) (.inl t₀) = false) :
    (TraegerSchreibt (J.code g) (.inl t₀) = true →
      ∃ (j : Nat) (w : Bool) (Λ : List (Res TestD)) (h : List TestD.Lock),
        run[j]? = some (Schritt.mk g (.zugriff t₀ w Λ h))) := by
  intro hw
  rw [hnowrite] at hw
  contradiction

#print axioms MuseAudit20.F3_link_needs_no_event_without_write

-- F4: forwarding shape: concluding `Q` from premises that already conclude
-- `Q` adds nothing -- the proof term is the identity on the callee result.
theorem F4_forwarding_is_identity (P Q : Prop) (callee : P → Q) (h : P) : Q :=
  callee h

#print axioms MuseAudit20.F4_forwarding_is_identity

/-!
CUTS:
- F1 shows `hsingle` excludes two-thread runs, but does NOT show the slice's
  goal theorems are actually applied to two-thread runs: the HB disjunction
  conjunct only needs two access EVENTS, which a single-thread run could also
  contain at different indices. Whether the conjunction is truly empty per
  program is NOT proved here.
- F2's dead-`have` claim rests on grep evidence (no later use of `hlen`),
  not on a Lean proof of non-use; Lean has no "unused hypothesis" witness.
- F3 shows the conditional shape of `SerialLink`, not that any slice theorem
  misuses it: `kette_mit_zeugen_schritt` does discharge the writing leg via
  `hneu_wit`. The finding is about the HEADER wording ("unconditional"),
  demonstrated by exhibiting the vacuous leg.
- F4 shows the forwarding SHAPE at Prop level, not a proof that
  `hwitschritt_kleber_reuse` is useless: as a named `hWitSchritt`-shaped
  lemma it may serve documentation. The finding is pattern (b) in the weak
  sense (conclusion = callee conclusion, premises = callee premises).
- F5 (stale line numbers in §11/§12 headers) has no Lean demonstration:
  UNVERIFIED.
-/
