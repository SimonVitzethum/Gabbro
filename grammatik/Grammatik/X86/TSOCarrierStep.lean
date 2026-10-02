/-
  File:      Grammatik/X86/TSOCarrierStep.lean
  Subject:   Growing TSO history to typed-carrier W transition (lane 650).

  Consumes the append-only `TSOTrace` projections (`traceHist`,
  `traceSicht`, `traceFrisch` over `SpurKnoten`, never the resetting
  `histVon` 0/1 snapshot), the admitted source representation
  (`SourceMemory`: `RepSlot`, `rep_schritt_bleibt`), the grouping
  discipline (`WordAccessGrouping`: `WortGruppe`, `DrainSpur`,
  `FremdFrei`, `wort_gruppe_liest_zurueck`) and the source access
  enumeration (`SourceAccessCompleteness`: `blattFragment_voll`).

  Produces: an explicit inherited history relation (`ErbtW`: W
  timestamps below the trace clock, source view covered by the target
  projection) with proved initial and step preservation, and at least
  one actual typed-carrier `SchrittW` transition for a no-read
  fragment write whose grouped TSO drain installs the same word the
  source step writes -- not only the `lies` consequent. Ordinary
  grouped drains stay observationally grouped under actual access
  exclusion (`WortGruppe` + `FremdFrei` at every visited state), never
  silently hardware-atomic. Full W/GX/LOCK/scheduling closure stays
  OPEN (see CUTS).
-/
import Grammatik.X86.TSOTrace
import Grammatik.X86.SourceMemory
import Grammatik.X86.WordAccessGrouping
import Grammatik.X86.SourceAccessCompleteness
import Grammatik.RufAdaequatG
import Grammatik.RennfreiVoll
import Grammatik.Speichermodell.MaschineW
import Grammatik.Speichermodell.Sicht

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- INHERITED HISTORY (`ErbtW`): the W machine `W` inherits its time
    discipline from the append-only trace node `n`. Every W message
    timestamp is strictly below the trace clock (`traceFrisch`), and
    the source thread view at carrier `e` is covered by the target
    projection (`traceSicht`) of the acting core `c` at the slot
    address `a`. A clock bound plus a view coverage -- never an
    assumed read and never a whole simulation. -/
def ErbtW (n : SpurKnoten) (W : RufMaschineW D) (u : Faden) (c : Nat)
    (e : D.Tab ⊕ D.Glob) (a : Adresse) : Prop :=
  (∀ d m, m ∈ W.hist d → m.ts < traceFrisch n) ∧
  W.sicht u e ≤ traceSicht n c a

/-! ## 1. Initial and step preservation of the inherited history -/

/-- INITIAL: a start W machine (`RufStartW`: one timestamp-0 message
    per carrier, empty views) inherits from any trace start node
    (`spurStart`: clock 1). Both conjuncts compute: `0 < 1` and
    `0 ≤ _`. Every premise is used: `s` names the trace state,
    `M0` the W machine. -/
theorem erbtW_start (s : TSOZustand) (M0 : RufMaschineG D) (u : Faden)
    (c : Nat) (e : D.Tab ⊕ D.Glob) (a : Adresse) :
    ErbtW (spurStart s) (RufStartW M0) u c e a := by
  refine ⟨?_, ?_⟩
  · intro d m hm
    simp only [RufStartW, traceFrisch, spurStart] at hm ⊢
    simp at hm
    subst hm
    exact Nat.zero_lt_one
  · simp only [RufStartW, traceSicht, spurStart]
    exact Nat.zero_le _

/-- STEP: one projected trace step preserves the inheritance. The
    clock never moves backwards (issues keep it, flushes advance by
    one), so every W timestamp stays below it; the writer view only
    ever joins the old clock at the flushed address (hence stays
    above the covered source view by the invariant), every other
    entry is untouched. Every premise is used: `hErbt` for both
    bounds, `hinv` for the joined view, `hs` for the step
    equations. -/
theorem erbtW_schritt (n n' : SpurKnoten) (W : RufMaschineW D) (u : Faden)
    (c : Nat) (e : D.Tab ⊕ D.Glob) (a : Adresse)
    (hErbt : ErbtW n W u c e a) (hinv : SpurInv n)
    (hs : SpurSchritt n n') : ErbtW n' W u c e a := by
  obtain ⟨hClock, hView⟩ := hErbt
  obtain ⟨_, hblick⟩ := hinv
  refine ⟨?_, ?_⟩
  · intro d m hm
    have hlt : m.ts < n.frisch := hClock d m hm
    simp only [traceFrisch]
    cases hs with
    | issue c' a' v' h' hh' hb' hf' =>
      rw [hf']
      exact hlt
    | flush c0' e0' rest' h' he' hh' hb' hf' =>
      rw [hf']
      omega
  · simp only [traceSicht]
    cases hs with
    | issue c' a' v' h' hh' hb' hf' =>
      rw [hb']
      exact hView
    | flush c0 e0 rest h he hh hb hf =>
      have hbca := congrFun hb c
      rw [hbca]
      by_cases hc : c = c0
      · subst hc
        rw [if_pos rfl]
        by_cases ha : a = e0.addr
        · subst ha
          rw [Speichermodell.Sicht.setze_selbst]
          have hle : traceSicht n c e0.addr ≤ n.frisch :=
            Nat.le_of_lt (hblick c e0.addr)
          exact Nat.le_trans hView hle
        · rw [Speichermodell.Sicht.setze_anders _ _ ha]
          exact hView
      · rw [if_neg hc]
        exact hView

/-- FINITE-TRACE TRANSPORT: over every reached trace node the
    inheritance holds: the invariant rides along (via
    `spurSchritt_inv`) and each step preserves the relation. The
    consumer of `spur_verlauf_waechst`'s clock discipline: timestamps
    are never reset, so a start inheritance reaches every grown
    history. Every premise is used: `hr` for the induction,
    `hinv0`/`hErbt0` at the start, both through the steps. -/
theorem erbtW_waechst (n0 n : SpurKnoten) (W : RufMaschineW D) (u : Faden)
    (c : Nat) (e : D.Tab ⊕ D.Glob) (a : Adresse)
    (hr : SpurErreichbar n0 n) (hinv0 : SpurInv n0)
    (hErbt0 : ErbtW n0 W u c e a) : ErbtW n W u c e a := by
  have hboth : ∀ {x}, SpurErreichbar n0 x → SpurInv x ∧ ErbtW x W u c e a := by
    intro x hx
    induction hx with
    | start => exact ⟨hinv0, hErbt0⟩
    | schritt _ hstep ih =>
      exact ⟨spurSchritt_inv _ _ hstep ih.1,
        erbtW_schritt _ _ _ _ _ _ _ ih.2 ih.1 hstep⟩
  exact (hboth hr).2

/- CUTS:
     - `ErbtW` with proved initial (`erbtW_start`), step
       (`erbtW_schritt`) and finite-trace (`erbtW_waechst`) preservation.
     - The actual typed-carrier `SchrittW` is still OPEN in this
       snapshot: next is the no-read fragment write with its grouped
       TSO drain. Read carriers, LOCK, GX runs and scheduling stay
       OPEN throughout.
-/

#print axioms ErbtW
#print axioms erbtW_start
#print axioms erbtW_schritt
#print axioms erbtW_waechst

end Gabbro.Grammatik.X86
