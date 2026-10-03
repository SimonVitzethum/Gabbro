/-
  File:      Grammatik/X86/OptRangeElim.lean
  Subject:   Range/bound/overflow-check elimination rule lemma (lane 867).

  DESIGN section 7 row: local premise "source extent proof AT the site
  (N571/N463/N506: gate ensures over once-bound name; constant
  fixed-size)", certificate "B+C", failure cases "entry invariant
  removes check inside writer's own mutating loop; entry range across a
  writing call", phase M, cost O(sites).
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- Validator-decided side conditions for one range-check site. -/
structure RangeElimCert where
  extentAmOrt : Bool
  einmalGebunden : Bool
  keinSchreiberDazwischen : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. -/
def rangeElimZulassen (c : RangeElimCert) : Bool :=
  c.extentAmOrt && c.einmalGebunden && c.keinSchreiberDazwischen

/-- No at-site extent proof: refuse. -/
theorem rangeElimVerweigert_ohneAusmass (c : RangeElimCert)
    (h : c.extentAmOrt = false) :
    rangeElimZulassen c = false := by
  simp [rangeElimZulassen, h]

/-- Twice-bound name carries no extent (N571): refuse. -/
theorem rangeElimVerweigert_zweitbindung (c : RangeElimCert)
    (h : c.einmalGebunden = false) :
    rangeElimZulassen c = false := by
  simp [rangeElimZulassen, h]

/-- An intervening writer (writing call; writer's own mutating loop): refuse. -/
theorem rangeElimVerweigert_schreiberDazwischen (c : RangeElimCert)
    (h : c.keinSchreiberDazwischen = false) :
    rangeElimZulassen c = false := by
  simp [rangeElimZulassen, h]

/-! ## Probes: admission passes only with every side condition. -/

/-- Probe: the fully admitted certificate passes. -/
theorem probe_rangeElimZulassen_ok :
    rangeElimZulassen ⟨true, true, true⟩ = true := by
  decide

/-- Probe: no at-site extent proof is refused. -/
theorem probe_rangeElimZulassen_ohneAusmass :
    rangeElimZulassen ⟨false, true, true⟩ = false := by
  decide

/-- Probe: a twice-bound name is refused. -/
theorem probe_rangeElimZulassen_zweitbindung :
    rangeElimZulassen ⟨true, false, true⟩ = false := by
  decide

/-- Probe: an intervening writer is refused. -/
theorem probe_rangeElimZulassen_schreiber :
    rangeElimZulassen ⟨true, true, false⟩ = false := by
  decide

/-! ## Connection: the admitted narrow takes the checked branch.

    The rewrite drops `Block.narrow e lo' hi' sonst rest` to its checked
    continuation `rest` with the same evaluated value. The rule lemma is
    over ARBITRARY values (`e` is any expression): the DESIGN local
    premise "source extent proof AT the site (N571/N463/N506 over a
    once-bound name)" arrives as the validator-recomputed side condition
    `hRegel`, conditional on admission `hz` -- the equation is claimed
    only where the validator admitted the site, exactly like the
    admitted float fold of the sibling file. Entry-invariant-across-call
    and writer's-own-mutating-loop removals never reach `hRegel`:
    `keinSchreiberDazwischen = false` forces `rangeElimZulassen = false`
    (`rangeElimVerweigert_schreiberDazwischen`), so no `hz` exists.

    Conclusion, jointly: the `execBlock` OUTCOME is equal -- same
    constructor, same successor worlds and environments -- so no fault
    is added or removed (`logik`/`hardware` agree, including
    `logik bereich` from IEEE ranges, which the checked window keeps),
    every downstream observation agrees (contracts at their place read
    the same values from the same environments, call logs gain no event,
    no shared access is added or removed for concurrency -- both sides
    read `e.orte` through the same `lese`), and the step-budget
    accounting is unchanged (the removed test is pure and unbudgeted).
    Certificate shape: the local rewrite record (which `narrow` site,
    target `lo'..hi'`) plus the recomputed analysis citations behind
    `hRegel` (B: at-site extent over the once-bound name; C: duty
    binding -- no intervening writer). Nothing here derives an
    `ensures`, turns a refusal into a warning, or speculates a faulting
    form above its guard: without admission the `sonst` branch stays. -/

/-- CONNECTION: an admitted `narrow` behaves like its checked
    continuation, with the same value, outcome and observations. -/
theorem OptRangeElim_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {lo hi lo' hi' : Int}
    (e : Expr D Γ Λ (.int lo hi))
    (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l ((.int lo' hi') :: Γ) Λ Λ')
    (σ : World D) (ρ : Env D Γ)
    (c : RangeElimCert)
    (hRegel : rangeElimZulassen c = true →
      lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')
    (hz : rangeElimZulassen c = true) :
    execBlock O passes R (Block.narrow e lo' hi' sonst rest) σ ρ
      = (execBlock O passes R rest (σ.lese Λ e.orte)
          (Env.cons ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n,
            (hRegel hz).1, (hRegel hz).2⟩ ρ)).schrumpf := by
  simp only [execBlock]
  rw [dif_pos (hRegel hz)]

/-! ## Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptRangeElim_verbindung` instantiated JOINTLY:
    the literal `3` narrows into `0..10` under a `Block.narrow` with a
    `leave` else-branch and a `nil` continuation, in the NON-DEGENERATE
    reference program `refD` (whose `einzahlen` writes its table,
    `refEin_schreibt`), beside the reached F-machine run `MB` that
    changes memory (`refB_erreicht`, `refB_schreibt`: slot `0 -> 100`).
    The admitted certificate is `⟨true, true, true⟩`; `hRegel` is the
    kernel-checked range fact `0 ≤ 3 ∧ 3 ≤ 10`. Every conjunct is used. -/

/-- JOINT WITNESS for `OptRangeElim_verbindung`: `3` narrows into
    `0..10` on `refD`, beside the memory-changing reached run. -/
theorem OptRangeElim_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (l : Bool) (Γ : Ctx) (Λ Λ' : List (Res refD))
      (lo hi lo' hi' : Int)
      (e : Expr refD Γ Λ (.int lo hi))
      (sonst : Endblock refD V l Γ Λ)
      (rest : Block refD V l ((.int lo' hi') :: Γ) Λ Λ')
      (σ : World refD) (ρ : Env refD Γ)
      (c : RangeElimCert)
      (hRegel : rangeElimZulassen c = true →
        lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
        (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi')
      (hz : rangeElimZulassen c = true),
      execBlock O passes R (Block.narrow e lo' hi' sonst rest) σ ρ
        = (execBlock O passes R rest (σ.lese Λ e.orte)
            (Env.cons ⟨(eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n,
              (hRegel hz).1, (hRegel hz).2⟩ ρ)).schrumpf
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, true, [], [], [],
    3, 3, 0, 10, .lit 3, Endblock.leave rfl, Block.nil,
    refSp0.welt [], Env.nil, ⟨true, true, true⟩, (fun _ => by decide),
    by decide, ?_, refEin_schreibt (), refB_erreicht, refB_schreibt⟩
  exact OptRangeElim_verbindung (V := vertragVon refD refEin) (O := refO)
    (passes := 0) (R := keinRuf) (e := (.lit 3))
    (sonst := Endblock.leave rfl) (rest := Block.nil)
    (σ := refSp0.welt []) (ρ := Env.nil) (c := ⟨true, true, true⟩)
    (fun _ => by decide) (by decide)

/- CUTS:
    - No `pruefung` connection: only `Block.narrow` gets the elimination
      equation; `where`-condition removal stays with a later lane.
    - No overflow-check elimination: arithmetic overflow guards (the
      DESIGN row's third shape) are not covered here.
    - No totalCost inequality: the eliminated window keeps the same block
      shape with one pure test removed, so step-budget accounting is
      unchanged; the formal level-(c) machine-work bound is OPEN per
      IR-VALIDIERUNG.
    - No silicon correspondence, no TSO/GX bridge, no ABI/loader claim:
      correspondence stops at the source `execBlock` outcome equality.
    - The validator's recomputation behind `hRegel` (B: at-site extent
      over the once-bound name; C: duty binding with no intervening
      writer) is the consumer's obligation; this file is its interface.
-/

#print axioms rangeElimZulassen
#print axioms rangeElimVerweigert_ohneAusmass
#print axioms rangeElimVerweigert_zweitbindung
#print axioms rangeElimVerweigert_schreiberDazwischen
#print axioms probe_rangeElimZulassen_ok
#print axioms probe_rangeElimZulassen_ohneAusmass
#print axioms probe_rangeElimZulassen_zweitbindung
#print axioms probe_rangeElimZulassen_schreiber
#print axioms OptRangeElim_verbindung
#print axioms OptRangeElim_verbindung_zeuge

end Gabbro.Grammatik.X86
