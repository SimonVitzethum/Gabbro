/-
  File:      Grammatik/X86/OptBoundElim.lean
  Subject:   Bound-check elimination rule lemma (lane 868).

  DESIGN section 7 row: local premise "source extent proof AT the site
  (N571/N463/N506: gate ensures over once-bound name; constant
  fixed-size)", certificate "B+C", failure cases "entry invariant removes
  check inside writer's own mutating loop; entry range across a writing
  call", phase M, cost O(sites).

  What is proved here, over the REUSED canonical vocabulary (`Typen`,
  `Syntax`, `Semantik`, `ReferenzB`): a redundant `Block.narrow` guard
  takes the `rest` branch with the widened value wherever the validator
  admits the site, and the admitted checked window equals the unchecked
  continuation (no value, fault or observation change). Both DESIGN
  failure cases are refused by `boundZulassen`. No `ensures` is derived,
  no refusal becomes a warning, no faulting form is speculated above its
  guard.
-/
import Grammatik.Typen
import Grammatik.Syntax
import Grammatik.Semantik
import Grammatik.ReferenzB
import Grammatik.X86.Typen
import Grammatik.X86.Wort

namespace Gabbro.Grammatik.X86

open Gabbro.Grammatik

/-- The validator-decided side conditions for one bound-check site
    (DESIGN section 7 row): the source extent proof holds AT the site
    (`umfangOk`: N571 gate ensures over a once-bound name, N463/N506
    constant fixed-size, recomputed by the validator), no writer runs
    between the extent fact and the site (`keinSchreiber`), and no
    writing call intervenes (`keinRufSchreiber`). -/
structure BoundCert where
  umfangOk : Bool
  keinSchreiber : Bool
  keinRufSchreiber : Bool
  deriving DecidableEq, Repr

/-- Admission: every side condition holds. A refused OPTIONAL
    optimisation falls back to another certified translation (the
    check stays), never to a warning. -/
def boundZulassen (c : BoundCert) : Bool :=
  c.umfangOk && c.keinSchreiber && c.keinRufSchreiber

/-! ## 1. Refusal: the two DESIGN failure cases must NOT eliminate.

    An entry invariant used to remove a check inside the writer's OWN
    mutating loop is refused: `keinSchreiber = false` forces
    `boundZulassen = false` (the extent fact does not survive the
    writer at the site). An entry range carried across a writing call
    is refused: `keinRufSchreiber = false` forces `false` (the callee
    may write the carrier the range speaks about). Both are proved of
    the decided Bool, so the validator cannot silently skip them. -/

/-- A writer between fact and site refuses the elimination. -/
theorem boundVerweigert_schreiber (c : BoundCert)
    (h : c.keinSchreiber = false) :
    boundZulassen c = false := by
  simp [boundZulassen, h]

/-- A writing call between fact and site refuses the elimination. -/
theorem boundVerweigert_ruf (c : BoundCert)
    (h : c.keinRufSchreiber = false) :
    boundZulassen c = false := by
  simp [boundZulassen, h]

/-- A missing extent proof refuses the elimination. -/
theorem boundVerweigert_umfang (c : BoundCert)
    (h : c.umfangOk = false) :
    boundZulassen c = false := by
  simp [boundZulassen, h]

/-- Probe: the fully admitted certificate passes. -/
theorem probe_boundZulassen_ok :
    boundZulassen ⟨true, true, true⟩ = true := by
  decide

/-- Probe: a writer-loop certificate is refused. -/
theorem probe_boundZulassen_schreiber :
    boundZulassen ⟨true, false, true⟩ = false := by
  decide

/-- Probe: a cross-call certificate is refused. -/
theorem probe_boundZulassen_ruf :
    boundZulassen ⟨true, true, false⟩ = false := by
  decide

/-! ## 2. Value: widening to the checked range keeps the number.

    Over ARBITRARY values (`v : Zahl lo hi`): the narrowed value IS
    the evaluated value (`Zahl.weiter` only carries the range proof).
    The range containment is the validator's recomputed extent fact
    (`hLink`, conditional on admission like the recomputation
    obligation it is); the value fact needs no additional premise. -/

/-- The widened value is the evaluated value. -/
theorem boundWeiter_wert {lo hi lo' hi' : Int} (v : Zahl lo hi)
    (h1 : lo' ≤ lo) (h2 : hi ≤ hi') :
    (Zahl.weiter h1 h2 v).n = v.n := by
  rfl

/-- Probe: `7` widened from `7..7` to `0..10` stays `7`. -/
theorem probe_boundWeiter :
    (Zahl.weiter (lo := 7) (hi := 7) (lo' := 0) (hi' := 10)
      (by decide) (by decide)
      (⟨7, by decide, by decide⟩ : Zahl 7 7)).n = 7 := by
  decide

/-! ## 3. Connection: the admitted check always passes, so removing it
    changes nothing.

    The rewrite fires only where the validator admits the site (`hz`)
    with a recomputed extent proof (`hLink`: the source type range
    inside the checked range, the N571/N463/N506 shape). It is stated
    at a `Block.narrow` window with an ARBITRARY `sonst` (dead under
    admission) and an ARBITRARY continuation `rest`, so the conclusion
    covers every downstream observation at once. Conclusion, jointly:
    (1) the pushed VALUE is preserved (the widened value IS the
    evaluated value);
    (2) the `execBlock` OUTCOME equals the unchecked continuation --
    same constructor, same successor worlds and environments -- so no
    fault is added or removed (`logik`/`hardware` agree: the `sonst`
    branch is dead), every downstream observation agrees (contracts
    at their place read the same values from the same environments,
    call logs gain no event, no shared access is added or removed for
    concurrency -- both sides read `e.orte` through the same `lese`,
    IEEE float state travels in the equal successor worlds), and the
    step-budget accounting is unchanged (same downstream block shape;
    the removed check is pure and unbudgeted).
    Nothing here derives an `ensures`, turns a refusal into a
    warning, or speculates a faulting form above its guard: where the
    validator refuses, the check stays. -/

/-- CONNECTION: an admitted bound check behaves like the unchecked
    continuation with the widened value. -/
theorem OptBoundElim_verbindung {D : Deklaration} (V : Vertrag D)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    {Γ : Ctx} {Λ Λ' : List (Res D)} {l : Bool}
    {lo hi lo' hi' : Int}
    (e : Expr D Γ Λ (.int lo hi))
    (sonst : Endblock D V l Γ Λ)
    (rest : Block D V l ((.int lo' hi') :: Γ) Λ Λ')
    (cert : BoundCert)
    (hz : boundZulassen cert = true)
    (hLink : boundZulassen cert = true → (lo' ≤ lo ∧ hi ≤ hi'))
    (σ : World D) (ρ : Env D Γ) :
    (Zahl.weiter (hLink hz).1 (hLink hz).2
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)).n
      = (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n
    ∧ execBlock O passes R (Block.narrow e lo' hi' sonst rest) σ ρ
      = (execBlock O passes R rest (σ.lese Λ e.orte)
          (.cons (Zahl.weiter (hLink hz).1 (hLink hz).2
            (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) ρ)).schrumpf := by
  have hB := hLink hz
  have hlo : lo ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n :=
    (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).lo_le
  have hhi : (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi :=
    (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).le_hi
  have hv : lo' ≤ (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ∧
      (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n ≤ hi' := by
    constructor <;> omega
  refine ⟨rfl, ?_⟩
  simp only [execBlock, Zahl.weiter, dif_pos hv]

/-! ## 4. Joint witness: the rule fires on a real program that moves memory.

    ALL premises of `OptBoundElim_verbindung` instantiated JOINTLY:
    the literal `7 : .int 7 7` against the checked range `0..10`
    under a `narrow` with a `leave` else-branch and a `nil`
    continuation, in the NON-DEGENERATE reference program `refD`
    (whose `einzahlen` writes its table, `refEin_schreibt`), beside
    the reached F-machine run `MB` that changes memory
    (`refB_erreicht`, `refB_schreibt`: slot `0 -> 100`). Both
    conjuncts are used. -/

/-- JOINT WITNESS for `OptBoundElim_verbindung`: `7` in `7..7`
    passes the `0..10` check on `refD`, beside the memory-changing
    reached run. -/
theorem OptBoundElim_verbindung_zeuge :
    ∃ (V : Vertrag refD) (O : Orakel refD) (passes : Nat)
      (R : ∀ f : refD.Fn, World refD → Env refD (refD.params f) → RufAusgang f)
      (Γ : Ctx) (Λ Λ' : List (Res refD)) (l : Bool)
      (lo hi lo' hi' : Int)
      (e : Expr refD Γ Λ (.int lo hi))
      (sonst : Endblock refD V l Γ Λ)
      (rest : Block refD V l ((.int lo' hi') :: Γ) Λ Λ')
      (cert : BoundCert)
      (_hz : boundZulassen cert = true)
      (_hLink : boundZulassen cert = true → (lo' ≤ lo ∧ hi ≤ hi'))
      (σ : World refD) (ρ : Env refD Γ),
      (Zahl.weiter (lo := lo) (hi := hi) (lo' := lo') (hi' := hi')
          (by obtain ⟨h1, _⟩ := _hLink _hz; exact h1)
          (by obtain ⟨_, h2⟩ := _hLink _hz; exact h2)
          (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)).n
        = (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ).n
      ∧ execBlock O passes R (Block.narrow e lo' hi' sonst rest) σ ρ
        = (execBlock O passes R rest (σ.lese Λ e.orte)
            (.cons (Zahl.weiter (lo := lo) (hi := hi) (lo' := lo') (hi' := hi')
              (by obtain ⟨h1, _⟩ := _hLink _hz; exact h1)
              (by obtain ⟨_, h2⟩ := _hLink _hz; exact h2)
              (eval (σ.lese Λ e.orte) e (σ.lese Λ e.orte) ρ)) ρ)).schrumpf
      ∧ (vertragVon refD refEin).schreibt () = true
      ∧ RufErreichbarF refP refO 0 (RufStartF refP refSp0 initB) MB
      ∧ MB.speicher.slots () 0 () ≠ refSp0.slots () 0 () := by
  have hV := OptBoundElim_verbindung (D := refD) (V := vertragVon refD refEin)
    (O := refO) (passes := 0) (R := keinRuf) (Γ := []) (Λ := []) (Λ' := [])
    (l := true) (lo := 7) (hi := 7) (lo' := 0) (hi' := 10)
    (e := Expr.lit 7) (sonst := Endblock.leave rfl) (rest := Block.nil)
    (cert := ⟨true, true, true⟩) (hz := by decide)
    (hLink := fun _ => ⟨by decide, by decide⟩)
    (σ := refSp0.welt []) (ρ := Env.nil)
  refine ⟨vertragVon refD refEin, refO, 0, keinRuf, [], [], [], true,
    7, 7, 0, 10, Expr.lit 7, Endblock.leave rfl, Block.nil,
    ⟨true, true, true⟩, by decide, (fun _ => ⟨by decide, by decide⟩),
    refSp0.welt [], Env.nil, ?_, ?_, ?_, ?_, ?_⟩
  · exact hV.1
  · exact hV.2
  · exact refEin_schreibt ()
  · exact refB_erreicht
  · exact refB_schreibt

/- CUTS:
    - No hoisted entry facts: the extent proof is required AT the site
      (`hLink` over the admitted certificate); entry invariants
      hoisted across the writer's own mutating loop or across a
      writing call are refused (`boundVerweigert_schreiber`,
      `boundVerweigert_ruf`), never weakened into warnings.
    - No overflow-check rule: only the `Block.narrow` range guard is
      covered; arithmetic overflow guards stay with their lane.
    - No totalCost inequality: the admitted window keeps the same
      downstream block shape with one pure check removed, so
      step-budget accounting is unchanged; the formal level-(c)
      machine-work bound is OPEN per IR-VALIDIERUNG (lane 278).
    - No silicon correspondence, no TSO/GX bridge, no ABI/loader claim:
      correspondence stops at `eval` values and `execBlock` outcomes.
-/

#print axioms boundZulassen
#print axioms boundVerweigert_schreiber
#print axioms boundVerweigert_ruf
#print axioms boundVerweigert_umfang
#print axioms boundWeiter_wert
#print axioms probe_boundWeiter
#print axioms OptBoundElim_verbindung
#print axioms OptBoundElim_verbindung_zeuge

end Gabbro.Grammatik.X86
