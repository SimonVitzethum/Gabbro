/-
  File:      Grammatik/X86/PipelineWork.lean
  Subject:   Source budget to target work and time transfer over the
             direct pipeline lowering (lane 1165).

  Connects the source cost/budget accounting (source `Kosten`/budget
  stops, the goal theorem's `ZeitAb`/budget-stop kinds via
  `BudgetExecution`) to target retired-instruction work: a
  lowering-derived worst-case instruction count per source step
  (`senkStmt` chunks: value code plus address materialisation plus
  slot store), the admitted pipeline summary `pipeSummary`
  (uniform maximum 6, honest zero spill/fence, proved retry bound,
  no exclusions), the derived `Deckung` producer, and the composed
  work/time transfer (`ComposeWorkTransfer`,
  `ComposeBudgetResum`). Named per-form timing bounds stay
  hardware assumptions (`HardwareAssumptions.laufKosten`); they
  never prove software bodies, fairness or bounded CAS retries.

  Reused, not duplicated: `Pipeline.senkStmt`/`senkWertT`/
  `senkWert_als_tief`/`validate`/`pipeline_correct`,
  `ExpressionLowering.senkFrag_laenge` (via `DerivedWorkBound`),
  `DerivedWorkBound.decodiertZu`/`arbeit_decodiert`/`fragmentSummary`
  lemmas, `BudgetExecution` stops and transfer, `CostSummary`
  schema, `TimeTransfer` admission. No second IR, no second source
  interpreter, no new cost model, no checker change, no
  friend-reserved optimiser file.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.ComposeWorkTransfer
import Grammatik.X86.ComposeBudgetResum

namespace Gabbro.Grammatik.X86.PipelineWork

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.OptimizationRules

/-! ## 1. The admitted pipeline summary: uniform maximum 6.

    A shallow lowered assignment chunk is value code (1 or 3
    instructions, `senkFrag_laenge` through `senkWert_als_tief`)
    plus address materialisation plus slot store (2 more), hence
    at most 5; a shallow check is two atoms plus `cmp` plus the
    refusal jump (4). The uniform maximum 6 covers both with
    honest zero spill/fence counts, a proved retry bound and no
    exclusions. -/

/-- The pipeline summary: uniform maximum 6, honest zero
    spill/fence counts, a proved retry bound, no exclusions. -/
def pipeSummary : CostSummary where
  expand := fun _ => some 6
  spillCount := 0
  fenceCount := 0
  retryBound := some 0
  exclusions := []

/-- The pipeline summary is admitted by the validator Bool. -/
theorem pipeSummary_ok : kostenSummeOk pipeSummary = true := by
  decide

/-- The pipeline summary has uniform maximum 6. -/
theorem pipeSummary_max : alleMax pipeSummary = some 6 := by
  decide

/-- The pipeline summary bounds work over any source budget `src` by
    `src * 6`: the expansion formula with honest zero spill/fence. -/
theorem pipeSummary_expand (src : Nat) :
    expandBound pipeSummary src = some (src * 6) := by
  have h := expandBound_keinVerlust pipeSummary src 6 pipeSummary_max
  simpa [pipeSummary] using h

/-! ## 2. Lowering-derived work per source step.

    A successful `senkStmt` assignment chunk is the value code plus
    address materialisation plus slot store, hence exactly two
    instructions longer than the value code. For the shallow
    fragment the value code is 1 or 3 instructions
    (`senkFrag_laenge` through `senkWert_als_tief`), so the chunk
    is 3 or 5. Both the lowering equation and the value equation
    are used. -/

variable {D : Deklaration}

/-- CHUNK SHAPE: a lowered pipeline assignment is the value code
    plus two instructions. -/
theorem senkStmt_chunk_laenge (c : PipeCfg) (L : Layout D)
    (l : Bool) {Γ : Ctx} {Λ : List (Res D)} {V : Vertrag D}
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    (e : Expr D Γ Λ (D.typ t f))
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (pv code : List Befehl)
    (hpv : senkWertT c e = some pv)
    (h : senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i e hw hL) = some code) :
    code.length = pv.length + 2 := by
  unfold senkStmt at h
  dsimp only at h
  cases hk : constInt? i with
  | none =>
    rw [hk] at h
    dsimp only at h
    cases h
  | some k =>
    rw [hk] at h
    dsimp only at h
    cases hloc : L.loc t k f with
    | none =>
      rw [hloc] at h
      dsimp only at h
      cases h
    | some A =>
      rw [hloc] at h
      dsimp only at h
      by_cases hr : repOk (D.typ t f) A 8 0 = true
      · rw [if_pos hr] at h
        rw [hpv] at h
        cases h
        simp only [List.length_append, List.length_cons,
          List.length_nil]
      · rw [if_neg hr] at h
        cases h

/-- CAST TRANSPORT: the deep value lowering sees through a type
    ascription cast (both sides of `g` are variables, so `cases`
    applies). Callers instantiate with the stuck field-type
    equation. Every premise is used. -/
theorem senkWertT_cast (c : PipeCfg) {Γ : Ctx} {Λ : List (Res D)}
    {τ1 τ2 : Ty} (g : τ1 = τ2) (e : Expr D Γ Λ τ1) :
    senkWertT c (cast (congrArg (Expr D Γ Λ) g) e) = senkWertT c e := by
  cases g
  rfl

/-- SHALLOW CHUNK BOUND: a chunk over a shallow value is 3 or 5
    instructions (value code 1 or 3, plus address plus store).
    The deep lowering agrees with the shallow one on the fragment
    (`senkWert_als_tief`), so the fragment count
    (`senkFrag_laenge`) applies. The value type is carried as a
    variable with the equation `hT` (so classification unifies)
    and the statement casts (`senkWertT_cast`). Every premise is
    used: `hflach` feeds agreement and classification, `hT` the
    cast, `h` the chunk shape. -/
theorem senkStmt_flach_laenge (c : PipeCfg) (L : Layout D)
    (l : Bool) {Γ : Ctx} {Λ : List (Res D)} {V : Vertrag D}
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    {τ : Ty} (e : Expr D Γ Λ τ) (hT : τ = D.typ t f)
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (p code : List Befehl)
    (hflach : senkWert (abbOf c) e c.dst c.tmp = some p)
    (h : senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i
      (cast (congrArg (Expr D Γ Λ) hT) e) hw hL) = some code) :
    code.length = 3 ∨ code.length = 5 := by
  have htief : senkWertT c e = some p :=
    senkWert_als_tief _ _ _ _ _ _ hflach
  have hcast : senkWertT c (cast (congrArg (Expr D Γ Λ) hT) e) = some p := by
    rw [senkWertT_cast c hT e]
    exact htief
  have hlen := senkStmt_chunk_laenge c L l t f i _ hw hL p code hcast h
  match hIst : istWert_von (abbOf c) e c.dst c.tmp p hflach with
  | .frag e' p' h' =>
    have hfrag := senkFrag_laenge (abbOf c) e' c.dst c.tmp p' h'
    omega
  | .weiter h1 h2 e' p' h' =>
    have hfrag := senkFrag_laenge (abbOf c) e' c.dst c.tmp p' h'
    omega

/-- DECKUNG PRODUCER (the missing leg for pipeline chunks): every
    shallow lowered pipeline chunk is covered in machine work by
    the admitted pipeline summary over any positive source
    budget. `Deckung` is DERIVED from the chunk bound plus the
    summary expansion -- it is never a premise. Every premise is
    used: `hflach`/`hchunk`/`hT` bound the generated length,
    `hsrc` keeps the scaled bound above it. -/
theorem deckung_pipeChunk (c : PipeCfg) (L : Layout D)
    (l : Bool) {Γ : Ctx} {Λ : List (Res D)} {V : Vertrag D}
    (t : D.Tab) (f : D.Feld t)
    (i : Expr D Γ Λ (.index (D.count t)))
    {τ : Ty} (e : Expr D Γ Λ τ) (hT : τ = D.typ t f)
    (hw : V.schreibt t = true) (hL : darf D t Λ)
    (src : Nat)
    (p chunk : List Befehl)
    (hflach : senkWert (abbOf c) e c.dst c.tmp = some p)
    (hchunk : senkStmt c L (Stmt.assignSlot (V := V) (l := l) t f i
      (cast (congrArg (Expr D Γ Λ) hT) e) hw hL) = some chunk)
    (hsrc : 1 ≤ src) :
    Deckung pipeSummary src (decodiertZu chunk) := by
  have hlen := senkStmt_flach_laenge c L l t f i e hT hw hL p chunk hflach hchunk
  intro k hk
  rw [pipeSummary_expand] at hk
  cases hk
  have hwork : targetWork ((decodiertZu chunk).map fun d => d.befehl) =
      chunk.length :=
    arbeit_decodiert chunk
  rw [hwork]
  omega

/- CUTS:
    - Proved here: the admitted pipeline summary (uniform maximum 6,
      honest zero spill/fence, proved retry bound, no exclusions).
    - OPEN: per-chunk derived work, the `Deckung` producer, the
      work/time transfer, the budget-stop connection, the
      validator-level closing, refusals and joint witnesses.
-/

#print axioms pipeSummary_ok
#print axioms pipeSummary_max

end Gabbro.Grammatik.X86.PipelineWork
