/-
  File:      Grammatik/X86/OptimizationWitnesses.lean
  Subject:   Joint `_zeuge` witnesses, positive probes and poison probes for
             `Grammatik/X86/OptimizationRules.lean` (grammatik/OPTIMIZER.md
             §§10.1, 10.2, 11.2).

  Every generic theorem of the rules file whose premises range over source
  syntax gets a companion `<name>_zeuge` that instantiates ALL its premises
  JOINTLY, on the non-degenerate witness declaration `InvariantenOpt.wD`
  (one table, written by its contract `wV`: `InvariantenOpt.wit_schreibt`).
  The block witnesses run a program whose run changes memory
  (`wP_run`, `wPOpt_run`: the slot moves from `0` to `5`).

  Poison probes are certificates the validators MUST refuse (§10.2): a fold
  that would delete a read, an undecided or always-failing check, an
  unentailed `narrow`, signed division, a non-power-of-two, a possibly
  negative or overflowing operand, a float condition, a pipeline out of
  order and a mislabelled certificate. Each is checked by computation.
-/
import Grammatik.X86.OptimizationRules
import Grammatik.X86.InvariantenOpt

namespace Gabbro.Grammatik.X86.OptimizationWitnesses

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.OptimizationRules
open Gabbro.Grammatik.X86.InvariantenOpt (wD wV wO wR wWorld0 wit_schreibt)

/-! ## 1. Building blocks over the witness declaration -/

/-- The one slot of the table, in any context. -/
def idx (Γ : Ctx) : Expr wD Γ [] (.index (wD.count ())) := .lit 0

/-- A store into the table's slot: the memory-changing statement. -/
def store {Γ : Ctx} (e : Expr wD Γ [] (wD.typ () ())) : Stmt wD wV true Γ [] [] :=
  .assignSlot () () (idx Γ) e rfl (fun _ hw => False.elim (List.not_mem_nil hw))

/-- `3`, at the declared range `0 .. 5`. -/
def xVal : Expr wD [] [] (.int 0 5) := .weiter (by decide) (by decide) (.lit 3)

/-- `2 + 3`, widened to the slot type `0 .. 10`: a constant to fold. -/
def five {Γ : Ctx} : Expr wD Γ [] (wD.typ () ()) :=
  .weiter (show (0 : Int) ≤ 2 + 3 by decide) (show (2 : Int) + 3 ≤ 10 by decide)
    (.add (.lit 2) (.lit 3))

/-- The folded form of `five`. -/
def fiveLit {Γ : Ctx} : Expr wD Γ [] (wD.typ () ()) :=
  .weiter (show (0 : Int) ≤ 5 by decide) (show (5 : Int) ≤ 10 by decide) (.lit 5)

/-- The variable bound by the outer `bind`, range `0 .. 5`. -/
def xVar {Γ : Ctx} : Expr wD (.int 0 5 :: Γ) [] (.int 0 5) := .var .hier

/-- The check `x <= 10`: decided `true` by `x`'s TYPE range, not by a constant. -/
def xCheck {Γ : Ctx} : Expr wD (.int 0 5 :: Γ) [] .bool := .le xVar (.lit 10)

/-! ## 2. The witness program and its optimised form

    ```
    let x : 0 .. 5 = 3;
    where x <= 10 else leave;          -- range-decided: removable (B1)
    let y = narrow x to 0 .. 10 else leave;   -- entailed: a widening (B2)
    T.slot[0] = y;
    T.slot[0] = 2 + 3;                 -- constant: folds to 5 (C1)
    ``` -/

/-- The source program. -/
def wP : Block wD wV true [] [] [] :=
  .bind xVal
    (.pruefung xCheck (.leave rfl)
      (.narrow xVar 0 10 (.leave rfl)
        (.cons (store (.var .hier)) (.cons (store five) .nil))))

/-- The program the certified pipeline must produce. -/
def wPOpt : Block wD wV true [] [] [] :=
  .bind xVal
    (.bind (.weiter (show (0 : Int) ≤ 0 by decide) (show (5 : Int) ≤ 10 by decide) xVar)
      (.cons (store (.var .hier)) (.cons (store fiveLit) .nil)))

/-- Fold the second store's value: `bind` -> `where` -> `narrow` -> `cons`
    -> `cons`, then its head statement. -/
def cFold : BlockCert := .rest (.rest (.rest (.rest (.head (.assignSlotValue .foldInt)))))

/-- Drop the check behind the outer `bind`. -/
def cDrop : BlockCert := .rest .dropCheck

/-- Turn the entailed `narrow` behind the outer `bind` into a widening. -/
def cNarrow : BlockCert := .rest .narrowEntailed

/-- The certificate pipeline, in the admitted order of OPTIMIZER.md §9:
    fold first, then the two check removals. -/
def wPipe : List (PassKind × BlockCert) :=
  [(.fold, cFold), (.checks, cDrop), (.checks, cNarrow)]

/-- **Positive probe**: the validator accepts the pipeline and produces
    exactly the optimised program. -/
theorem wPipe_accepts : applyPipeline wPipe wP = some wPOpt := rfl

/-- The witness run changes memory: the slot holds `5` afterwards. -/
theorem wPOpt_run :
    ∃ σ' ρ', execBlock wO 5 wR wPOpt wWorld0 Env.nil = .ok σ' ρ' ∧ (σ'.slots () 0 ()).n = 5 :=
  ⟨_, _, rfl, rfl⟩

/-- The source run changes memory in the same way (it is the same run). -/
theorem wP_run :
    ∃ σ' ρ', execBlock wO 5 wR wP wWorld0 Env.nil = .ok σ' ρ' ∧ (σ'.slots () 0 ()).n = 5 :=
  ⟨_, _, rfl, rfl⟩

/-- The slot starts at `0`: the run really changed it. -/
theorem wWorld0_slot : (wWorld0.slots () 0 ()).n = 0 := rfl

/-! ## 3. Joint witnesses for the expression layer -/

/-- An environment binding `x = 3` (range `0 .. 5`). -/
def env3 : Env wD [.int 0 5] := .cons (⟨3, by decide, by decide⟩ : Zahl 0 5) .nil

/-- Every premise of `constInt?_sound`, jointly: `2 + 3` is the constant `5`. -/
theorem constInt?_sound_zeuge :
    intOf (D := wD) (wD.typ () ()) (eval wWorld0 (five (Γ := [])) wWorld0 Env.nil) = some 5 ∧
      wV.schreibt () = true :=
  ⟨constInt?_sound (five (Γ := [])) wWorld0 wWorld0 Env.nil 5 rfl, wit_schreibt⟩

/-- Every premise of `constInt?_orte`, jointly. -/
theorem constInt?_orte_zeuge : (five (Γ := [])).orte = [] :=
  constInt?_orte (five (Γ := [])) 5 rfl

/-- Every premise of `bounds_sound`: a NON-constant operand, bounded by its type. -/
theorem bounds_sound_zeuge :
    (bounds (xVar (Γ := []))).1 ≤ (eval wWorld0 (xVar (Γ := [])) wWorld0 env3).n ∧
      (eval wWorld0 (xVar (Γ := [])) wWorld0 env3).n ≤ (bounds (xVar (Γ := []))).2 :=
  bounds_sound xVar wWorld0 wWorld0 env3

/-- Every premise of `constBool?_sound`, jointly, on a condition over a
    VARIABLE (decided by its type range, not by a literal). -/
theorem constBool?_sound_zeuge :
    boolOf (D := wD) .bool (eval wWorld0 (xCheck (Γ := [])) wWorld0 env3) = some true :=
  constBool?_sound xCheck wWorld0 wWorld0 env3 true rfl

/-- Every premise of `foldInt_sound`, jointly. -/
theorem foldInt_sound_zeuge : ExprEquiv (five (Γ := [])) (fiveLit (Γ := [])) :=
  foldInt_sound _ _ rfl

/-- Every premise of `foldBool_sound`, jointly, on the range-decided check. -/
theorem foldBool_sound_zeuge : ExprEquiv (xCheck (Γ := [])) .wahr :=
  foldBool_sound _ _ rfl

/-- Every premise of `applyExpr_sound`, jointly. -/
theorem applyExpr_sound_zeuge : ExprEquiv (five (Γ := [])) (fiveLit (Γ := [])) :=
  applyExpr_sound .foldInt _ _ _ rfl

/-- Every premise of `ExprEquiv.trans`, jointly (fold, then keep). -/
theorem ExprEquiv.trans_zeuge : ExprEquiv (five (Γ := [])) (fiveLit (Γ := [])) :=
  ExprEquiv.trans foldInt_sound_zeuge (ExprEquiv.refl _)

/-! ## 4. Strength reduction: witnesses and probes -/

/-- An operand in `0 .. 100`, bound to `7`. -/
def yVar : Expr wD [.int 0 100] [] (.int 0 100) := .var .hier

/-- The environment `y = 7`. -/
def env7 : Env wD [.int 0 100] := .cons (⟨7, by decide, by decide⟩ : Zahl 0 100) .nil

/-- `y * 8`. -/
def yMul8 := Expr.mul yVar (Expr.lit (D := wD) (Γ := [.int 0 100]) (Λ := []) 8)

/-- `y / 4`. -/
def yDiv4 := Expr.div (by decide) (by decide) yVar (Expr.lit (D := wD) (Γ := [.int 0 100]) (Λ := []) 4)

/-- `y % 16`. -/
def yRem16 := Expr.rem (by decide) (by decide) yVar (Expr.lit (D := wD) (Γ := [.int 0 100]) (Λ := []) 16)

/-- Positive probes: R1–R3 are selected with the right shift count / mask. -/
theorem strength_accepts :
    checkStrength 3 yMul8 = some (.shl 3) ∧ checkStrength 2 yDiv4 = some (.shr 2) ∧
      checkStrength 4 yRem16 = some (.mask 4) := by
  decide

/-- Every premise of `checkStrength_sound`, jointly: `7 * 8` is `shlW 7 3`. -/
theorem checkStrength_sound_zeuge :
    ∃ x, shiftedOperand wWorld0 yMul8 wWorld0 env7 = some x ∧ 0 ≤ x ∧ x < 2 ^ 64 ∧
      intOf _ (eval wWorld0 yMul8 wWorld0 env7) = some (((TargetOp.shl 3).run (encodeNat x)).toNat : Int) :=
  checkStrength_sound 3 yMul8 (.shl 3) (by decide) wWorld0 wWorld0 env7

/-- The selected word operation really computes `56` on the encoded `7`. -/
theorem strength_word_probe : ((TargetOp.shl 3).run (encodeNat 7)).toNat = 56 ∧
    ((TargetOp.shr 2).run (encodeNat 7)).toNat = 1 ∧
    ((TargetOp.mask 4).run (encodeNat 23)).toNat = 7 := by
  decide

/-- Poison: signed division is never strength-reduced (R4), whatever `k`. -/
theorem strength_refuses_sdiv :
    checkStrength 2 (.sdiv (Or.inl (by decide)) yVar (.lit 4) : Expr wD [.int 0 100] [] _) = none :=
  checkStrength_sdiv 2 _ _ _

/-- Every premise of `checkStrength_sdiv`, jointly. -/
theorem checkStrength_sdiv_zeuge :
    checkStrength 2 (.sdiv (Or.inl (by decide)) yVar (.lit 4) : Expr wD [.int 0 100] [] _) = none :=
  checkStrength_sdiv 2 _ _ _

/-- Every premise of `checkStrength_srem`, jointly. -/
theorem checkStrength_srem_zeuge :
    checkStrength 2 (.srem (Or.inl (by decide)) yVar (.lit 4) : Expr wD [.int 0 100] [] _) = none :=
  checkStrength_srem 2 _ _ _

/-- Poison: `y * 6` is not a shift (6 is not a power of two). -/
theorem strength_refuses_non_pow2 :
    checkStrength 1 (.mul yVar (.lit 6) : Expr wD [.int 0 100] [] _) = none ∧
      checkStrength 2 (.mul yVar (.lit 6) : Expr wD [.int 0 100] [] _) = none := by
  decide

/-- Poison: a possibly negative operand (`-5 .. 5`) is not shifted (R1's
    counterexample in OPTIMIZER.md §3.6). -/
theorem strength_refuses_signed_operand :
    checkStrength 3 (.mul (.var .hier) (.lit 8) : Expr wD [.int (-5) 5] [] _) = none := by
  decide

/-- Poison: an operand up to `2^62`, times `8`, may wrap 64 bits: refused. -/
theorem strength_refuses_overflow :
    checkStrength 3 (.mul (.var .hier) (.lit 8) : Expr wD [.int 0 (2 ^ 62)] [] _) = none := by
  decide

/-- Poison: the certificate's `k` must match the constant (`8` is `2^3`, not `2^2`). -/
theorem strength_refuses_wrong_k : checkStrength 2 yMul8 = none := by
  decide

/-! ## 5. Joint witnesses for the statement / block layer

    All on `wP`, whose run writes the table (`wP_run`). -/

/-- The inner block after the outer `bind` (context `x : 0 .. 5`). -/
def wInner : Block wD wV true [.int 0 5] [] [] :=
  .pruefung xCheck (.leave rfl)
    (.narrow xVar 0 10 (.leave rfl) (.cons (store (.var .hier)) (.cons (store five) .nil)))

/-- `wInner` without its check. -/
def wInnerNoCheck : Block wD wV true [.int 0 5] [] [] :=
  .narrow xVar 0 10 (.leave rfl) (.cons (store (.var .hier)) (.cons (store five) .nil))

/-- Every premise of `dropCheck_sound`, jointly: a range-decided check on a
    VARIABLE, in front of table writes. -/
theorem dropCheck_sound_zeuge : BlockEquiv wInner wInnerNoCheck :=
  dropCheck_sound xCheck (.leave rfl) _ rfl

/-- Every premise of `narrowEntailed_sound`, jointly. -/
theorem narrowEntailed_sound_zeuge :
    BlockEquiv wInnerNoCheck
      (.bind (.weiter (show (0 : Int) ≤ 0 by decide) (show (5 : Int) ≤ 10 by decide) xVar)
        (.cons (store (.var .hier)) (.cons (store five) .nil))) :=
  narrowEntailed_sound xVar 0 10 (.leave rfl) _ _ rfl

/-- Every premise of `applyStmt_sound`, jointly: fold the stored value. -/
theorem applyStmt_sound_zeuge :
    StmtEquiv (store (Γ := [.int 0 5]) five) (store fiveLit) :=
  applyStmt_sound (.assignSlotValue .foldInt) _ _ rfl

/-- Every premise of `applyBlock_sound`, jointly, through a path. -/
theorem applyBlock_sound_zeuge :
    BlockEquiv wP (.bind xVal wInnerNoCheck) :=
  applyBlock_sound (.rest .dropCheck) _ _ rfl

/-- Every premise of `BlockEquiv.trans`, jointly. -/
theorem BlockEquiv.trans_zeuge : BlockEquiv wP (.bind xVal wInnerNoCheck) :=
  BlockEquiv.trans applyBlock_sound_zeuge (BlockEquiv.refl _)

/-- Every premise of `applyOrKeep_sound`, jointly (an accepted certificate). -/
theorem applyOrKeep_sound_zeuge : BlockEquiv wP (applyOrKeep (.rest .dropCheck) wP) :=
  applyOrKeep_sound _ wP

/-- Every premise of `runCerts_sound`, jointly. -/
theorem runCerts_sound_zeuge : BlockEquiv wP wPOpt :=
  runCerts_sound wPipe wP wPOpt rfl

/-- Every premise of `applyPipeline_sound`, jointly: the whole certified
    optimisation of the table-writing program. -/
theorem applyPipeline_sound_zeuge : BlockEquiv wP wPOpt :=
  applyPipeline_sound wPipe wP wPOpt wPipe_accepts

/-- Every premise of `applyPipeline_order`, jointly. -/
theorem applyPipeline_order_zeuge : admittedOrder (wPipe.map Prod.fst) = true :=
  applyPipeline_order wPipe wP wPOpt wPipe_accepts

/-- The joint witness of the whole chain: the certified pipeline is accepted,
    the optimised program has the same outcome as the source program, and
    that outcome is a run that changed memory (slot `0` -> `5`) of a table
    the contract writes. -/
theorem pipeline_zeuge :
    applyPipeline wPipe wP = some wPOpt ∧
      execBlock wO 5 wR wPOpt wWorld0 Env.nil = execBlock wO 5 wR wP wWorld0 Env.nil ∧
      (∃ σ' ρ', execBlock wO 5 wR wP wWorld0 Env.nil = .ok σ' ρ' ∧
        (σ'.slots () 0 ()).n = 5 ∧ (wWorld0.slots () 0 ()).n = 0) ∧
      wV.schreibt () = true := by
  refine ⟨wPipe_accepts, applyPipeline_sound_zeuge wO 5 wR wWorld0 Env.nil, ?_, wit_schreibt⟩
  obtain ⟨σ', ρ', h, h5⟩ := wP_run
  exact ⟨σ', ρ', h, h5, wWorld0_slot⟩

/-! ## 6. Poison probes for the block layer and the pipeline (§10.2) -/

/-- A slot read in `0 .. 10`. -/
def slotRead : Expr wD [] [] (wD.typ () ()) :=
  .slot () () (idx []) (fun _ hw => False.elim (List.not_mem_nil hw))

/-- Poison: `slot <= 100` is decided `true` by the slot's TYPE range, yet the
    fold is refused, because it would delete the read event of the slot. -/
theorem foldBool_refuses_read :
    constBool? (Expr.le slotRead (.lit 100)) = some true ∧
      foldBool (Expr.le slotRead (.lit 100)) = none := by
  decide

/-- Poison: the same read-bearing check is not dropped. -/
theorem dropCheck_refuses_read :
    applyBlock .dropCheck
      (.pruefung (Expr.le slotRead (.lit 100)) (.leave rfl) .nil : Block wD wV true [] [] []) = none := by
  decide

/-- Poison: an undecided check (`x <= 3` with `x` in `0 .. 5`) stays. -/
theorem dropCheck_refuses_undecided :
    applyBlock .dropCheck
      (.pruefung (.le xVar (.lit 3)) (.leave rfl) .nil : Block wD wV true [.int 0 5] [] []) = none := by
  decide

/-- Poison: a check decided FALSE is not removed -- it always fails and its
    `else` is the behaviour. -/
theorem dropCheck_refuses_false :
    applyBlock .dropCheck
      (.pruefung (.le (.lit 5) (.lit 2)) (.leave rfl) .nil : Block wD wV true [] [] []) = none := by
  decide

/-- Poison: `narrow x to 0 .. 3` with `x` in `0 .. 5` is not entailed. -/
theorem narrow_refuses_unentailed :
    applyBlock .narrowEntailed
      (.narrow xVar 0 3 (.leave rfl) .nil : Block wD wV true [.int 0 5] [] []) = none := by
  decide

/-- Poison: an integer fold on a non-constant operand is refused. -/
theorem foldInt_refuses_variable : foldInt (xVar (Γ := [])) = none := by
  decide

/-- Poison: a rule at the wrong type is refused, not coerced. -/
theorem applyExpr_refuses_wrong_type :
    applyExpr .foldInt .bool (xCheck (Γ := [])) = none ∧
      applyExpr .foldBool _ (five (Γ := [])) = none := by
  decide

/-- Poison: a float comparison has no rule (F2–F4 refused by absence). -/
theorem constBool_refuses_float {Γ : Ctx} (a b : Expr wD Γ [] (.fl (1, 1) (2, 1))) :
    constBool? (Expr.fllt a b) = none ∧ constBool? (Expr.flle a b) = none :=
  ⟨rfl, rfl⟩

/-- Poison: a certificate path into the wrong shape is refused. -/
theorem applyBlock_refuses_bad_path : applyBlock .dropCheck wP = none := by
  decide

/-- Poison: the same certificates out of order (checks before fold). -/
theorem pipeline_refuses_order :
    applyPipeline [(.checks, cDrop), (.fold, cFold), (.checks, cNarrow)] wP = none := by
  decide

/-- Poison: a fold certificate filed under the check-removal pass. -/
theorem pipeline_refuses_mislabel :
    applyPipeline [(.checks, cFold)] wP = none := by
  decide

/-- The conservative route on a refused certificate is the input itself. -/
theorem applyOrKeep_refused_keeps : applyOrKeep .dropCheck wP = wP := rfl

/- CUTS:
   - The witnesses run single-thread `execBlock` on one declaration with one
     table (`InvariantenOpt.wD`); they show the premises of every rule are
     jointly satisfiable on a table-writing program with a memory-changing
     run, not that any rule covers a concurrent run beyond what exact
     `Ausgang` equality states.
   - The poison probes are the refusals the rules file claims (§10.2); they
     do not exhaust every wrong certificate (stale SSA versions, dropped
     ghost events, weakened orderings and atomic rereads belong to rules
     that need the shared IR and do not exist yet).
   - `strength_word_probe` checks the canonical word helpers on concrete
     values; no encoded instruction byte is involved.
-/

#print axioms wPipe_accepts
#print axioms wPOpt_run
#print axioms wP_run
#print axioms wWorld0_slot
#print axioms constInt?_sound_zeuge
#print axioms constInt?_orte_zeuge
#print axioms bounds_sound_zeuge
#print axioms constBool?_sound_zeuge
#print axioms foldInt_sound_zeuge
#print axioms foldBool_sound_zeuge
#print axioms applyExpr_sound_zeuge
#print axioms ExprEquiv.trans_zeuge
#print axioms strength_accepts
#print axioms checkStrength_sound_zeuge
#print axioms strength_word_probe
#print axioms strength_refuses_sdiv
#print axioms checkStrength_sdiv_zeuge
#print axioms checkStrength_srem_zeuge
#print axioms strength_refuses_non_pow2
#print axioms strength_refuses_signed_operand
#print axioms strength_refuses_overflow
#print axioms strength_refuses_wrong_k
#print axioms dropCheck_sound_zeuge
#print axioms narrowEntailed_sound_zeuge
#print axioms applyStmt_sound_zeuge
#print axioms applyBlock_sound_zeuge
#print axioms BlockEquiv.trans_zeuge
#print axioms applyOrKeep_sound_zeuge
#print axioms runCerts_sound_zeuge
#print axioms applyPipeline_sound_zeuge
#print axioms applyPipeline_order_zeuge
#print axioms pipeline_zeuge
#print axioms foldBool_refuses_read
#print axioms dropCheck_refuses_read
#print axioms dropCheck_refuses_undecided
#print axioms dropCheck_refuses_false
#print axioms narrow_refuses_unentailed
#print axioms foldInt_refuses_variable
#print axioms applyExpr_refuses_wrong_type
#print axioms constBool_refuses_float
#print axioms applyBlock_refuses_bad_path
#print axioms pipeline_refuses_order
#print axioms pipeline_refuses_mislabel
#print axioms applyOrKeep_refused_keeps

end Gabbro.Grammatik.X86.OptimizationWitnesses
