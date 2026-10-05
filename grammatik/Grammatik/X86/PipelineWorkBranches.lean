/-
  File:      Grammatik/X86/PipelineWorkBranches.lean
  Subject:   Pipeline work bounds for branches and loops (lane 1233).

  Follow-up of lane 1165 (`PipelineWork.lean`: shallow assignment chunks
  only). Worst-case retired-instruction bounds for if/else (max of the
  branches plus the compare/jump, over the accepted `iteCode` shape of
  `Pipeline.lean`) and for bounded loops (the source iteration budget
  transfers to the target step budget `schleifeSchritte` of
  `PipelineLoops.lean`); unbounded loops (`retry`/`forever` at the
  `senkBlock` level) stay refused. A small validator (`pruefeZweig`)
  recomputes the bound from the lowered list, and the main correctness
  theorem is in the style of `pipeline_arbeit_korrekt` (source
  `execBlock` related to the fetched-byte run, plus retired-work and
  named-time bounds). Reused unchanged: `senkBlock`/`senkBlock_korrektC`/
  `iteCode`/`Entspricht`/`CodeAt`, `pipeSummary`/`pipeSummary_expand`,
  `decodiertZu`/`arbeit_decodiert`, `Deckung`/
  `budgetAusfuehrung_transfer`, `schleifeSchritte`, the `pd`/`pw`
  witness packages. No second IR, no second interpreter, no optimiser
  edit. Rust is out of scope.
-/
import Grammatik.X86.Pipeline
import Grammatik.X86.PipelineWork
import Grammatik.X86.PipelineLoops
import Grammatik.X86.PipelineImageWitnesses
import Grammatik.X86.BudgetExecution
import Grammatik.X86.DerivedWorkBound
import Grammatik.X86.HardwareAssumptions

namespace Gabbro.Grammatik.X86.PipeWorkBranches

open Gabbro.Grammatik
open Gabbro.Grammatik.X86
open Gabbro.Grammatik.X86.Pipeline
open Gabbro.Grammatik.X86.PipelineWitnesses
open Gabbro.Grammatik.X86.PipelineWork
open Gabbro.Grammatik.X86.PipelineLoops
open Gabbro.Grammatik.X86.PipelineImageWitnesses

variable {D : Deklaration} {V : Vertrag D}

/-! ## 1. Branch worst-case bound over the accepted `iteCode` shape. -/

/-- Worst-case retired instructions of an if/else: the compare code,
    one taken jump, the LONGER branch, one end jump. -/
def iteSchranke (codeLen tLen eLen : Nat) : Nat :=
  codeLen + 1 + Nat.max tLen eLen + 1

/-- Static length of the accepted ite code shape (both branches). -/
theorem iteCode_laenge (code : List Befehl) (j : Bedingung) (pt pe : List Befehl) :
    (iteCode code j pt pe).length = code.length + 1 + pt.length + 1 + pe.length := by
  simp [iteCode]
  omega

/-- DYNAMIC PATH BOUND: whichever branch the jump takes, the retired
    instructions of the ite (compare code, taken jump, taken branch,
    end jump) are at most the worst case over the longer branch. -/
theorem itePfad_schranke (genommen : Bool) (codeLen tLen eLen : Nat) :
    (if genommen then codeLen + 1 + eLen + 1 else codeLen + 1 + tLen + 1) ≤
      iteSchranke codeLen tLen eLen := by
  unfold iteSchranke
  cases genommen with
  | true =>
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.le_max_right _ _) _) _
  | false =>
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.le_max_left _ _) _) _

/-! ## 2. Validator: recompute the bound from the lowered list. -/

/-- The branch validator: the lowered list fits the source budget scaled
    by the admitted summary maximum. Decided by computation, never a
    premise. -/
def pruefeZweig (prog : List Befehl) (src : Nat) : Bool :=
  decide (prog.length ≤ src * 6)

/-- COVERAGE FROM LENGTH: a lowered list within the scaled budget is
    covered by the admitted pipeline summary. `Deckung` is DERIVED,
    never assumed. -/
theorem deckung_von_laenge (prog : List Befehl) (src : Nat)
    (h : prog.length ≤ src * 6) : Deckung pipeSummary src (decodiertZu prog) := by
  intro k hk
  rw [pipeSummary_expand] at hk
  cases hk
  rw [arbeit_decodiert]
  exact h

/-- VALIDATOR CORRECTNESS: an accepted list is covered. Every premise
    is used: `h` feeds the derived coverage. -/
theorem pruefeZweig_korrekt (prog : List Befehl) (src : Nat)
    (h : pruefeZweig prog src = true) :
    Deckung pipeSummary src (decodiertZu prog) := by
  unfold pruefeZweig at h
  simp only [decide_eq_true_eq] at h
  exact deckung_von_laenge prog src h

/-- BRANCH COVERAGE: a lowered ite whose static whole-list length fits
    the scaled budget is covered. The static length counts BOTH
    branches; the retired path (`itePfad_schranke`) is only smaller.
    Every premise is used: the lists feed the shape in `h` and the
    conclusion. -/
theorem deckung_ite (code : List Befehl) (j : Bedingung) (pt pe : List Befehl)
    (src : Nat) (h : (iteCode code j pt pe).length ≤ src * 6) :
    Deckung pipeSummary src (decodiertZu (iteCode code j pt pe)) :=
  deckung_von_laenge _ _ h

/-! ## 3. Work/time correctness over validated programs.

    In the style of `pipeline_arbeit_korrekt`: the source `execBlock`
    result is related to the fetched-byte run on the loaded image
    (`senkBlock_korrektC`, reused as a black box -- no second
    interpreter), and the validated bytes carry retired-work and
    named-time bounds through the validator-derived coverage (never
    an assumed `Deckung`). Every premise is used. -/

/-- BRANCH WORK CORRECTNESS: a validated program runs from the loaded
    image with world and environment represented, and retired work
    and named time are bounded over the source budget. -/
theorem zweig_arbeit_korrekt (c : PipeCfg) (L : Layout D)
    (hc : cfgOk c = true) (hsep : LayoutSep L)
    (O : Orakel D) (passes : Nat)
    (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
    (flat : List Byte)
    {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ') (pre post : List Byte) (prog : List Befehl)
    (h : senkBlock c L pre.length b = some prog)
    (σ : World D) (ρ : Env D Γ) (s : Zustand)
    (hcode : Pipeline.CodeAt s.speicher (natAdresse c.codeBase) flat)
    (hf : flat = pre ++ encodeAll prog ++ post)
    (hrip : s.rip = addrOff (natAdresse c.codeBase) pre.length)
    (hW : WorldRep L s.speicher σ) (hE : EnvRepr ρ s.register (abbOf c))
    (prof : HardwareProfil) (srcB B tt k : Nat)
    (hval : pruefeZweig prog srcB = true)
    (hCost : laufKosten prof (decodiertZu prog) = some tt)
    (hb : ∀ dd ∈ decodiertZu prog,
      ∃ cc, schrittKosten prof dd = some cc ∧ cc ≤ B)
    (hk : expandBound pipeSummary srcB = some k) :
    (∃ n s', laufBytes n s = .weiter s' ∧
      Pipeline.CodeAt s'.speicher (natAdresse c.codeBase) flat ∧
      Entspricht c L (addrOff (natAdresse c.codeBase) (pre.length + (encodeAll prog).length))
        (execBlock O passes R b σ ρ) s') ∧
    targetWork prog ≤ k ∧ tt ≤ B * k := by
  have hrun := senkBlock_korrektC c L hc hsep O passes R flat b pre post prog h σ ρ s
    hcode hf hrip hW hE
  have hDeck := pruefeZweig_korrekt prog srcB hval
  have hwork := hDeck k hk
  rw [arbeit_decodiert] at hwork
  have htime := budgetAusfuehrung_transfer pipeSummary prof (decodiertZu prog) srcB B tt
    hCost hb hDeck k hk
  exact ⟨hrun, hwork, htime⟩

/-! ## 4. Bounded loops: source iteration budget to target step budget.

    The target step budget is the accepted `schleifeSchritte` of
    `PipelineLoops.lean` (one source round costs at most `m + 2`
    labelled steps, the final exit check one more); a source run that
    finishes within `n'` rounds with `n' ≤ n` fits the budget for `n`.
    Unbounded loops (`retry`, `forever`) have no `senkBlock` lowering
    at all: refused, never guessed. -/

/-- BUDGET TRANSFER: fewer source rounds need fewer target steps, so a
    source iteration budget covers every run finishing inside it. Both
    premises are used. -/
theorem schleife_budget_transfer (n n' m : Nat) (h : n' ≤ n) :
    schleifeSchritte n' m ≤ schleifeSchritte n m := by
  unfold schleifeSchritte
  exact Nat.add_le_add_right (Nat.mul_le_mul_right (m + 2) h) 1

/-- UNBOUNDED-LOOP REFUSAL (`retry`, every bound): a `retry` head has
    no `senkBlock` lowering at any bound -- refused, never guessed.
    (PipeBlock proves the bound-5 instance; this is the generic
    statement over the same catch-all arm.) -/
theorem senkBlock_verweigert_retry (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (n : Nat) (bis : Expr D Γ Λ .bool)
    (body : _root_.Gabbro.Grammatik.Block D V true Γ Λ Λ)
    (ueber : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ)
    (rest : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ'') (pos : Nat) :
    senkBlock c L pos
      (_root_.Gabbro.Grammatik.Block.cons (Stmt.retry n bis body ueber) rest) =
      none := rfl

/-- UNBOUNDED-LOOP REFUSAL (`forever`): an unbounded loop head has no
    `senkBlock` lowering -- refused, never guessed. -/
theorem senkBlock_verweigert_forever (c : PipeCfg) (L : Layout D)
    {l : Bool} {Γ : Ctx} {Λ Λ'' : List (Res D)}
    (a : D.Annahme) (inv : Expr D Γ Λ .bool)
    (body : _root_.Gabbro.Grammatik.Block D V true Γ Λ Λ)
    (rest : _root_.Gabbro.Grammatik.Block D V l Γ Λ Λ'') (pos : Nat) :
    senkBlock c L pos
      (_root_.Gabbro.Grammatik.Block.cons (Stmt.forever a inv body) rest) =
      none := rfl

/- CUTS (skeleton):
    - Proved here: `iteCode_laenge`.
    - OPEN: everything else of the task (validator, main theorem,
      loop transfer, refusals, witnesses).
-/

#print axioms iteCode_laenge

end Gabbro.Grammatik.X86.PipeWorkBranches
