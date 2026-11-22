module

public import Stage0.Senke.Bild.Ruf.IdleLowering
import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheStatisch.T1.Teil1Basis

@[expose] public section

namespace Gabbro.Stage0.Senke

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D}

private theorem counterDepthS_cast {l : Bool} {Γ : Ctx} {Λ Λ₁ Λ₂ : List (Res D)}
    (h : Λ₁ = Λ₂) (s : Stmt D V l Γ Λ Λ₁) :
    counterDepthS (Stmt.nachΛ h s) = counterDepthS s := by
  cases h
  rfl

private theorem counterDepthB_cast {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ Λ' : List (Res D)}
    (h : Λ₁ = Λ₂) (b : Block D V l Γ Λ₁ Λ') :
    counterDepthB (Block.vorΛ h b) = counterDepthB b := by
  cases h
  rfl

private theorem counterDepthE_cast {l : Bool} {Γ : Ctx} {Λ₁ Λ₂ : List (Res D)}
    (h : Λ₁ = Λ₂) (e : Endblock D V l Γ Λ₁) :
    counterDepthE (e.umΛ h) = counterDepthE e := by
  cases h
  rfl

mutual

private theorem counterDepthS_ru : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (s : Stmt D V l Γ Λ Λ'), counterDepthS (ruS s) = counterDepthS s
  | _, _, _, _, .ite _ yes no | _, _, _, _, .onOption _ yes no =>
    kongr₂ max (counterDepthB_ru yes) (counterDepthB_ru no)
  | _, _, _, _, .onTag _ arms => counterDepthA_ru arms
  | _, _, _, _, .onWhy _ arms => counterDepthG_ru arms
  | _, _, _, _, .locks _ _ body | _, _, _, _, .breaking _ body
  | _, _, _, _, .traverse _ _ body => counterDepthB_ru body
  | _, _, _, _, .retry _ _ body fallback =>
    kongr₂ (fun b f : Nat => max (1 + b) f) (counterDepthB_ru body) (counterDepthB_ru fallback)
  | _, _, _, _, .forever _ _ body | _, _, _, _, .consumeTraverse _ _ _ _ _ _ body =>
    congrArg (1 + ·) (counterDepthB_ru body)
  | _, _, _, _, .call .. | _, _, _, _, .callInd ..
  | _, _, _, _, .advances .. | _, _, _, _, .retires .. =>
    counterDepthS_cast _ _
  | _, _, _, _, .callIndElse _ _ _ _ _ err | _, _, _, _, .axiomCallElse _ _ _ _ _ _ _ _ err =>
    (counterDepthS_cast _ _).trans ((counterDepthE_cast _ _).trans (counterDepthE_ru err))
  | _, _, _, _, .assignSlot .. | _, _, _, _, .assignThru .. | _, _, _, _, .assignThruOwn ..
  | _, _, _, _, .assignSlotRef .. | _, _, _, _, .assignGlob .. | _, _, _, _, .putBytes ..
  | _, _, _, _, .assignVar .. | _, _, _, _, .shift .. | _, _, _, _, .axiomCall ..
  | _, _, _, _, .regWrite .. | _, _, _, _, .transition .. | _, _, _, _, .publish ..
  | _, _, _, _, .ret .. | _, _, _, _, .retWhy .. | _, _, _, _, .leave ..
  | _, _, _, _, .next .. | _, _, _, _, .retScoped .. | _, _, _, _, .retWhyScoped .. => rfl

private theorem counterDepthB_ru : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    (b : Block D V l Γ Λ Λ'), counterDepthB (ruB b) = counterDepthB b
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons s rest => kongr₂ max (counterDepthS_ru s) (counterDepthB_ru rest)
  | _, _, _, _, .bind _ rest | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest
  | _, _, _, _, .regRead _ _ rest | _, _, _, _, .awaits _ _ _ _ _ rest
  | _, _, _, _, .exchange _ _ _ _ rest | _, _, _, _, .narrowRequired _ _ _ rest
  | _, _, _, _, .float _ _ _ _ _ rest | _, _, _, _, .floatLit _ _ _ rest
  | _, _, _, _, .floatOf _ _ _ rest => counterDepthB_ru rest
  | _, _, _, _, .bindCall _ _ _ _ _ rest | _, _, _, _, .bindCallInd _ _ _ _ _ rest
  | _, _, _, _, .bindAxiomOpt none _ _ _ _ _ _ rest
  | _, _, _, _, .bindAxiomOpt (some _) _ _ _ _ _ _ rest =>
    (counterDepthB_cast _ _).trans (counterDepthB_ru rest)
  | _, _, _, _, .bindCallElse _ _ _ _ _ err rest | _, _, _, _, .bindCallIndElse _ _ _ _ _ err rest
  | _, _, _, _, .bindAxiomOptElse none _ _ _ _ _ _ _ err rest
  | _, _, _, _, .bindAxiomOptElse (some _) _ _ _ _ _ _ _ err rest =>
    kongr₂ max ((counterDepthE_cast _ _).trans (counterDepthE_ru err))
      ((counterDepthB_cast _ _).trans (counterDepthB_ru rest))
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest | _, _, _, _, .regReadElse _ _ _ err rest
  | _, _, _, _, .narrow _ _ _ err rest | _, _, _, _, .check _ err rest
  | _, _, _, _, .floatNarrow _ _ _ err rest =>
    kongr₂ max (counterDepthE_ru err) (counterDepthB_ru rest)

/-- The exact live counter nesting depends only on control structure.
    Function and resource index transport keeps its assigned stack space. -/
theorem counterDepthE_ru : ∀ {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ), counterDepthE (ruEnd e) = counterDepthE e
  | _, _, _, .ret .. | _, _, _, .retWhy .. | _, _, _, .leave .. | _, _, _, .next ..
  | _, _, _, .retScoped .. | _, _, _, .retWhyScoped .. => rfl
  | _, _, _, .cons s rest => kongr₂ max (counterDepthS_ru s) (counterDepthE_ru rest)
  | _, _, _, .bind _ rest | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest
  | _, _, _, .regRead _ _ rest | _, _, _, .awaits _ _ _ _ _ rest
  | _, _, _, .narrowRequired _ _ _ rest | _, _, _, .exchange _ _ _ _ rest
  | _, _, _, .float _ _ _ _ _ rest | _, _, _, .floatLit _ _ _ rest
  | _, _, _, .floatOf _ _ _ rest => counterDepthE_ru rest
  | _, _, _, .bindCall _ _ _ _ _ rest | _, _, _, .bindCallInd _ _ _ _ _ rest
  | _, _, _, .bindAxiomOpt none _ _ _ _ _ _ rest
  | _, _, _, .bindAxiomOpt (some _) _ _ _ _ _ _ rest =>
    (counterDepthE_cast _ _).trans (counterDepthE_ru rest)
  | _, _, _, .bindCallElse _ _ _ _ _ err rest | _, _, _, .bindCallIndElse _ _ _ _ _ err rest
  | _, _, _, .bindAxiomOptElse none _ _ _ _ _ _ _ err rest
  | _, _, _, .bindAxiomOptElse (some _) _ _ _ _ _ _ _ err rest =>
    kongr₂ max ((counterDepthE_cast _ _).trans (counterDepthE_ru err))
      ((counterDepthE_cast _ _).trans (counterDepthE_ru rest))
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest | _, _, _, .regReadElse _ _ _ err rest
  | _, _, _, .narrow _ _ _ err rest | _, _, _, .floatNarrow _ _ _ err rest =>
    kongr₂ max (counterDepthE_ru err) (counterDepthE_ru rest)
  | _, _, _, .ite _ yes no => kongr₂ max (counterDepthE_ru no) (counterDepthE_ru yes)

private theorem counterDepthA_ru : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option Ty)} (a : Arms D V l Γ Λ Λ' cs),
    counterDepthA (ruArms a) = counterDepthA a
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons (c := none) b rest | _, _, _, _, _, .cons (c := some _) b rest =>
    kongr₂ max (counterDepthB_ru b) (counterDepthA_ru rest)

private theorem counterDepthG_ru : ∀ {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {n : Nat} (a : GrundArms D V l Γ Λ Λ' n),
    counterDepthG (ruGArms a) = counterDepthG a
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => kongr₂ max (counterDepthB_ru b) (counterDepthG_ru rest)
end

theorem functionCounterDepth_withIdle (P : Programm D) (f : D.Fn) :
    (functionFrame P.mitRuhe (some f)).counterDepth = (functionFrame P f).counterDepth :=
  (counterDepthE_cast _ _).trans (counterDepthE_ru (P.rumpf f))

/-- The function retains all layout inputs except the nominal type labels. -/
theorem functionFrame_withIdle (P : Programm D) (L : Lay D) (f : D.Fn) :
    functionFrame P.mitRuhe (some f) =
      { functionFrame P f with
        params := (D.params f).map tyR
        result := (D.erg f).map tyR } := by
  have snapshots := (postSnapshots_withIdle P L f FB).1
  have counters := functionCounterDepth_withIdle P f
  change
    { params := (D.params f).map tyR, result := (D.erg f).map tyR, reasons := D.gruende f,
      snapshotWords := EntrySnapshots.words (oldCells (P.mitRuhe.ensures (some f))),
      counterDepth := counterDepthE (P.mitRuhe.rumpf (some f)) } =
    { params := (D.params f).map tyR, result := (D.erg f).map tyR, reasons := D.gruende f,
      snapshotWords := EntrySnapshots.words (oldCells (P.ensures f)),
      counterDepth := counterDepthE (P.rumpf f) }
  exact kongr₂ (FrameLayout.mk ((D.params f).map tyR) ((D.erg f).map tyR) (D.gruende f))
    snapshots counters

/-- Every physical offset used by the function prologue and its return
    protocol is independent of the logical function-number shift. -/
theorem functionFrame_offsets_withIdle (P : Programm D) (L : Lay D) (f : D.Fn) :
    let shifted := functionFrame P.mitRuhe (some f)
    let original := functionFrame P f
    shifted.parameterWords = original.parameterWords ∧
      shifted.returnSpan = original.returnSpan ∧ shifted.ensReserved = original.ensReserved ∧
      shifted.canonicalResult = original.canonicalResult ∧ shifted.internalResult = original.internalResult ∧
      shifted.internalStatus = original.internalStatus ∧ shifted.bodyReserved = original.bodyReserved := by
  dsimp only
  rw [functionFrame_withIdle P L f]
  simp only [FrameLayout.parameterWords, FrameLayout.returnSpan, FrameLayout.ensReserved,
    FrameLayout.canonicalResult, FrameLayout.internalResult, FrameLayout.ensParams,
    FrameLayout.internalStatus, FrameLayout.bodyReserved, functionFrame, tyR,
    contextWords_mapNumbers, returnWords_mapNumbers, and_self]

end Gabbro.Stage0.Senke
