module
public import Grammatik.Parser.Elab.UebersetzeAllg3.FunctionResults
import all Grammatik.Parser.Elab.UebersetzeAllg2.Teil2
import all Grammatik.Parser.Elab.UebersetzeAllg2.Teil3
import all Grammatik.Parser.Elab.UebersetzeAllg2.Teil4
import all Grammatik.Parser.Elab.UebersetzeAllg3.Body
import all Grammatik.Parser.Elab.UebersetzeAllg3.Returns

@[expose] public section
namespace Gabbro.Grammatik.Parser.UebersetzeProben11
open Gabbro.Grammatik Gabbro.Grammatik.Parser Gabbro.Grammatik.Parser.Uebersetze
open Gabbro.Grammatik.Parser.UebersetzeAllg Gabbro.Grammatik.Parser.UebersetzeAllg2
set_option maxRecDepth 100000

private abbrev BodyStep (u : UProg) (f : Fin u.fns.length) (Λ : List (Res (declOf u))) :=
  Σ after, Stmt (declOf u) (verOf u f) false (ctxOf u f) Λ after

private theorem call_prefix (u : UProg) (f : Fin u.fns.length) (fn : UFn) (n : Nat)
    (Λ : List (Res (declOf u))) (name : String) (args : List UArg) (rest : List UStmt) (ret : URet)
    (step : BodyStep u f Λ) (made : lowStmtL u f (ctxOf u f) fn Λ (.call name args) = .ok step) :
    lowBodyF u f (ctxOf u f) fn (n + 1) Λ (.call name args :: rest) ret =
      (lowBodyF u f (ctxOf u f) fn n step.1 rest ret).map (Endblock.cons step.2) := by
  rcases step with ⟨after, statement⟩
  rw [lowBodyF, made] <;> simp
  cases lowBodyF u f (ctxOf u f) fn n after rest ret <;> rfl

private theorem retire_prefix (u : UProg) (f : Fin u.fns.length) (fn : UFn) (n : Nat)
    (Λ : List (Res (declOf u))) (name : String) (rest : List UStmt) (ret : URet)
    (step : BodyStep u f Λ) (made : lowStmtL u f (ctxOf u f) fn Λ (.retires name) = .ok step) :
    lowBodyF u f (ctxOf u f) fn (n + 1) Λ (.retires name :: rest) ret =
      (lowBodyF u f (ctxOf u f) fn n step.1 rest ret).map (Endblock.cons step.2) := by
  rcases step with ⟨after, statement⟩
  rw [lowBodyF, made] <;> simp
  cases lowBodyF u f (ctxOf u f) fn n after rest ret <;> rfl

private theorem call_body (u : UProg) (f : Fin u.fns.length) (name : String) (args : List UArg)
    (shape : (fnAt u f).body = [.call name args]) (step : BodyStep u f (resOf u f))
    (made : lowStmtL u f (ctxOf u f) (fnAt u f) (resOf u f) (.call name args) = .ok step) :
    lowBody u f (fnAt u f).body (fnAt u f).ret =
      (lowEnd u f (ctxOf u f) step.1 (fnAt u f) (fnAt u f).ret).map (Endblock.cons step.2) := by
  unfold lowBody
  rw [shape]
  dsimp only [List.length_cons, List.length_nil]
  rw [call_prefix u f (fnAt u f) 1 _ _ _ _ _ step made] <;> rfl

private theorem retire_body (u : UProg) (f : Fin u.fns.length) (name : String)
    (shape : (fnAt u f).body = [.retires name]) (step : BodyStep u f (resOf u f))
    (made : lowStmtL u f (ctxOf u f) (fnAt u f) (resOf u f) (.retires name) = .ok step) :
    lowBody u f (fnAt u f).body (fnAt u f).ret =
      (lowEnd u f (ctxOf u f) step.1 (fnAt u f) (fnAt u f).ret).map (Endblock.cons step.2) := by
  unfold lowBody
  rw [shape]
  dsimp only [List.length_cons, List.length_nil]
  rw [retire_prefix u f (fnAt u f) 1 _ _ _ _ step made] <;> rfl

private theorem repeated_body (u : UProg) (f : Fin u.fns.length) (a b error : String)
    (shape : (fnAt u f).body = [.retires a, .retires b]) (step : BodyStep u f (resOf u f))
    (made : lowStmtL u f (ctxOf u f) (fnAt u f) (resOf u f) (.retires a) = .ok step)
    (failed : lowStmtL (l := false) u f (ctxOf u f) (fnAt u f) step.1 (.retires b) = .error error) :
    lowBody u f (fnAt u f).body (fnAt u f).ret = .error error := by
  unfold lowBody
  rw [shape]
  dsimp only [List.length_cons, List.length_nil]
  rw [retire_prefix u f (fnAt u f) 2 _ _ _ _ step made, lowBodyF, failed] <;> simp
  rfl

-- Assemble exactly the existing retirement constructor from separately checked
-- name, loan and held-stage facts; do not normalize a whole dependent result.
private def retire_step (u : UProg) (f : Fin u.fns.length) (name : String)
    (m : Fin u.marken.length) (a : Nat)
    (hb : (fnAt u f).leiht.any (strEq · name) = false)
    (hm : markFin u.marken name = some m) (hs : heldMarkStage (D := declOf u) m (resOf u f) = some a) :
    { actual : BodyStep u f (resOf u f) //
      lowStmtL (l := false) u f (ctxOf u f) (fnAt u f) (resOf u f) (.retires name) = .ok actual } := by
  refine ⟨⟨(resOf u f).erase (.marke m a), Stmt.retires (D := declOf u) (V := verOf u f)
    (l := false) (Γ := ctxOf u f) (Λ := resOf u f) m a (heldMarkStage_mem (D := declOf u) m _ a hs) none⟩, ?_⟩
  exact lowRetiresL_exact (l := false) u f (ctxOf u f) (resOf u f) name m a hb hm hs

-- These are precisely the seven gates of the canonical direct-call head.
private structure CallGates (u : UProg) (caller callee : Fin u.fns.length)
    (Λ : List (Res (declOf u))) : Prop where
  writes : ∀ t : Fin u.tabs.length, writesAt u (fnAt u callee) t = true → writesAt u (fnAt u caller) t = true
  globals : ∀ g : Fin u.globs.length, writesGAt u (fnAt u callee) g = true → writesGAt u (fnAt u caller) g = true
  held : ∀ L ∈ ((declOf u).signatur callee).haelt, Res.held (D := declOf u) L ∈ Λ
  floor : floorLeB u caller callee = true
  extra : ∀ L ∈ heldLocksD u Λ, L ∈ ((declOf u).signatur callee).haelt ∨ floorUeberB u callee L = true
  inventory : decide (Untermulti (((declOf u).signatur callee).inputMarks.map (Res.vonMarke (declOf u))) Λ) = true
  owners : ownerReadyB u ((declOf u).signatur callee) = true

-- Resolve the complete existing producer before specializing its dependent fields.
private def call_head (u : UProg) (f callee : Fin u.fns.length) (name : String) (raw : List UArg)
    (found : fnIdx u.fns name = .ok callee)
    (arguments : { actual : Args (declOf u) (ctxOf u f) (resOf u f) ((declOf u).params callee) //
      lowCallArgsAuxL u f (ctxOf u f) (fnAt u f) (resOf u f) (fnAt u callee).kinds
        ((declOf u).params callee) raw = .ok actual })
    (gates : CallGates u f callee (resOf u f)) :
    { actual : RufKopf u f (ctxOf u f) (resOf u f) //
      lowRufKopf u f (ctxOf u f) (fnAt u f) (resOf u f) name raw = .ok actual } := by
  refine ⟨?_, by
    erw [lowRufKopf, found]
    dsimp only
    erw [arguments.property]
    dsimp only
    erw [dif_pos gates.writes, dif_pos gates.globals,
      dif_pos gates.held, dif_pos gates.floor, dif_pos gates.extra,
      dif_pos gates.inventory, dif_pos gates.owners] <;> exact Eq.refl _⟩

private def call_step (u : UProg) (f : Fin u.fns.length) (name : String) (raw : List UArg)
    (head : { actual : RufKopf u f (ctxOf u f) (resOf u f) //
      lowRufKopf u f (ctxOf u f) (fnAt u f) (resOf u f) name raw = .ok actual })
    (reason : (declOf u).gruende head.val.callee = 0) :
    { actual : BodyStep u f (resOf u f) //
      lowStmtL (l := false) u f (ctxOf u f) (fnAt u f) (resOf u f) (.call name raw) = .ok actual } := by
  rcases head with ⟨actual, made⟩
  refine ⟨⟨nach (declOf u) actual.callee (resOf u f),
    Stmt.call (D := declOf u) (V := verOf u f) (l := false) (Γ := ctxOf u f)
      actual.callee actual.args actual.hp reason⟩, ?_⟩
  change lowCallL (l := false) u f (ctxOf u f) (fnAt u f) (resOf u f) name raw = _
  erw [lowCallL, made]
  dsimp only
  rw [dif_pos reason]

end Gabbro.Grammatik.Parser.UebersetzeProben11
