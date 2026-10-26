/-
  File:      Grammatik/Gen/Abdeckung/Satz/MerkmalGOk.lean
  Subject:   the fragment test `gOk` is an `mE` over the indirect calls (part of step 1, `ZellenSatz.lean`).
-/
import Grammatik.Gen.Abdeckung.Satz.MerkmalZerlegt

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

variable {D : Deklaration} [Aufz D] [Zahlen]

set_option linter.unusedSectionVars false

/-! ## Component 0: the fragment is an `mE` over the indirect calls -/

/-- The feature set that checks only the signatures of indirect calls. -/
def indMerkmal (K : Nat → Bool) : Merkmal D := ⟨fun _ => true, K, fun _ => true⟩

mutual

theorem sGOk (K : Nat → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (s : Stmt D V l Γ Λ Λ') → s.gOk K (fun _ => true) = mS (indMerkmal K) s
  | .ite _ t e => by simp only [Stmt.gOk, mS, bGOk K t, bGOk K e]
  | .onOption _ p a => by simp only [Stmt.gOk, mS, bGOk K p, bGOk K a]
  | .onTag _ arms => by simp only [Stmt.gOk, mS, aGOk K arms]
  | .onWhy _ arms => by simp only [Stmt.gOk, mS, gaGOk K arms]
  | .call .. => rfl
  | .callInd .. => rfl
  | .locks _ _ body => by simp only [Stmt.gOk, mS, bGOk K body]; rfl
  | .breaking _ body => by simp only [Stmt.gOk, mS, bGOk K body]
  | .traverse _ _ body => by simp only [Stmt.gOk, mS, bGOk K body]
  | .retry _ _ body ueber => by simp only [Stmt.gOk, mS, bGOk K body, bGOk K ueber]
  | .forever _ _ body => by simp only [Stmt.gOk, mS, bGOk K body]
  | .assignSlot .. => rfl
  | .assignThru .. | .assignSlotRef .. => rfl
  | .assignGlob .. => rfl
  | .putBytes .. => rfl
  | .assignVar .. => rfl
  | .shift .. => rfl
  | .axiomCall .. => rfl
  | .regWrite .. => rfl
  | .transition .. => rfl
  | .publish .. => rfl
  | .advances .. => rfl
  | .retires .. => rfl
  | .ret .. => rfl
  | .retWhy .. => rfl
  | .leave _ => rfl
  | .next _ => rfl

theorem bGOk (K : Nat → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} :
    (b : Block D V l Γ Λ Λ') → b.gOk K (fun _ => true) = mB (indMerkmal K) b
  | .nil => rfl
  | .cons s rest => by simp only [Block.gOk, mB, sGOk K s, bGOk K rest]
  | .bind _ rest => by simp only [Block.gOk, mB, bGOk K rest]
  | .bindCall _ _ _ _ _ rest => by simp only [Block.gOk, mB, bGOk K rest]; rfl
  | .bindCallInd _ _ _ _ _ rest => by simp only [Block.gOk, mB, bGOk K rest]; rfl
  | .bindCallElse _ _ _ _ _ err rest => by simp only [Block.gOk, mB, eGOk K err, bGOk K rest]; rfl
  | .bindAxiom _ _ _ _ _ _ _ rest => by simp only [Block.gOk, mB, bGOk K rest]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by simp only [Block.gOk, mB, eGOk K err, bGOk K rest]
  | .regRead _ _ rest => by simp only [Block.gOk, mB, bGOk K rest, Bool.true_and]
  | .regReadElse _ _ _ sonst rest => by simp only [Block.gOk, mB, eGOk K sonst, bGOk K rest, Bool.true_and]
  | .awaits _ _ _ _ _ rest => by simp only [Block.gOk, mB, bGOk K rest]
  | .exchange _ _ _ _ rest => by simp only [Block.gOk, mB, bGOk K rest]
  | .narrow _ _ _ sonst rest => by simp only [Block.gOk, mB, eGOk K sonst, bGOk K rest]
  | .check _ sonst rest => by simp only [Block.gOk, mB, eGOk K sonst, bGOk K rest]
  | .float _ _ _ _ _ rest => by simp only [Block.gOk, mB, bGOk K rest]
  | .floatLit _ _ _ rest => by simp only [Block.gOk, mB, bGOk K rest]
  | .floatOf _ _ _ rest => by simp only [Block.gOk, mB, bGOk K rest]
  | .floatNarrow _ _ _ sonst rest => by simp only [Block.gOk, mB, eGOk K sonst, bGOk K rest]

theorem aGOk (K : Nat → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
    {cs : List (Option (Int × Int))} : (a : Arms D V l Γ Λ Λ' cs) → a.gOk K (fun _ => true) = mArms (indMerkmal K) a
  | .nil => rfl
  | .cons b rest => by simp only [Arms.gOk, mArms, bGOk K b, aGOk K rest]

theorem gaGOk (K : Nat → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} :
    (a : GrundArms D V l Γ Λ Λ' n) → a.gOk K (fun _ => true) = mGArms (indMerkmal K) a
  | .nil => rfl
  | .cons b rest => by simp only [GrundArms.gOk, mGArms, bGOk K b, gaGOk K rest]

theorem eGOk (K : Nat → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} :
    (e : Endblock D V l Γ Λ) → e.gOk K (fun _ => true) = mE (indMerkmal K) e
  | .ret .. => rfl
  | .retWhy .. => rfl
  | .leave _ => rfl
  | .next _ => rfl
  | .cons s rest => by simp only [Endblock.gOk, mE, sGOk K s, eGOk K rest]
  | .bind _ rest => by simp only [Endblock.gOk, mE, eGOk K rest]
  | .bindCall _ _ _ _ _ rest => by simp only [Endblock.gOk, mE, eGOk K rest]; rfl
  | .bindCallElse _ _ _ _ _ err rest => by simp only [Endblock.gOk, mE, eGOk K err, eGOk K rest]; rfl
  | .bindAxiom _ _ _ _ _ _ _ rest => by simp only [Endblock.gOk, mE, eGOk K rest]
  | .bindAxiomElse _ _ _ _ _ _ _ _ err rest => by simp only [Endblock.gOk, mE, eGOk K err, eGOk K rest]
  | .regRead _ _ rest => by simp only [Endblock.gOk, mE, eGOk K rest, Bool.true_and]
  | .regReadElse _ _ _ sonst rest => by simp only [Endblock.gOk, mE, eGOk K sonst, eGOk K rest, Bool.true_and]
  | .awaits _ _ _ _ _ rest => by simp only [Endblock.gOk, mE, eGOk K rest]
  | .bindCallInd _ _ _ _ _ rest => by simp only [Endblock.gOk, mE, eGOk K rest]; rfl
  | .narrow _ _ _ sonst rest => by simp only [Endblock.gOk, mE, eGOk K sonst, eGOk K rest]
  | .exchange _ _ _ _ rest => by simp only [Endblock.gOk, mE, eGOk K rest]
  | .ite _ t e => by simp only [Endblock.gOk, mE, eGOk K t, eGOk K e, Bool.and_comm]

end

/-- **The atom "in the fragment without its indirect-call test" is always true**: the cells `0.0 0..` have no program. -/
theorem gOk_ohne_test {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    e.gOk (fun _ => true) (fun _ => true) = true := by
  rw [eGOk]; exact mE_top e

/-- The probe "calls through no pointer type `g` conforms to" (the probe of `indB`). -/
def ohneInd (g : D.Fn) : Merkmal D := ⟨fun _ => true, fun n => !(D.passt g n), fun _ => true⟩

/-- The admissibility of indirect calls over the complete function list is the conjunction, over every function `g`
    whose contract carriers are not in the footprint, of "calls through no pointer type `g` conforms to". -/
theorem kand_zerlegt (fs : List D.Fn) (Ok : D.Fn → Bool) {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}
    (e : Endblock D V l Γ Λ) :
    mE (indMerkmal fun n => fs.all fun g => !(D.passt g n) || Ok g) e =
      fs.all fun g => Ok g || mE (ohneInd g) e := by
  have hA : (indMerkmal fun n => fs.all fun g => !(D.passt g n) || Ok g : Merkmal D) =
      Merkmal.alle (fs.map fun g => if Ok g then Merkmal.top else ohneInd g) := by
    apply Merkmal.gleich
    · intro h; rw [alle_ruf]; simp only [List.all_map, Function.comp_def]
      symm; apply List.all_eq_true.2; intro g _; split <;> rfl
    · intro n; rw [alle_ind]; simp only [List.all_map, Function.comp_def]
      show (fs.all fun g => !(D.passt g n) || Ok g) = _
      apply congrArg (List.all fs); funext g
      split
      · rename_i h; simp [h, Merkmal.top]
      · rename_i h
        simp only [h, ohneInd, Bool.or_false]
    · intro L; rw [alle_sperre]; simp only [List.all_map, Function.comp_def]
      symm; apply List.all_eq_true.2; intro g _; split <;> rfl
  rw [hA, mE_alle, List.all_map]
  apply congrArg (List.all fs); funext g
  simp only [Function.comp_def]
  split
  · rename_i h; rw [h, mE_top]; rfl
  · rename_i h; simp [h]

theorem indB_eq (P : Programm D) (f g : D.Fn) : indB P f g = !(mE (ohneInd g) (P.rumpf f)) := rfl

theorem any_nicht {α : Type} (l : List α) (p : α → Bool) : (l.any fun x => !p x) = !(l.all p) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.any_cons, List.all_cons, ih, Bool.not_and]

end Gabbro.Grammatik.Gen
