/- Part 2 of 3 of `MitRuheStatisch` (split by instrumente/teile/lean-teilen.py; the umbrella `MitRuheStatisch.lean` imports all parts). -/
module
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheStatisch.T1
@[expose] public section


namespace Gabbro.Grammatik

variable {D : Deklaration}

mutual

theorem ruS_mS (A : Merkmal D.mitRuhe) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ'), mS A (ruS s) = mS (mZ A) s
  | _, _, _, _, .assignSlot .. => rfl
  | _, _, _, _, .assignThru .. | _, _, _, _, .assignSlotRef .. => rfl
  | _, _, _, _, .assignGlob .. => rfl
  | _, _, _, _, .putBytes .. => rfl
  | _, _, _, _, .assignVar .. => rfl
  | _, _, _, _, .shift .. => rfl
  | _, _, _, _, .ite _ t e => kongr₂ (· && ·) (ruB_mB A t) (ruB_mB A e)
  | _, _, _, _, .onOption _ p a => kongr₂ (· && ·) (ruB_mB A p) (ruB_mB A a)
  | _, _, _, _, .onTag _ arms => ruArms_mArms A arms
  | _, _, _, _, .onWhy _ arms => ruGArms_mGArms A arms
  | _, _, _, _, .call .. => mS_nachΛ _ _ _
  | _, _, _, _, .callInd .. => mS_nachΛ _ _ _
  | _, _, _, _, .callIndElse (n := n) _ _ _ _ _ err =>
      (mS_nachΛ _ _ _).trans (kongr₂ (· && ·) rfl ((mE_umΛ _ _ _).trans (ruEnd_mE A err)))
  | _, _, _, _, .locks L _ body => congrArg (A.sperre L && ·) (ruB_mB A body)
  | _, _, _, _, .breaking _ body => ruB_mB A body
  | _, _, _, _, .traverse _ _ body => ruB_mB A body
  | _, _, _, _, .consumeTraverse _ _ _ _ _ _ body => ruB_mB A body
  | _, _, _, _, .retry _ _ body ueber => kongr₂ (· && ·) (ruB_mB A body) (ruB_mB A ueber)
  | _, _, _, _, .forever _ _ body => ruB_mB A body
  | _, _, _, _, .axiomCall .. => rfl
  | _, _, _, _, .axiomCallElse e _ _ _ _ _ _ _ err => by
      have ih0 := ruEnd_mE A err
      cases e with
      | none =>
          simp only [ruS, mS]
          exact (mS_nachΛ _ _ _).trans ((mE_umΛ _ _ _).trans (ih0))
      | some _ =>
          simp only [ruS, mS]
          exact (mS_nachΛ _ _ _).trans ((mE_umΛ _ _ _).trans (ih0))
  | _, _, _, _, .regWrite .. => rfl
  | _, _, _, _, .transition .. => rfl
  | _, _, _, _, .publish .. => rfl
  | _, _, _, _, .advances .. => mS_nachΛ _ _ _
  | _, _, _, _, .retires .. => mS_nachΛ _ _ _
  | _, _, _, _, .ret .. => rfl
  | _, _, _, _, .retWhy .. => rfl
  | _, _, _, _, .retScoped .. => rfl
  | _, _, _, _, .retWhyScoped .. => rfl
  | _, _, _, _, .leave _ => rfl
  | _, _, _, _, .next _ => rfl

theorem ruB_mB (A : Merkmal D.mitRuhe) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ'), mB A (ruB b) = mB (mZ A) b
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons s rest => kongr₂ (· && ·) (ruS_mS A s) (ruB_mB A rest)
  | _, _, _, _, .bind _ rest => ruB_mB A rest
  | _, _, _, _, .bindCall g _ _ _ _ rest =>
      congrArg (A.ruf (some g) && ·) ((mB_vorΛ _ _ _).trans (ruB_mB A rest))
  | _, _, _, _, .bindCallInd (n := n) _ _ _ _ _ rest =>
      congrArg (A.ind (n + 1) && ·) ((mB_vorΛ _ _ _).trans (ruB_mB A rest))
  | _, _, _, _, .bindCallIndElse (n := n) _ _ _ _ _ err rest =>
      kongr₂ (fun x y => A.ind (n + 1) && x && y) ((mE_umΛ _ _ _).trans (ruEnd_mE A err))
        ((mB_vorΛ _ _ _).trans (ruB_mB A rest))
  | _, _, _, _, .bindCallElse g _ _ _ _ err rest =>
      kongr₂ (fun x y => A.ruf (some g) && x && y) ((mE_umΛ _ _ _).trans (ruEnd_mE A err))
        ((mB_vorΛ _ _ _).trans (ruB_mB A rest))
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => ruB_mB A rest
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest =>
      kongr₂ (· && ·) (ruEnd_mE A err) (ruB_mB A rest)
  | _, _, _, _, .bindAxiomOpt e _ _ _ _ _ _ rest => by
      have ih0 := ruB_mB A rest
      cases e with
      | none =>
          simp only [ruB, mB]
          exact (mB_vorΛ _ _ _).trans (ih0)
      | some _ =>
          simp only [ruB, mB]
          exact (mB_vorΛ _ _ _).trans (ih0)
  | _, _, _, _, .bindAxiomOptElse e _ _ _ _ _ _ _ err rest => by
      have ih0 := ruEnd_mE A err
      have ih1 := ruB_mB A rest
      cases e with
      | none =>
          simp only [ruB, mB]
          exact kongr₂ (· && ·)
            ((mE_umΛ _ _ _).trans (ih0))
            ((mB_vorΛ _ _ _).trans (ih1))
      | some _ =>
          simp only [ruB, mB]
          exact kongr₂ (· && ·)
            ((mE_umΛ _ _ _).trans (ih0))
            ((mB_vorΛ _ _ _).trans (ih1))
  | _, _, _, _, .regRead _ _ rest => ruB_mB A rest
  | _, _, _, _, .regReadElse _ _ _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_mE A sonst) (ruB_mB A rest)
  | _, _, _, _, .awaits _ _ _ _ _ rest => ruB_mB A rest
  | _, _, _, _, .exchange _ _ _ _ rest => ruB_mB A rest
  | _, _, _, _, .narrow _ _ _ sonst rest => kongr₂ (· && ·) (ruEnd_mE A sonst) (ruB_mB A rest)
  | _, _, _, _, .narrowRequired _ _ _ rest => ruB_mB A rest
  | _, _, _, _, .check _ sonst rest => kongr₂ (· && ·) (ruEnd_mE A sonst) (ruB_mB A rest)
  | _, _, _, _, .float _ _ _ _ _ rest => ruB_mB A rest
  | _, _, _, _, .floatLit _ _ _ rest => ruB_mB A rest
  | _, _, _, _, .floatOf _ _ _ rest => ruB_mB A rest
  | _, _, _, _, .floatNarrow _ _ _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_mE A sonst) (ruB_mB A rest)

theorem ruEnd_mE (A : Merkmal D.mitRuhe) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} (e : Endblock D V l Γ Λ), mE A (ruEnd e) = mE (mZ A) e
  | _, _, _, .ret .. => rfl
  | _, _, _, .retWhy .. => rfl
  | _, _, _, .retScoped .. => rfl
  | _, _, _, .retWhyScoped .. => rfl
  | _, _, _, .leave _ => rfl
  | _, _, _, .next _ => rfl
  | _, _, _, .cons s rest => kongr₂ (· && ·) (ruS_mS A s) (ruEnd_mE A rest)
  | _, _, _, .bind _ rest => ruEnd_mE A rest
  | _, _, _, .bindCall g _ _ _ _ rest =>
      congrArg (A.ruf (some g) && ·) ((mE_umΛ _ _ _).trans (ruEnd_mE A rest))
  | _, _, _, .bindCallElse g _ _ _ _ err rest =>
      kongr₂ (fun x y => A.ruf (some g) && x && y) ((mE_umΛ _ _ _).trans (ruEnd_mE A err))
        ((mE_umΛ _ _ _).trans (ruEnd_mE A rest))
  | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => ruEnd_mE A rest
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest =>
      kongr₂ (· && ·) (ruEnd_mE A err) (ruEnd_mE A rest)
  | _, _, _, .bindAxiomOpt e _ _ _ _ _ _ rest => by
      have ih0 := ruEnd_mE A rest
      cases e with
      | none =>
          simp only [ruEnd, mE]
          exact (mE_umΛ _ _ _).trans (ih0)
      | some _ =>
          simp only [ruEnd, mE]
          exact (mE_umΛ _ _ _).trans (ih0)
  | _, _, _, .bindAxiomOptElse e _ _ _ _ _ _ _ err rest => by
      have ih0 := ruEnd_mE A err
      have ih1 := ruEnd_mE A rest
      cases e with
      | none =>
          simp only [ruEnd, mE]
          exact kongr₂ (· && ·)
            ((mE_umΛ _ _ _).trans (ih0))
            ((mE_umΛ _ _ _).trans (ih1))
      | some _ =>
          simp only [ruEnd, mE]
          exact kongr₂ (· && ·)
            ((mE_umΛ _ _ _).trans (ih0))
            ((mE_umΛ _ _ _).trans (ih1))
  | _, _, _, .regRead _ _ rest => ruEnd_mE A rest
  | _, _, _, .regReadElse _ _ _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_mE A sonst) (ruEnd_mE A rest)
  | _, _, _, .awaits _ _ _ _ _ rest => ruEnd_mE A rest
  | _, _, _, .bindCallInd (n := n) _ _ _ _ _ rest =>
      congrArg (A.ind (n + 1) && ·) ((mE_umΛ _ _ _).trans (ruEnd_mE A rest))
  | _, _, _, .bindCallIndElse (n := n) _ _ _ _ _ err rest =>
      kongr₂ (fun x y => A.ind (n + 1) && x && y) ((mE_umΛ _ _ _).trans (ruEnd_mE A err))
        ((mE_umΛ _ _ _).trans (ruEnd_mE A rest))
  | _, _, _, .narrow _ _ _ sonst rest => kongr₂ (· && ·) (ruEnd_mE A sonst) (ruEnd_mE A rest)
  | _, _, _, .narrowRequired _ _ _ rest => ruEnd_mE A rest
  | _, _, _, .exchange _ _ _ _ rest => ruEnd_mE A rest
  | _, _, _, .ite _ t e => kongr₂ (· && ·) (ruEnd_mE A t) (ruEnd_mE A e)

theorem ruArms_mArms (A : Merkmal D.mitRuhe) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} (arms : Arms D V l Γ Λ Λ' cs),
    mArms A (ruArms arms) = mArms (mZ A) arms
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons (c := none) b rest => kongr₂ (· && ·) (ruB_mB A b) (ruArms_mArms A rest)
  | _, _, _, _, _, .cons (c := some _) b rest =>
      kongr₂ (· && ·) (ruB_mB A b) (ruArms_mArms A rest)

theorem ruGArms_mGArms (A : Merkmal D.mitRuhe) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n),
    mGArms A (ruGArms arms) = mGArms (mZ A) arms
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => kongr₂ (· && ·) (ruB_mB A b) (ruGArms_mGArms A rest)

end
end Gabbro.Grammatik
