module

public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuhe
public import Grammatik.Nebenlaeufigkeit.Allgemein.Verklemmung
public import Grammatik.Nebenlaeufigkeit.Sperren.Ruhe.MitRuheStatisch.T1.Teil1

@[expose] public section

namespace Gabbro.Grammatik
variable {D : Deklaration}

mutual

theorem ruS_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ'), Stmt.gOk (D := D.mitRuhe) K Rg (ruS s) = s.gOk (kZ K) Rg
  | _, _, _, _, .assignSlot .. => rfl
  | _, _, _, _, .assignThru .. | _, _, _, _, .assignSlotRef .. => rfl
  | _, _, _, _, .assignGlob .. => rfl
  | _, _, _, _, .putBytes .. => rfl
  | _, _, _, _, .assignVar .. => rfl
  | _, _, _, _, .shift .. => rfl
  | _, _, _, _, .ite _ t e => kongr₂ (· && ·) (ruB_gOk K Rg t) (ruB_gOk K Rg e)
  | _, _, _, _, .onOption _ p a => kongr₂ (· && ·) (ruB_gOk K Rg p) (ruB_gOk K Rg a)
  | _, _, _, _, .onTag _ arms => ruArms_gOk K Rg arms
  | _, _, _, _, .onWhy _ arms => ruGArms_gOk K Rg arms
  | _, _, _, _, .call .. => gOk_nachΛ _ _ _ _
  | _, _, _, _, .callInd .. => gOk_nachΛ _ _ _ _
  | _, _, _, _, .locks _ _ body => ruB_gOk K Rg body
  | _, _, _, _, .breaking _ body => ruB_gOk K Rg body
  | _, _, _, _, .traverse _ _ body => ruB_gOk K Rg body
  | _, _, _, _, .consumeTraverse _ _ _ _ _ _ body => ruB_gOk K Rg body
  | _, _, _, _, .retry _ _ body ueber =>
      kongr₂ (· && ·) (ruB_gOk K Rg body) (ruB_gOk K Rg ueber)
  | _, _, _, _, .forever _ _ body => ruB_gOk K Rg body
  | _, _, _, _, .axiomCall .. => rfl
  | _, _, _, _, .regWrite .. => rfl
  | _, _, _, _, .transition .. => rfl
  | _, _, _, _, .publish .. => rfl
  | _, _, _, _, .advances .. => gOk_nachΛ _ _ _ _
  | _, _, _, _, .retires .. => gOk_nachΛ _ _ _ _
  | _, _, _, _, .ret .. => rfl
  | _, _, _, _, .retWhy .. => rfl
  | _, _, _, _, .retScoped .. => rfl
  | _, _, _, _, .retWhyScoped .. => rfl
  | _, _, _, _, .leave _ => rfl
  | _, _, _, _, .next _ => rfl

theorem ruB_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) {V : Vertrag D} : ∀ {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (b : Block D V l Γ Λ Λ'), Block.gOk (D := D.mitRuhe) K Rg (ruB b) = b.gOk (kZ K) Rg
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons s rest => kongr₂ (· && ·) (ruS_gOk K Rg s) (ruB_gOk K Rg rest)
  | _, _, _, _, .bind _ rest => ruB_gOk K Rg rest
  | _, _, _, _, .bindCall _ _ _ _ _ rest => (gOk_vorΛ _ _ _ _).trans (ruB_gOk K Rg rest)
  | _, _, _, _, .bindCallInd (n := n) _ _ _ _ _ rest =>
      congrArg (K (n + 1) && ·) ((gOk_vorΛ _ _ _ _).trans (ruB_gOk K Rg rest))
  | _, _, _, _, .bindCallElse _ _ _ _ _ err rest =>
      kongr₂ (· && ·) ((gOk_umΛ _ _ _ _).trans (ruEnd_gOk K Rg err))
        ((gOk_vorΛ _ _ _ _).trans (ruB_gOk K Rg rest))
  | _, _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => ruB_gOk K Rg rest
  | _, _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest =>
      kongr₂ (· && ·) (ruEnd_gOk K Rg err) (ruB_gOk K Rg rest)
  | _, _, _, _, .regRead r _ rest => congrArg (Rg r && ·) (ruB_gOk K Rg rest)
  | _, _, _, _, .regReadElse r _ _ sonst rest =>
      congrArg (Rg r && ·) (kongr₂ (· && ·) (ruEnd_gOk K Rg sonst) (ruB_gOk K Rg rest))
  | _, _, _, _, .awaits _ _ _ _ _ rest => ruB_gOk K Rg rest
  | _, _, _, _, .exchange _ _ _ _ rest => ruB_gOk K Rg rest
  | _, _, _, _, .narrow _ _ _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_gOk K Rg sonst) (ruB_gOk K Rg rest)
  | _, _, _, _, .narrowRequired _ _ _ rest => ruB_gOk K Rg rest
  | _, _, _, _, .check _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_gOk K Rg sonst) (ruB_gOk K Rg rest)
  | _, _, _, _, .float _ _ _ _ _ rest => ruB_gOk K Rg rest
  | _, _, _, _, .floatLit _ _ _ rest => ruB_gOk K Rg rest
  | _, _, _, _, .floatOf _ _ _ rest => ruB_gOk K Rg rest
  | _, _, _, _, .floatNarrow _ _ _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_gOk K Rg sonst) (ruB_gOk K Rg rest)

theorem ruEnd_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) {V : Vertrag D} : ∀ {l : Bool}
    {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ), Endblock.gOk (D := D.mitRuhe) K Rg (ruEnd e) = e.gOk (kZ K) Rg
  | _, _, _, .ret .. => rfl
  | _, _, _, .retWhy .. => rfl
  | _, _, _, .retScoped .. => rfl
  | _, _, _, .retWhyScoped .. => rfl
  | _, _, _, .leave _ => rfl
  | _, _, _, .next _ => rfl
  | _, _, _, .cons s rest => kongr₂ (· && ·) (ruS_gOk K Rg s) (ruEnd_gOk K Rg rest)
  | _, _, _, .bind _ rest => ruEnd_gOk K Rg rest
  | _, _, _, .bindCall _ _ _ _ _ rest => (gOk_umΛ _ _ _ _).trans (ruEnd_gOk K Rg rest)
  | _, _, _, .bindCallElse _ _ _ _ _ err rest =>
      kongr₂ (· && ·) ((gOk_umΛ _ _ _ _).trans (ruEnd_gOk K Rg err))
        ((gOk_umΛ _ _ _ _).trans (ruEnd_gOk K Rg rest))
  | _, _, _, .bindAxiom _ _ _ _ _ _ _ rest => ruEnd_gOk K Rg rest
  | _, _, _, .bindAxiomElse _ _ _ _ _ _ _ _ err rest =>
      kongr₂ (· && ·) (ruEnd_gOk K Rg err) (ruEnd_gOk K Rg rest)
  | _, _, _, .regRead r _ rest => congrArg (Rg r && ·) (ruEnd_gOk K Rg rest)
  | _, _, _, .regReadElse r _ _ sonst rest =>
      congrArg (Rg r && ·) (kongr₂ (· && ·) (ruEnd_gOk K Rg sonst) (ruEnd_gOk K Rg rest))
  | _, _, _, .awaits _ _ _ _ _ rest => ruEnd_gOk K Rg rest
  | _, _, _, .bindCallInd (n := n) _ _ _ _ _ rest =>
      congrArg (K (n + 1) && ·) ((gOk_umΛ _ _ _ _).trans (ruEnd_gOk K Rg rest))
  | _, _, _, .narrow _ _ _ sonst rest =>
      kongr₂ (· && ·) (ruEnd_gOk K Rg sonst) (ruEnd_gOk K Rg rest)
  | _, _, _, .narrowRequired _ _ _ rest => ruEnd_gOk K Rg rest
  | _, _, _, .exchange _ _ _ _ rest => ruEnd_gOk K Rg rest
  | _, _, _, .ite _ t e => kongr₂ (· && ·) (ruEnd_gOk K Rg e) (ruEnd_gOk K Rg t)

theorem ruArms_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) {V : Vertrag D} : ∀ {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    (arms : Arms D V l Γ Λ Λ' cs), Arms.gOk (D := D.mitRuhe) K Rg (ruArms arms) = arms.gOk (kZ K) Rg
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons (c := none) b rest =>
      kongr₂ (· && ·) (ruB_gOk K Rg b) (ruArms_gOk K Rg rest)
  | _, _, _, _, _, .cons (c := some _) b rest =>
      kongr₂ (· && ·) (ruB_gOk K Rg b) (ruArms_gOk K Rg rest)

theorem ruGArms_gOk (K : Nat → Bool) (Rg : D.Reg → Bool) {V : Vertrag D} : ∀ {l : Bool}
    {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat} (arms : GrundArms D V l Γ Λ Λ' n),
    GrundArms.gOk (D := D.mitRuhe) K Rg (ruGArms arms) = arms.gOk (kZ K) Rg
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .cons b rest => kongr₂ (· && ·) (ruB_gOk K Rg b) (ruGArms_gOk K Rg rest)

end
/-! ## 7. The feature test -/

/-- A feature set of `D.mitRuhe`, read back on `D`: direct callee `f` is
    `some f`, signature `n` is `n + 1`. -/
def mZ (A : Merkmal D.mitRuhe) : Merkmal D :=
  ⟨fun f => A.ruf (some f), fun n => A.ind (n + 1), A.sperre⟩


end Gabbro.Grammatik
