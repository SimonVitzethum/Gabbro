/-
  File:      stage0/Stage0/Senke/Bild/Rek/EndRBSatz.lean
  Subject:   **The fragment check is sound** (review M1): a statement, block or terminal block that passes the
             decidable check `fragB` (`EndRB.lean`) lies in the call fragment `StmtR`/`BlockR`/`EndR` with every
             callee admitted, for every lock predicate `Agl` that contains the locks `a` admits. One mutual recursion
             over the grammar; every constructor the fragment does not contain fails the check.
-/
module
public import Stage0.Senke.Bild.Rek.EndRB
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration} {V : Vertrag D} {Agl : D.Lock → Prop}

mutual

theorem stmtR_fragB (a : D.Lock → Bool) (hA : ∀ L, a L = true → Agl L) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (mr : Bool) :
    (s : Stmt D V l Γ Λ Λ') → Stmt.fragB a mr s = true → StmtR Agl (fun _ => True) mr s
  | .ite c t e, h => by
      simp only [Stmt.fragB, Bool.and_eq_true] at h
      exact StmtR.ite c t e (blockR_fragB a hA mr t h.1) (blockR_fragB a hA mr e h.2)
  | .onOption o p q, h => by
      simp only [Stmt.fragB, Bool.and_eq_true] at h
      exact StmtR.onOption o p q (blockR_fragB a hA mr p h.1) (blockR_fragB a hA mr q h.2)
  | .onTag v arms, h => by
      simp only [Stmt.fragB] at h
      exact StmtR.onTag v arms (armsR_fragB a hA mr arms h)
  | .onWhy r arms, h => by
      simp only [Stmt.fragB] at h
      exact StmtR.onWhy r arms (grundR_fragB a hA mr arms h)
  | .breaking i body, h => by
      simp only [Stmt.fragB] at h
      exact StmtR.breaking i body (blockR_fragB a hA mr body h)
  | .locks L hr body, h => by
      simp only [Stmt.fragB, Bool.and_eq_true, and_assoc] at h
      exact StmtR.locks L hr body (bodenOk_sound h.2.1) (hA L h.1) (blockR_fragB a hA false body h.2.2)
  | .ret e hΛ, h => by
      simp only [Stmt.fragB] at h
      subst h
      exact StmtR.ret e hΛ
  | .call f args hp hr, _ => StmtR.call _ f rfl trivial
  | .traverse t inv body, h => by
      simp only [Stmt.fragB] at h
      exact StmtR.traverse t inv body (blockR_fragB a hA mr body h)
  | .retry n bis body u, h => by
      simp only [Stmt.fragB, Bool.and_eq_true] at h
      exact StmtR.retry n bis body u (blockR_fragB a hA mr body h.1) (blockR_fragB a hA mr u h.2)
  | .forever x inv body, h => by
      simp only [Stmt.fragB] at h
      exact StmtR.forever x inv body (blockR_fragB a hA mr body h)
  | .leave hl, _ => by
      subst hl
      exact StmtR.leave rfl
  | .next hl, _ => by
      subst hl
      exact StmtR.next rfl
  | .retWhy r hΛ, h => by
      simp only [Stmt.fragB] at h
      subst h
      exact StmtR.retWhy (A := Agl) (C := fun _ => True) (l := l) (Γ := Γ) (Λ := Λ) r hΛ
  | .assignSlot .., _ => StmtR.blatt _ (by constructor)
  | .assignThru .., _ => StmtR.blatt _ (by constructor)
  | .assignThruOwn .., _ => StmtR.blatt _ (by constructor)
  | .assignSlotRef .., _ => StmtR.blatt _ (by constructor)
  | .assignGlob .., _ => StmtR.blatt _ (by constructor)
  | .putBytes .., _ => StmtR.blatt _ (by constructor)
  | .assignVar .., _ => StmtR.blatt _ (by constructor)
  | .shift .., _ => StmtR.blatt _ (by constructor)
  | .regWrite .., _ => StmtR.blatt _ (by constructor)
  | .transition .., _ => StmtR.blatt _ (by constructor)
  | .publish .., _ => StmtR.blatt _ (by constructor)
  | .advances .., _ => StmtR.blatt _ (by constructor)
  | .retires .., _ => StmtR.blatt _ (by constructor)
  | .consumeTraverse .., h => absurd h Bool.false_ne_true
  | .axiomCallElse .., h => absurd h Bool.false_ne_true
  | .callIndElse .., h => absurd h Bool.false_ne_true
  | .callInd .., h => absurd h Bool.false_ne_true
  | .axiomCall .., h => absurd h Bool.false_ne_true
  | .retScoped .., h => absurd h Bool.false_ne_true
  | .retWhyScoped .., h => absurd h Bool.false_ne_true

theorem blockR_fragB (a : D.Lock → Bool) (hA : ∀ L, a L = true → Agl L) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} (mr : Bool) :
    (b : Block D V l Γ Λ Λ') → Block.fragB a mr b = true → BlockR Agl (fun _ => True) mr b
  | .nil, _ => BlockR.nil
  | .cons s rest, h => by
      simp only [Block.fragB, Bool.and_eq_true] at h
      exact BlockR.cons s rest (stmtR_fragB a hA mr s h.1) (blockR_fragB a hA mr rest h.2)
  | .bind e rest, h => by
      simp only [Block.fragB] at h
      exact BlockR.bind e rest (blockR_fragB a hA mr rest h)
  | .bindCall f args he hp hr rest, h => by
      simp only [Block.fragB] at h
      exact BlockR.bindCall f args he hp hr rest trivial (blockR_fragB a hA mr rest h)
  | .regRead r hk rest, h => by
      simp only [Block.fragB] at h
      exact BlockR.regRead r hk rest (blockR_fragB a hA mr rest h)
  | .regReadElse r hk z sonst rest, h => by
      simp only [Block.fragB, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at h
      obtain ⟨hl, hm, hs, hr⟩ := h
      have hRec0 := endR_fragB a hA sonst hs
      have hRec1 := blockR_fragB a hA _ rest hr
      subst hl
      subst hm
      exact BlockR.regReadElse r hk z sonst rest hRec0 hRec1
  | .awaits g pl hp hL ha rest, h => by
      simp only [Block.fragB] at h
      exact BlockR.awaits g pl hp hL ha rest (blockR_fragB a hA mr rest h)
  | .exchange g neu hw hL rest, h => by
      simp only [Block.fragB] at h
      exact BlockR.exchange g neu hw hL rest (blockR_fragB a hA mr rest h)
  | .narrow e lo' hi' sonst rest, h => by
      simp only [Block.fragB, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at h
      obtain ⟨hl, hm, hs, hr⟩ := h
      have hRec0 := endR_fragB a hA sonst hs
      have hRec1 := blockR_fragB a hA _ rest hr
      subst hl
      subst hm
      exact BlockR.narrow e lo' hi' sonst rest hRec0 hRec1
  | .check c sonst rest, h => by
      simp only [Block.fragB, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at h
      obtain ⟨hl, hm, hs, hr⟩ := h
      have hRec0 := endR_fragB a hA sonst hs
      have hRec1 := blockR_fragB a hA _ rest hr
      subst hl
      subst hm
      exact BlockR.check c sonst rest hRec0 hRec1
  | .float op x y lo hi rest, h => by
      simp only [Block.fragB] at h
      exact BlockR.float op x y lo hi rest (blockR_fragB a hA mr rest h)
  | .floatLit q lo hi rest, h => by
      simp only [Block.fragB] at h
      exact BlockR.floatLit q lo hi rest (blockR_fragB a hA mr rest h)
  | .floatOf e lo hi rest, h => by
      simp only [Block.fragB] at h
      exact BlockR.floatOf e lo hi rest (blockR_fragB a hA mr rest h)
  | .floatNarrow e lo hi sonst rest, h => by
      simp only [Block.fragB, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at h
      obtain ⟨hl, hm, hs, hr⟩ := h
      have hRec0 := endR_fragB a hA sonst hs
      have hRec1 := blockR_fragB a hA _ rest hr
      subst hl
      subst hm
      exact BlockR.floatNarrow e lo hi sonst rest hRec0 hRec1
  | .bindCallElse f args he hp hr err rest, h => by
      simp only [Block.fragB, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at h
      obtain ⟨hl, hm, hs, hrest⟩ := h
      have hRec0 := endR_fragB a hA err hs
      have hRec1 := blockR_fragB a hA _ rest hrest
      subst hl
      subst hm
      exact BlockR.bindCallElse f args he hp hr err rest trivial hRec0 hRec1
  | .bindCallInd .., h => absurd h Bool.false_ne_true
  | .bindCallIndElse .., h => absurd h Bool.false_ne_true
  | .bindAxiom .., h => absurd h Bool.false_ne_true
  | .bindAxiomElse .., h => absurd h Bool.false_ne_true
  | .bindAxiomOpt .., h => absurd h Bool.false_ne_true
  | .bindAxiomOptElse .., h => absurd h Bool.false_ne_true
  | .narrowRequired .., h => absurd h Bool.false_ne_true

theorem endR_fragB (a : D.Lock → Bool) (hA : ∀ L, a L = true → Agl L) {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} : (e : Endblock D V l Γ Λ) → Endblock.fragB a e = true → EndR Agl (fun _ => True) e
  | .ret e hΛ, h => by
      simp only [Endblock.fragB, Bool.not_eq_true'] at h
      subst h
      exact EndR.ret e hΛ
  | .retWhy r hΛ, h => by
      simp only [Endblock.fragB, Bool.not_eq_true'] at h
      subst h
      exact EndR.retWhy (A := Agl) (C := fun _ => True) (Γ := Γ) (Λ := Λ) r hΛ
  | .cons s rest, h => by
      simp only [Endblock.fragB, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at h
      obtain ⟨hl, hs, hr⟩ := h
      have hRec0 := stmtR_fragB a hA _ s hs
      have hRec1 := endR_fragB a hA rest hr
      subst hl
      exact EndR.cons s rest hRec0 hRec1
  | .bind e rest, h => by
      simp only [Endblock.fragB, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hl, hr⟩ := h
      have hRec0 := endR_fragB a hA rest hr
      subst hl
      exact EndR.bind e rest hRec0
  | .float op x y lo hi rest, h => by
      simp only [Endblock.fragB, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hl, hr⟩ := h
      have hRec0 := endR_fragB a hA rest hr
      subst hl
      exact EndR.float op x y lo hi rest hRec0
  | .floatLit q lo hi rest, h => by
      simp only [Endblock.fragB, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hl, hr⟩ := h
      have hRec0 := endR_fragB a hA rest hr
      subst hl
      exact EndR.floatLit q lo hi rest hRec0
  | .floatOf e lo hi rest, h => by
      simp only [Endblock.fragB, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨hl, hr⟩ := h
      have hRec0 := endR_fragB a hA rest hr
      subst hl
      exact EndR.floatOf e lo hi rest hRec0
  | .floatNarrow e lo hi sonst rest, h => by
      simp only [Endblock.fragB, Bool.and_eq_true, Bool.not_eq_true', and_assoc] at h
      obtain ⟨hl, hs, hr⟩ := h
      have hRec0 := endR_fragB a hA sonst hs
      have hRec1 := endR_fragB a hA rest hr
      subst hl
      exact EndR.floatNarrow e lo hi sonst rest hRec0 hRec1
  | .leave .., h => absurd h Bool.false_ne_true
  | .next .., h => absurd h Bool.false_ne_true
  | .bindCall .., h => absurd h Bool.false_ne_true
  | .bindCallElse .., h => absurd h Bool.false_ne_true
  | .bindAxiom .., h => absurd h Bool.false_ne_true
  | .bindAxiomElse .., h => absurd h Bool.false_ne_true
  | .regRead .., h => absurd h Bool.false_ne_true
  | .regReadElse .., h => absurd h Bool.false_ne_true
  | .awaits .., h => absurd h Bool.false_ne_true
  | .bindCallInd .., h => absurd h Bool.false_ne_true
  | .narrow .., h => absurd h Bool.false_ne_true
  | .exchange .., h => absurd h Bool.false_ne_true
  | .ite .., h => absurd h Bool.false_ne_true
  | .narrowRequired .., h => absurd h Bool.false_ne_true
  | .bindAxiomOpt .., h => absurd h Bool.false_ne_true
  | .bindAxiomOptElse .., h => absurd h Bool.false_ne_true
  | .bindCallIndElse .., h => absurd h Bool.false_ne_true
  | .retScoped .., h => absurd h Bool.false_ne_true
  | .retWhyScoped .., h => absurd h Bool.false_ne_true

theorem armsR_fragB (a : D.Lock → Bool) (hA : ∀ L, a L = true → Agl L) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} (mr : Bool) :
    (arms : Arms D V l Γ Λ Λ' cs) → Arms.fragB a mr arms = true → ArmsR Agl (fun _ => True) mr arms
  | .nil, _ => ArmsR.nil
  | .cons b rest, h => by
      simp only [Arms.fragB, Bool.and_eq_true] at h
      exact ArmsR.cons b rest (blockR_fragB a hA mr b h.1) (armsR_fragB a hA mr rest h.2)

theorem grundR_fragB (a : D.Lock → Bool) (hA : ∀ L, a L = true → Agl L) {l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} (mr : Bool) :
    (arms : GrundArms D V l Γ Λ Λ' n) → GrundArms.fragB a mr arms = true →
      GrundArmsR Agl (fun _ => True) mr arms
  | .nil, _ => GrundArmsR.nil
  | .cons b rest, h => by
      simp only [GrundArms.fragB, Bool.and_eq_true] at h
      exact GrundArmsR.cons b rest (blockR_fragB a hA mr b h.1) (grundR_fragB a hA mr rest h.2)

end

/-- **The check discharges the fragment premise of one body.** -/
theorem endR_endRB (a : D.Lock → Bool) (hA : ∀ L, a L = true → Agl L) {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {e : Endblock D V l Γ Λ} (h : endRB a e = true) : EndR Agl (fun _ => True) e :=
  endR_fragB a hA e h

/-- **The check discharges the fragment premise of a program** (`tiefAlle_frag`, `zerlegung_tiefAlle`): every body
    of an enumerated program passes. -/
theorem endR_programmRB {P : Programm D} (a : D.Lock → Bool) (hA : ∀ L, a L = true → Agl L)
    {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) (h : programmRB P a fs = true) :
    ∀ g : D.Fn, EndR Agl (fun _ => True) (P.rumpf g) := by
  intro g
  unfold programmRB at h
  exact endR_endRB a hA (List.all_eq_true.mp h g (hvoll g))

#print axioms endR_programmRB

end Gabbro.Stage0.Senke.BildLauf
