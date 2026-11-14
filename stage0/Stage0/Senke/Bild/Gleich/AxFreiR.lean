/-
  File:      stage0/Stage0/Senke/Bild/Gleich/AxFreiR.lean
  Subject:   **The image fragment has no foreign call.** Every statement, block and terminal block of the covered
             fragment (`StmtR`/`BlockR`/`EndR`, `RufAdaequatRufG/T1.lean`) passes the check `axFrei`: the fragment
             admits no foreign-call form (leaves are `BlattG`, calls are direct calls). So inside the fragment the
             substitution theorem (`Ersetzung.lean`) needs only the register/visibility half of read-blindness, and
             a program all of whose bodies lie in the fragment is `FremdFrei`.
-/
module
public import Stage0.Senke.Bild.Gleich.AxFrei
public import Grammatik.Logik.Ruf.Adaequat.RufAdaequatRufG.T1
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration} {V : Vertrag D} {A : D.Lock → Prop} {C : D.Fn → Prop}

mutual

theorem axFrei_stmtR {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} :
    StmtR A C mr s → s.axFrei = true
  | .blatt _ hb => by cases hb <;> rfl
  | .ite _ _ _ ht he => by
      simp only [Stmt.axFrei, Bool.and_eq_true]
      exact ⟨axFrei_blockR ht, axFrei_blockR he⟩
  | .onOption _ _ _ hp ha => by
      simp only [Stmt.axFrei, Bool.and_eq_true]
      exact ⟨axFrei_blockR hp, axFrei_blockR ha⟩
  | .onTag _ _ ha => by
      simp only [Stmt.axFrei]
      exact axFrei_armsR ha
  | .onWhy _ _ ha => by
      simp only [Stmt.axFrei]
      exact axFrei_grundR ha
  | .breaking _ _ hb => by
      simp only [Stmt.axFrei]
      exact axFrei_blockR hb
  | .locks _ _ _ _ _ hb => by
      simp only [Stmt.axFrei]
      exact axFrei_blockR hb
  | .ret _ _ => rfl
  | .call s _ hg _ => by
      cases s <;> simp only [Stmt.rufZiel, Option.some.injEq, reduceCtorEq] at hg <;> rfl
  | .traverse _ _ _ hb => by
      simp only [Stmt.axFrei]
      exact axFrei_blockR hb
  | .retry _ _ _ _ hb hu => by
      simp only [Stmt.axFrei, Bool.and_eq_true]
      exact ⟨axFrei_blockR hb, axFrei_blockR hu⟩
  | .forever _ _ _ hb => by
      simp only [Stmt.axFrei]
      exact axFrei_blockR hb
  | .leave _ => rfl
  | .next _ => rfl
  | .retWhy _ _ => rfl

theorem axFrei_blockR {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {b : Block D V l Γ Λ Λ'} :
    BlockR A C mr b → b.axFrei = true
  | .nil => rfl
  | .cons _ _ hs hr => by
      simp only [Block.axFrei, Bool.and_eq_true]
      exact ⟨axFrei_stmtR hs, axFrei_blockR hr⟩
  | .bind _ _ hr => by
      simp only [Block.axFrei]
      exact axFrei_blockR hr
  | .bindCall _ _ _ _ _ _ _ hr => by
      simp only [Block.axFrei]
      exact axFrei_blockR hr
  | .regRead _ _ _ hr => by
      simp only [Block.axFrei]
      exact axFrei_blockR hr
  | .regReadElse _ _ _ _ _ hs hr => by
      simp only [Block.axFrei, Bool.and_eq_true]
      exact ⟨axFrei_endR hs, axFrei_blockR hr⟩
  | .awaits _ _ _ _ _ _ hr => by
      simp only [Block.axFrei]
      exact axFrei_blockR hr
  | .exchange _ _ _ _ _ hr => by
      simp only [Block.axFrei]
      exact axFrei_blockR hr
  | .narrow _ _ _ _ _ hs hr => by
      simp only [Block.axFrei, Bool.and_eq_true]
      exact ⟨axFrei_endR hs, axFrei_blockR hr⟩
  | .check _ _ _ hs hr => by
      simp only [Block.axFrei, Bool.and_eq_true]
      exact ⟨axFrei_endR hs, axFrei_blockR hr⟩
  | .float _ _ _ _ _ _ hr => by
      simp only [Block.axFrei]
      exact axFrei_blockR hr
  | .floatLit _ _ _ _ hr => by
      simp only [Block.axFrei]
      exact axFrei_blockR hr
  | .floatOf _ _ _ _ hr => by
      simp only [Block.axFrei]
      exact axFrei_blockR hr
  | .floatNarrow _ _ _ _ _ hs hr => by
      simp only [Block.axFrei, Bool.and_eq_true]
      exact ⟨axFrei_endR hs, axFrei_blockR hr⟩
  | .bindCallElse _ _ _ _ _ _ _ _ herr hr => by
      simp only [Block.axFrei, Bool.and_eq_true]
      exact ⟨axFrei_endR herr, axFrei_blockR hr⟩

theorem axFrei_endR {l : Bool} {Γ : Ctx} {Λ : List (Res D)} {e : Endblock D V l Γ Λ} :
    EndR A C e → e.axFrei = true
  | .ret _ _ => rfl
  | .cons _ _ hs hr => by
      simp only [Endblock.axFrei, Bool.and_eq_true]
      exact ⟨axFrei_stmtR hs, axFrei_endR hr⟩
  | .bind _ _ hr => by
      simp only [Endblock.axFrei]
      exact axFrei_endR hr
  | .retWhy _ _ => rfl
  | .float _ _ _ _ _ _ hr => by
      simp only [Endblock.axFrei]
      exact axFrei_endR hr
  | .floatLit _ _ _ _ hr => by
      simp only [Endblock.axFrei]
      exact axFrei_endR hr
  | .floatOf _ _ _ _ hr => by
      simp only [Endblock.axFrei]
      exact axFrei_endR hr
  | .floatNarrow _ _ _ _ _ hs hr => by
      simp only [Endblock.axFrei, Bool.and_eq_true]
      exact ⟨axFrei_endR hs, axFrei_endR hr⟩

theorem axFrei_armsR {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {cs : List (Option Ty)}
    {a : Arms D V l Γ Λ Λ' cs} : ArmsR A C mr a → a.axFrei = true
  | .nil => rfl
  | .cons _ _ hb hr => by
      simp only [Arms.axFrei, Bool.and_eq_true]
      exact ⟨axFrei_blockR hb, axFrei_armsR hr⟩

theorem axFrei_grundR {mr l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)} {n : Nat}
    {a : GrundArms D V l Γ Λ Λ' n} : GrundArmsR A C mr a → a.axFrei = true
  | .nil => rfl
  | .cons _ _ hb hr => by
      simp only [GrundArms.axFrei, Bool.and_eq_true]
      exact ⟨axFrei_blockR hb, axFrei_grundR hr⟩

end

/-- **A program whose bodies all lie in the fragment has no foreign call.** -/
theorem fremdFrei_endR {P : Programm D} (h : ∀ g : D.Fn, EndR A C (P.rumpf g)) : FremdFrei P :=
  fun g => axFrei_endR (h g)

#print axioms axFrei_endR

end Gabbro.Stage0.Senke.BildLauf
