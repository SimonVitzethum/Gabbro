/-
  File:      stage0/Stage0/Senke/Bild/Rek/EndRBVoll.lean
  Subject:   **The fragment check is complete** (review M1): everything in the call fragment passes `fragB`, for every
             callee predicate (the check admits every callee) and every lock predicate whose locks `a` admits. With
             the soundness (`EndRBSatz.lean`): `endRB_iff` -- the decidable check IS the fragment premise -- and the
             program form `programmRB_iff`. A program whose bodies pass has no foreign call (`fremdFrei_programmRB`).
-/
module
public import Stage0.Senke.Bild.Rek.EndRBSatz
public import Stage0.Senke.Bild.Gleich.AxFreiR
@[expose] public section

namespace Gabbro.Stage0.Senke.BildLauf

open Gabbro.Grammatik

set_option linter.unusedSectionVars false

variable {D : Deklaration} {V : Vertrag D} {Agl : D.Lock → Prop} {C : D.Fn → Prop}

mutual

theorem fragB_stmtR (a : D.Lock → Bool) (hA : ∀ L, Agl L → a L = true) {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {s : Stmt D V l Γ Λ Λ'} : StmtR Agl C mr s → Stmt.fragB a mr s = true
  | .blatt _ hb => by cases hb <;> rfl
  | .ite _ _ _ ht he => by
      simp only [Stmt.fragB, fragB_blockR a hA ht, fragB_blockR a hA he] <;> rfl
  | .onOption _ _ _ hp ha => by
      simp only [Stmt.fragB, fragB_blockR a hA hp, fragB_blockR a hA ha] <;> rfl
  | .onTag _ _ ha => by
      simp only [Stmt.fragB, fragB_armsR a hA ha] <;> rfl
  | .onWhy _ _ ha => by
      simp only [Stmt.fragB, fragB_grundR a hA ha] <;> rfl
  | .breaking _ _ hb => by
      simp only [Stmt.fragB, fragB_blockR a hA hb] <;> rfl
  | .locks L _ _ hbo hAL hb => by
      simp only [Stmt.fragB, hA L hAL, bodenOk_voll hbo, fragB_blockR a hA hb] <;> rfl
  | .ret _ _ => rfl
  | .call s _ hg _ => by
      cases s <;> simp only [Stmt.rufZiel, Option.some.injEq, reduceCtorEq] at hg <;> rfl
  | .traverse _ _ _ hb => by
      simp only [Stmt.fragB, fragB_blockR a hA hb] <;> rfl
  | .retry _ _ _ _ hb hu => by
      simp only [Stmt.fragB, fragB_blockR a hA hb, fragB_blockR a hA hu] <;> rfl
  | .forever _ _ _ hb => by
      simp only [Stmt.fragB, fragB_blockR a hA hb] <;> rfl
  | .leave _ => rfl
  | .next _ => rfl
  | .retWhy _ _ => rfl

theorem fragB_blockR (a : D.Lock → Bool) (hA : ∀ L, Agl L → a L = true) {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {b : Block D V l Γ Λ Λ'} : BlockR Agl C mr b → Block.fragB a mr b = true
  | .nil => rfl
  | .cons _ _ hs hr => by
      simp only [Block.fragB, fragB_stmtR a hA hs, fragB_blockR a hA hr] <;> rfl
  | .bind _ _ hr => by
      simp only [Block.fragB, fragB_blockR a hA hr] <;> rfl
  | .bindCall _ _ _ _ _ _ _ hr => by
      simp only [Block.fragB, fragB_blockR a hA hr] <;> rfl
  | .regRead _ _ _ hr => by
      simp only [Block.fragB, fragB_blockR a hA hr] <;> rfl
  | .regReadElse _ _ _ _ _ hs hr => by
      simp only [Block.fragB, fragB_endR a hA hs, fragB_blockR a hA hr] <;> rfl
  | .awaits _ _ _ _ _ _ hr => by
      simp only [Block.fragB, fragB_blockR a hA hr] <;> rfl
  | .exchange _ _ _ _ _ hr => by
      simp only [Block.fragB, fragB_blockR a hA hr] <;> rfl
  | .narrow _ _ _ _ _ hs hr => by
      simp only [Block.fragB, fragB_endR a hA hs, fragB_blockR a hA hr] <;> rfl
  | .check _ _ _ hs hr => by
      simp only [Block.fragB, fragB_endR a hA hs, fragB_blockR a hA hr] <;> rfl
  | .float _ _ _ _ _ _ hr => by
      simp only [Block.fragB, fragB_blockR a hA hr] <;> rfl
  | .floatLit _ _ _ _ hr => by
      simp only [Block.fragB, fragB_blockR a hA hr] <;> rfl
  | .floatOf _ _ _ _ hr => by
      simp only [Block.fragB, fragB_blockR a hA hr] <;> rfl
  | .floatNarrow _ _ _ _ _ hs hr => by
      simp only [Block.fragB, fragB_endR a hA hs, fragB_blockR a hA hr] <;> rfl
  | .bindCallElse _ _ _ _ _ _ _ _ herr hr => by
      simp only [Block.fragB, fragB_endR a hA herr, fragB_blockR a hA hr] <;> rfl

theorem fragB_endR (a : D.Lock → Bool) (hA : ∀ L, Agl L → a L = true) {l : Bool} {Γ : Ctx}
    {Λ : List (Res D)} {e : Endblock D V l Γ Λ} : EndR Agl C e → Endblock.fragB a e = true
  | .ret _ _ => rfl
  | .cons _ _ hs hr => by
      simp only [Endblock.fragB, fragB_stmtR a hA hs, fragB_endR a hA hr] <;> rfl
  | .bind _ _ hr => by
      simp only [Endblock.fragB, fragB_endR a hA hr] <;> rfl
  | .retWhy _ _ => rfl
  | .float _ _ _ _ _ _ hr => by
      simp only [Endblock.fragB, fragB_endR a hA hr] <;> rfl
  | .floatLit _ _ _ _ hr => by
      simp only [Endblock.fragB, fragB_endR a hA hr] <;> rfl
  | .floatOf _ _ _ _ hr => by
      simp only [Endblock.fragB, fragB_endR a hA hr] <;> rfl
  | .floatNarrow _ _ _ _ _ hs hr => by
      simp only [Endblock.fragB, fragB_endR a hA hs, fragB_endR a hA hr] <;> rfl

theorem fragB_armsR (a : D.Lock → Bool) (hA : ∀ L, Agl L → a L = true) {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {cs : List (Option Ty)} {arms : Arms D V l Γ Λ Λ' cs} :
    ArmsR Agl C mr arms → Arms.fragB a mr arms = true
  | .nil => rfl
  | .cons _ _ hb hr => by
      simp only [Arms.fragB, fragB_blockR a hA hb, fragB_armsR a hA hr] <;> rfl

theorem fragB_grundR (a : D.Lock → Bool) (hA : ∀ L, Agl L → a L = true) {mr l : Bool} {Γ : Ctx}
    {Λ Λ' : List (Res D)} {n : Nat} {arms : GrundArms D V l Γ Λ Λ' n} :
    GrundArmsR Agl C mr arms → GrundArms.fragB a mr arms = true
  | .nil => rfl
  | .cons _ _ hb hr => by
      simp only [GrundArms.fragB, fragB_blockR a hA hb, fragB_grundR a hA hr] <;> rfl

end

/-- **THE FRAGMENT PREMISE IS DECIDABLE** (review M1): a terminal block lies in the call fragment with every callee
    admitted and the locks `a` admits iff it passes the check `endRB a`. -/
theorem endRB_iff (a : D.Lock → Bool) {l : Bool} {Γ : Ctx} {Λ : List (Res D)} (e : Endblock D V l Γ Λ) :
    EndR (fun L => a L = true) (fun _ => True) e ↔ endRB a e = true :=
  ⟨fun h => fragB_endR a (fun _ hL => hL) h, fun h => endR_fragB a (fun _ hL => hL) e h⟩

/-- **The program form**: every body of the program lies in the call fragment iff the program check passes on a
    complete enumeration of its functions. -/
theorem programmRB_iff {P : Programm D} (a : D.Lock → Bool) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs) :
    (∀ g : D.Fn, EndR (fun L => a L = true) (fun _ => True) (P.rumpf g)) ↔ programmRB P a fs = true := by
  constructor
  · intro h
    unfold programmRB
    exact List.all_eq_true.mpr fun g _ => (endRB_iff a (P.rumpf g)).mp (h g)
  · exact endR_programmRB a (fun _ hL => hL) hvoll

/-- A program that passes the check has no foreign call. -/
theorem fremdFrei_programmRB {P : Programm D} (a : D.Lock → Bool) {fs : List D.Fn} (hvoll : ∀ g : D.Fn, g ∈ fs)
    (h : programmRB P a fs = true) : FremdFrei P :=
  fremdFrei_endR (A := fun L => a L = true) (C := fun _ => True) ((programmRB_iff a hvoll).mpr h)

#print axioms endRB_iff
#print axioms programmRB_iff

end Gabbro.Stage0.Senke.BildLauf
