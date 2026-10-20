/-
  File:      Grammatik/ArenaBaumFormG.lean
  Subject:   THE GUARDED TREE FORMS (PLAN-DYNAMIC.md section 8a.1, third pass): the tree moves of `ArenaBaumForm.lean`
             need facts about the world that a recognizer cannot read off the names of the variables: that a child
             place is EMPTY (leaf in), that a child is a LEAF (leaf out), that the tree is empty (the first node goes in).
             Here the guard is part of the form, a `check` whose `else` branch the recognizer demands to be store-free
             (`Rein`), exactly as the `narrow` of a pop.

    `Block.haengen Cp Co p i voll rest`   =  `check Cp[p] == nil else voll;  Cp[i] = nil; Co[i] = nil; Cp[p] = i;  rest`
    `Block.abschneiden Lf Rf C p voll voll2 rest`
                                           =  `let i = C[p] else voll;  check Lf[i] == nil && Rf[i] == nil else voll2;
                                              C[p] = nil;  rest`
    `Block.wurzelEin Lf Rf Wz x voll rest` =  `check root == nil else voll;  Lf[x] = nil; Rf[x] = nil; root = x;  rest`
    `Block.wurzelAus Lf Rf Wz voll voll2 rest`
                                           =  `let i = root else voll;  check Lf[i] == nil && Rf[i] == nil else voll2;
                                              root = nil;  rest`

  This file holds the forms, the two generic facts about `check`, what a guard says (`leerTest_wahr`, `blattTest_wahr`,
  `wurzelLeer_wahr`) and what the unguarded kernel of the root move leaves (`wurzelSetze_ausfuehren`); the invariant
  theorems on the executed forms are in `ArenaBaumFormZug.lean`.
-/
import Grammatik.Bausteine.Arena.Struktur.Formen.ArenaBaumForm
import Grammatik.Bausteine.Arena.Struktur.ArenaBaumWurzel

namespace Gabbro.Grammatik

open Gabbro.Grammatik.ArenaDyn Gabbro.Grammatik.ArenaKette

variable {D : Deklaration}

namespace Block
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable {A : FreiForm D}

/-- The test `C[p] == nil`: the child place `C` of `p` is empty. -/
def leerTest (C : LinkFeld A) (p : Var Γ (Ty.index (D.count A.tab))) (hLT : darf D A.tab Λ) : Expr D Γ Λ .bool :=
  Expr.eq (Expr.umTyp C.hf (Expr.slot A.tab C.f (Expr.var p) hLT)) (Expr.lit (D.count A.tab))

/-- The test "`i` is a leaf": both child places empty. -/
def blattTest (Lf Rf : LinkFeld A) (i : Var Γ (Ty.index (D.count A.tab))) (hLT : darf D A.tab Λ) :
    Expr D Γ Λ .bool :=
  Expr.and (leerTest Lf i hLT) (leerTest Rf i hLT)

/-- The test `root == nil`: the tree is empty. -/
def wurzelLeerTest (Wz : LinkKopf A) (hLG : gdarf D Wz.g Λ) : Expr D Γ Λ .bool :=
  Expr.eq (Expr.umTyp Wz.hg (Expr.glob Wz.g hLG)) (Expr.lit (D.count A.tab))

/-- The nil marker `count`, at the root global's declared type. -/
def linkNilKopf (Wz : LinkKopf A) : Expr D Γ Λ (D.gtyp Wz.g) :=
  Expr.umTyp Wz.hg.symm
    (Expr.widen (lo := D.count A.tab) (hi := D.count A.tab) (lo' := 0) (hi' := D.count A.tab)
      (by have := A.hpos; omega) (Int.le_refl _) (Expr.lit (D.count A.tab)))

/-- **`check Cp[p] == nil else voll;  Cp[i] = nil; Co[i] = nil; Cp[p] = i;  rest`** -- hang `i` below `p`. -/
def haengen (Cp Co : LinkFeld A) (p i : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l Γ Λ Λ') : Block D V l Γ Λ Λ' :=
  .check (leerTest Cp p hLT) voll (blattEin Cp Co p i hwT hLT rest)

/-- **`let i = C[p] else voll;  check leaf(i) else voll2;  C[p] = nil;  rest`** -- cut the leaf child off `p`. -/
def abschneiden (Lf Rf C : LinkFeld A) (p : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
    (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') : Block D V l Γ Λ Λ' :=
  .narrow (Expr.umTyp C.hf (Expr.slot A.tab C.f (Expr.var p) hLT)) 0 (D.count A.tab - 1) voll
    (.check (blattTest Lf Rf .here hLT) voll2
      (.cons (.assignSlot A.tab C.f (Expr.var (.there p)) (linkNil C) hwT hLT) rest))

/-- The three stores that make `x` the root of an empty tree: no children, then the root word. -/
def wurzelSetze (Lf Rf : LinkFeld A) (Wz : LinkKopf A) (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt Wz.g = true) (hLG : gdarf D Wz.g Λ) (rest : Block D V l Γ Λ Λ') : Block D V l Γ Λ Λ' :=
  .cons (.assignSlot A.tab Lf.f (Expr.var x) (linkNil Lf) hwT hLT)
    (.cons (.assignSlot A.tab Rf.f (Expr.var x) (linkNil Rf) hwT hLT)
      (.cons (.assignGlob Wz.g (linkIdxAlsKopf Wz x) hwG hLG) rest))

/-- **`check root == nil else voll;  Lf[x] = nil; Rf[x] = nil; root = x;  rest`** -- the first node. -/
def wurzelEin (Lf Rf : LinkFeld A) (Wz : LinkKopf A) (x : Var Γ (Ty.index (D.count A.tab)))
    (hwT : V.schreibt A.tab = true) (hLT : darf D A.tab Λ)
    (hwG : V.gschreibt Wz.g = true) (hLG : gdarf D Wz.g Λ) (voll : Endblock D V l Γ Λ)
    (rest : Block D V l Γ Λ Λ') : Block D V l Γ Λ Λ' :=
  .check (wurzelLeerTest Wz hLG) voll (wurzelSetze Lf Rf Wz x hwT hLT hwG hLG rest)

/-- **`let i = root else voll;  check leaf(i) else voll2;  root = nil;  rest`** -- the root goes, a leaf. -/
def wurzelAus (Lf Rf : LinkFeld A) (Wz : LinkKopf A)
    (hwG : V.gschreibt Wz.g = true) (hLG : gdarf D Wz.g Λ) (hLT : darf D A.tab Λ) (voll : Endblock D V l Γ Λ)
    (voll2 : Endblock D V l (Ty.index (D.count A.tab) :: Γ) Λ)
    (rest : Block D V l (Ty.index (D.count A.tab) :: Γ) Λ Λ') : Block D V l Γ Λ Λ' :=
  .narrow (Expr.umTyp Wz.hg (Expr.glob Wz.g hLG)) 0 (D.count A.tab - 1) voll
    (.check (blattTest Lf Rf .here hLT) voll2 (.cons (.assignGlob Wz.g (linkNilKopf Wz) hwG hLG) rest))

end Block

section Bedeutung
variable (O : Orakel D) (passes : Nat)
variable {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ Λ' : List (Res D)}
variable (R : ∀ f : D.Fn, World D → Env D (D.params f) → RufAusgang f)
variable {A : FreiForm D}

/-! ## 1. A `check` runs on, or takes its `else` -/

theorem execBlock_check_wahr (c : Expr D Γ Λ .bool) (voll : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    execBlock (V := V) O passes R (.check c voll rest) σ ρ = execBlock (V := V) O passes R rest (σ.lese Λ c.orte) ρ := by
  simp only [execBlock]
  rw [if_pos h]

theorem execBlock_check_falsch (c : Expr D Γ Λ .bool) (voll : Endblock D V l Γ Λ) (rest : Block D V l Γ Λ Λ')
    (σ : World D) (ρ : Env D Γ) (h : ¬ wahr? (eval (σ.lese Λ c.orte) c (σ.lese Λ c.orte) ρ) = true) :
    execBlock (V := V) O passes R (.check c voll rest) σ ρ
      = (execEnd O passes R voll (σ.lese Λ c.orte) ρ).zuAusgang := by
  simp only [execBlock]
  rw [if_neg h]

/-! ## 2. What a guard says -/

theorem leerTest_wahr (C : LinkFeld A) (p : Var Γ (Ty.index (D.count A.tab))) (hLT : darf D A.tab Λ)
    (s : World D) (ρ : Env D Γ) :
    wahr? (eval s (Block.leerTest C p hLT) s ρ) = true ↔ C.wert s (ρ.get p).n = D.count A.tab := by
  simp only [Block.leerTest, wahr?, eval, eval_umTyp, decide_eq_true_eq]
  exact Iff.rfl

theorem blattTest_wahr (Lf Rf : LinkFeld A) (i : Var Γ (Ty.index (D.count A.tab))) (hLT : darf D A.tab Λ)
    (s : World D) (ρ : Env D Γ) :
    wahr? (eval s (Block.blattTest Lf Rf i hLT) s ρ) = true ↔
      (Lf.wert s (ρ.get i).n = D.count A.tab ∧ Rf.wert s (ρ.get i).n = D.count A.tab) := by
  have h1 := leerTest_wahr (Γ := Γ) (Λ := Λ) Lf i hLT s ρ
  have h2 := leerTest_wahr (Γ := Γ) (Λ := Λ) Rf i hLT s ρ
  simp only [wahr?] at h1 h2
  rw [← h1, ← h2]
  simp only [Block.blattTest, eval, wahr?]
  cases eval s (Block.leerTest Lf i hLT) s ρ <;> cases eval s (Block.leerTest Rf i hLT) s ρ <;> simp

theorem wurzelLeer_wahr (Wz : LinkKopf A) (hLG : gdarf D Wz.g Λ) (s : World D) (ρ : Env D Γ) :
    wahr? (eval s (Block.wurzelLeerTest (Γ := Γ) Wz hLG) s ρ) = true ↔ Wz.st s = D.count A.tab := by
  simp only [Block.wurzelLeerTest, wahr?, eval, eval_umTyp, decide_eq_true_eq]
  exact Iff.rfl

end Bedeutung

end Gabbro.Grammatik
