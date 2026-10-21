/-
  File:      Grammatik/Gen/Erzeuger/Kompakt/Gleich.lean
  Subject:   WHEN A TERM STANDS FOR ANOTHER. Arguments, results, statements, blocks, end blocks and arms are seen by the
             cells only through what the summary of a body reads (`Rumpf.schluessel`): the calls, indirect calls and lock
             takes (`mS` for every feature), the fragment (`gOk`), the answer sites (`ants`), the registers read
             (`regs`) and the carriers read (`koerperS`). `GlS s' s` says `s'` agrees with `s` on all of them and is not
             larger; likewise `GlB`, `GlN`, `GlArms`, `GlGArms`, and for argument lists and results the carriers read.
             An end block that stands for a body has the body's summary (`schluessel_of_glN`).
-/
import Grammatik.Gen.Erzeuger.Kompakt.AusdruckTab
import Grammatik.Gen.Abdeckung.Satz.KoerperOrte

namespace Gabbro.Grammatik.Gen

set_option linter.unusedSectionVars false

open Gabbro.Grammatik

variable {D : Deklaration} {V : Vertrag D} {l : Bool} {Γ : Ctx} {Λ : List (Res D)}

/-- `a'` stands for the argument list `a`. -/
structure GlArgs [Aufz D] [Zahlen] {τs : List Ty} (a' a : Args D Γ Λ τs) : Prop where
  orte : ∀ c, c ∈ a'.orte ↔ c ∈ a.orte
  groesse : groesseArgs a' ≤ groesseArgs a

/-- `a'` stands for the result `a`. -/
structure GlErg [Aufz D] [Zahlen] {o : Option Ty} (a' a : ErgExpr D Γ Λ o) : Prop where
  orte : ∀ c, c ∈ a'.orte ↔ c ∈ a.orte
  groesse : groesseErg a' ≤ groesseErg a

/-- `s'` stands for the statement `s`. -/
structure GlS [Aufz D] [Zahlen] {Λ' : List (Res D)} (s' s : Stmt D V l Γ Λ Λ') : Prop where
  m : ∀ A : Merkmal D, mS A s' = mS A s
  g : ∀ K Rg, s'.gOk K Rg = s.gOk K Rg
  ant : ∀ x, x ∈ s'.ants ↔ x ∈ s.ants
  r : ∀ x, x ∈ s'.regs ↔ x ∈ s.regs
  o : ∀ c, c ∈ koerperS s' ↔ c ∈ koerperS s
  groesse : groesseStmt s' ≤ groesseStmt s

/-- `b'` stands for the block `b`. -/
structure GlB [Aufz D] [Zahlen] {Λ' : List (Res D)} (b' b : Block D V l Γ Λ Λ') : Prop where
  m : ∀ A : Merkmal D, mB A b' = mB A b
  g : ∀ K Rg, b'.gOk K Rg = b.gOk K Rg
  ant : ∀ x, x ∈ b'.ants ↔ x ∈ b.ants
  r : ∀ x, x ∈ b'.regs ↔ x ∈ b.regs
  o : ∀ c, c ∈ koerperB b' ↔ c ∈ koerperB b
  groesse : groesseBlock b' ≤ groesseBlock b

/-- `e'` stands for the end block `e`. -/
structure GlN [Aufz D] [Zahlen] (e' e : Endblock D V l Γ Λ) : Prop where
  m : ∀ A : Merkmal D, mE A e' = mE A e
  g : ∀ K Rg, e'.gOk K Rg = e.gOk K Rg
  ant : ∀ x, x ∈ e'.ants ↔ x ∈ e.ants
  r : ∀ x, x ∈ e'.regs ↔ x ∈ e.regs
  o : ∀ c, c ∈ koerperE e' ↔ c ∈ koerperE e
  groesse : groesseEnd e' ≤ groesseEnd e

/-- `a'` stands for the arms `a`. -/
structure GlArms [Aufz D] [Zahlen] {Λ' : List (Res D)} {cs : List (Option (Int × Int))} (a' a : Arms D V l Γ Λ Λ' cs) :
    Prop where
  m : ∀ A : Merkmal D, mArms A a' = mArms A a
  g : ∀ K Rg, a'.gOk K Rg = a.gOk K Rg
  ant : ∀ x, x ∈ a'.ants ↔ x ∈ a.ants
  r : ∀ x, x ∈ a'.regs ↔ x ∈ a.regs
  o : ∀ c, c ∈ koerperArms a' ↔ c ∈ koerperArms a
  groesse : groesseArms a' ≤ groesseArms a

/-- `a'` stands for the reason arms `a`. -/
structure GlGArms [Aufz D] [Zahlen] {Λ' : List (Res D)} {n : Nat} (a' a : GrundArms D V l Γ Λ Λ' n) : Prop where
  m : ∀ A : Merkmal D, mGArms A a' = mGArms A a
  g : ∀ K Rg, a'.gOk K Rg = a.gOk K Rg
  ant : ∀ x, x ∈ a'.ants ↔ x ∈ a.ants
  r : ∀ x, x ∈ a'.regs ↔ x ∈ a.regs
  o : ∀ c, c ∈ koerperGArms a' ↔ c ∈ koerperGArms a
  groesse : groesseGrundArms a' ≤ groesseGrundArms a

variable [Aufz D] [Zahlen]

theorem GlS.refl {Λ' : List (Res D)} (s : Stmt D V l Γ Λ Λ') : GlS s s :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, Nat.le_refl _⟩
theorem GlB.refl {Λ' : List (Res D)} (b : Block D V l Γ Λ Λ') : GlB b b :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, Nat.le_refl _⟩
theorem GlN.refl (e : Endblock D V l Γ Λ) : GlN e e :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ => Iff.rfl, Nat.le_refl _⟩

theorem GlB.trans {Λ' : List (Res D)} {a b c : Block D V l Γ Λ Λ'} (h1 : GlB a b) (h2 : GlB b c) : GlB a c :=
  ⟨fun A => (h1.m A).trans (h2.m A), fun K R => (h1.g K R).trans (h2.g K R), fun x => (h1.ant x).trans (h2.ant x),
    fun x => (h1.r x).trans (h2.r x), fun x => (h1.o x).trans (h2.o x), Nat.le_trans h1.groesse h2.groesse⟩
theorem GlS.trans {Λ' : List (Res D)} {a b c : Stmt D V l Γ Λ Λ'} (h1 : GlS a b) (h2 : GlS b c) : GlS a c :=
  ⟨fun A => (h1.m A).trans (h2.m A), fun K R => (h1.g K R).trans (h2.g K R), fun x => (h1.ant x).trans (h2.ant x),
    fun x => (h1.r x).trans (h2.r x), fun x => (h1.o x).trans (h2.o x), Nat.le_trans h1.groesse h2.groesse⟩
theorem GlN.trans {a b c : Endblock D V l Γ Λ} (h1 : GlN a b) (h2 : GlN b c) : GlN a c :=
  ⟨fun A => (h1.m A).trans (h2.m A), fun K R => (h1.g K R).trans (h2.g K R), fun x => (h1.ant x).trans (h2.ant x),
    fun x => (h1.r x).trans (h2.r x), fun x => (h1.o x).trans (h2.o x), Nat.le_trans h1.groesse h2.groesse⟩

/-- **An end block that stands for a body has the body's summary.** -/
theorem schluessel_of_glN {f : D.Fn} {b' b : Rumpf D f} (h : GlN b' b) : Rumpf.schluessel b' = Rumpf.schluessel b := by
  simp only [Rumpf.schluessel, h.m, h.g]
  congr 1
  · congr 1; funext a; exact decide_eq_decide.2 (h.ant _)
  congr 1
  · congr 1; funext r; exact decide_eq_decide.2 (h.ant _)
  congr 1
  · congr 1; funext r; exact decide_eq_decide.2 (h.r _)
  · congr 1; funext c
    exact Bool.eq_iff_iff.2 (by rw [istIn_iff, istIn_iff]; exact h.o c)

end Gabbro.Grammatik.Gen
