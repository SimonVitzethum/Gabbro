/-
  File:      Grammatik/Adaequanz/Gabbro/Zaehlung.lean
  Subject:   THE COUNT FOR GABBRO, as far as it is mechanical: the context dimensions of the checker read off the
             model (`Akzeptiert.lean`, `Syntax.lean`), their sizes per declaration of the family (`Gen/Familie`),
             and the number of PROGRAM-ROOT cells that Theorem 2a (`wurzel_schranke`) demands as separate test
             programs from every set sufficient for implementations with one state more than the presentation.

  THE DIMENSIONS (sources in brackets; written out in CHECKER.md section 16):
    inherited  l      loop flag                          2                 [`Stmt l`, `Block true` in loops]
               Λ      held locks x held mark stages      2^L * (b+1)^K     [`Res.held`, `Res.marke`, `Stmt.locks`]
               V      the enclosing contract             F                 [`Vertrag`, `vertragVon`]
    synthesized τ     the type of an expression          |types|           [`Expr Γ Λ τ`]
               Λ'     held set after a statement         as Λ              [`Stmt l Γ Λ Λ'`]
               calls  direct callees, signatures         2^F * 2^S         [`mE`.ruf/.ind: `reachB`, `abgB`, `kandB`]
               locks  locks taken                        2^L               [`mE`.sperre: `bodenM`, `NurMaskiert`]
               reads  carriers read                      2^(T+G)           [`endblockOrteP`, `fussOrte`]
               regs   registers read                     2^R               [`regs`, `fussOrteG`]
               ants   answer sites                       2^(A+R)           [`ants`, `antwortenB`]
               frag   in the replay fragment             2                 [`gOk`, `programmImFragmentG`]
  Names are resolved (a variable is its type: hypothesis H-names); numbers live in the family's alphabet
  (H-data); a mark stage is held at most `b` times (H-mult).

  The root of a program reads, per function, `requires` and `ensures` (a Bool expression in a FIXED context,
  so its state is its carriers read, or refused) and the body (an end block in a fixed context: its summary, or
  refused); per invariant its predicate; per function the handler flag. A presentation state per root child is
  its synthesized value or `refused`, so the root cells are the product (`wurzelZellen`).
-/
import Grammatik.Gen.Familie.Familie

namespace Gabbro.Grammatik.Adaequanz.GabbroZahl

open Gabbro.Grammatik.Gen

/-- The measures of a declaration the dimensions read. -/
structure Masse where
  tab : Nat
  glob : Nat
  lock : Nat
  fn : Nat
  sig : Nat
  ax : Nat
  reg : Nat
  inv : Nat
  /-- the number of (mark, stage) pairs -/
  stufen : Nat
  /-- the bound `b` on how often one (mark, stage) pair is held (hypothesis H-mult) -/
  mult : Nat := 1

/-- The measures of a member of the family. -/
def masseVon (z : Spez) : Masse where
  tab := z.tabs.length
  glob := z.globs.length
  lock := z.locks.length
  fn := z.fns.length
  sig := z.sigs.length
  ax := z.axs.length
  reg := z.regs.length
  inv := z.invs.length
  stufen := z.marken.sum

/-- Held resources `Λ`. -/
def lam (d : Masse) : Nat := 2 ^ d.lock * (d.mult + 1) ^ d.stufen

/-- The summary of a body: callees, signatures, locks taken, carriers read, registers, answer sites, fragment. -/
def summe (d : Masse) : Nat :=
  2 ^ d.fn * 2 ^ d.sig * 2 ^ d.lock * 2 ^ (d.tab + d.glob) * 2 ^ d.reg * 2 ^ (d.ax + d.reg) * 2

/-- Inherited context of a statement, a block, an end block. -/
def inhStmt (d : Masse) : Nat := 2 * lam d * d.fn

/-- Synthesized value of a statement or block. -/
def synStmt (d : Masse) : Nat := lam d * summe d

/-- Synthesized value of an expression of a given number of types. -/
def synExpr (d : Masse) (typen : Nat) : Nat := typen * 2 ^ (d.tab + d.glob)

/-- Presentation states of a statement subtree (bottom-up: a function from the inherited context to the
    synthesized value or `refused`). An upper bound on the Myhill-Nerode index. -/
def zustStmt (d : Masse) : Nat := (synStmt d + 1) ^ inhStmt d

/-- **The program-root cells**: per function `requires`, `ensures` (carriers read, or refused) and the body
    (summary, or refused), per invariant its predicate, per function the handler flag. -/
def wurzelZellen (d : Masse) : Nat :=
  2 ^ d.fn * ((2 ^ (d.tab + d.glob) + 1) ^ 2 * (summe d + 1)) ^ d.fn * (2 ^ (d.tab + d.glob) + 1) ^ d.inv

/-- z0 (one table, one static, one function): 1 650 root cells. -/
theorem wurzel_z0 : wurzelZellen (masseVon z0) = 1650 := by decide

/-- z1 (locks: two locks, two functions): 657 922 500 root cells. -/
theorem wurzel_z1 : wurzelZellen (masseVon z1) = 657922500 := by decide

/-- The root cells of every member of the family. -/
def wurzelFamilie : List Nat := familie.map fun z => wurzelZellen (masseVon z)

/-! ## The pattern cells of the ten components (Theorem 4, hypothesis H7)

    Each component of `AkzeptiertX` is a conjunction, over tuples of functions, carriers and locks, of a
    quantifier-free kernel; a pattern cell is an assignment to the atoms that kernel reads. The atoms, read off
    the definitions in `Akzeptiert.lean` and `AtomarAkzeptiert.lean`:

    0 `programmImFragmentG` (f, g, c): `gOk f`, f calls through `sig g`, `c` a contract carrier of `g`, `c ∈ fussOrteG f`
    1 `abgAlleB` (w, f, g): `reach w f`, `f` calls `g`, `reach w g`
    2 `fussWXB` (f, c, L, w1, w2, f', g): `c ∈ fussOrte f`, `sigB f c`, `L` guards `c`, `c ∈ S.orte L`, `c` atomic,
      `c` vertragsfrei, `w1 = w2`, `w1` declared twice, `reach w1 f'`, `c ∈ fuss f'`, `reach w2 g`, `g` writes `c`
    3 `stufenB` (f, L): `f` takes `L`, `boden f ≤ rang L`
    4 `sperrOrteB` (L, c): `c ∈ S.orte L`, `L` guards `c`
    5 `wurzelnB` (w): `haelt w = []`, `gruende w = 0`
    6 `einzelnPoolB` (w, f, c): `w` twice, `haelt w = []`, `gruende w = 0`, `reach w f`, `f` writes `c`, `c` guarded,
      `c` atomic
    7 `rennB` (c, w1, w2, f, g): `c` guarded, `c` atomic, `w1 = w2`, `w1` twice, `reach w1 f`, `f` writes `c`,
      `reach w2 g`, `g` writes `c`
    8 `antwortenB` (f, x): `x` an answer site of `f`, `x` an axiom `-> never`, the answer type has a value
    9 `maskenB` (w, f, L): `w` a handler, `reach w f`, `f` takes `L`, `L` masks irqs -/

/-- The number of atoms of each component's kernel. -/
def atome : List Nat := [4, 3, 12, 2, 2, 2, 7, 8, 3, 4]

/-- At most `Σ 2^atoms` pattern cells (an upper bound: not every assignment is consistent). -/
def musterZellen : Nat := (atome.map fun a => 2 ^ a).sum

theorem musterZellen_wert : musterZellen = 4540 := by decide

end Gabbro.Grammatik.Adaequanz.GabbroZahl
