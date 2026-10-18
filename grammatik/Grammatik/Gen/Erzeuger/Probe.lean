/-
  File:      Grammatik/Gen/Erzeuger/Probe.lean
  Subject:   WITNESSES and a PLANTED DEFECT for the generator and its completeness.

  `probeD` is a small concrete declaration (one table with a counted field, one static, one function, no lock) with
  complete enumerations (`probeA`). On it:

  * the generator is NOT EMPTY: the stream of the expressions of size 2 holds a literal, a negation, a table slot,
    and the theorem (`genE_vollst`) puts a concrete term into the bucket of its size;
  * the PLANTED DEFECT `exprSOhneNeg` is the clause list with the clause of `neg` removed: the same concrete term is
    NOT in the table it builds (decided by the kernel on the head constructors), so a bounded instance of
    completeness FAILS for a generator that skips a constructor -- the theorem is not vacuous;
  * a concrete valid skeleton is accepted by the checker's Bool (decided) and generated at its size; the same program
    with one root declared twice is refused by exactly component 6 (decided) and generated under that label.
-/
import Grammatik.Gen.Erzeuger.Gueltig

namespace Gabbro.Grammatik.Gen

open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz

/-- The probe's one function signature: no parameters, no result, no channel, writes everything. -/
def probeSig : Signatur Unit Unit Empty Empty where
  params := []
  erg := none
  gruende := 0
  haelt := []
  schreibt := fun _ => true
  gschreibt := fun _ => true
  konsumiert := []
  produziert := []

/-- The probe declaration: `Tab = Unit` (count 2, one field `0 .. 3`), `Glob = Unit` (`0 .. 1`),
    `Fn = Unit`; locks, marks, invariants, axioms, registers are empty. -/
def probeD : Deklaration where
  Tab := Unit
  decTab := inferInstance
  count := fun _ => 2
  Feld := fun _ => Unit
  decFeld := fun _ => inferInstance
  typ := fun _ _ => .int 0 3
  erlaubt := fun _ _ _ _ => false
  tabNr := fun | 0 => some () | _ => none
  Glob := Unit
  decGlob := inferInstance
  gtyp := fun _ => .int 0 1
  nutzlast := fun _ => []
  atomar := fun _ => false
  geteilt := fun _ => false
  ggeteilt := fun _ => false
  Lock := Empty
  decLock := inferInstance
  rang := fun e => nomatch e
  maskiert := fun e => nomatch e
  Marke := Empty
  decMarke := inferInstance
  stufen := fun e => nomatch e
  braucht := fun _ => []
  gbraucht := fun _ => []
  eigner := fun _ => []
  Fn := Unit
  sig := fun _ => 0
  sigNr := fun _ => probeSig
  eigner_nie_erzeugt := fun _ _ _ _ h => by simp at h
  Inv := Empty
  traeger := fun e => nomatch e
  invs := []
  Ax := Empty
  aparams := fun e => nomatch e
  aerg := fun e => nomatch e
  aschreibt := fun e => nomatch e
  agschreibt := fun e => nomatch e
  Reg := Empty
  rtyp := fun e => nomatch e
  rklasse := fun e => nomatch e
  spiegel := fun e => nomatch e
  rzusage := fun e => nomatch e
  Annahme := Unit
  a10 := ()
  geteilt_bewacht := fun _ h => by simp at h
  invarianten_gehalten := fun _ i => nomatch i
  ggeteilt_bewacht := fun _ h => by simp at h

/-- Complete enumerations of the probe. -/
instance probeA : Aufz probeD where
  tab := [()]
  tab_mem := fun _ => List.mem_singleton.2 rfl
  feld := fun _ => [()]
  feld_mem := fun _ _ => List.mem_singleton.2 rfl
  glob := [()]
  glob_mem := fun _ => List.mem_singleton.2 rfl
  lock := []
  lock_mem := fun e => nomatch e
  marke := []
  marke_mem := fun e => nomatch e
  fn := [()]
  fn_mem := fun _ => List.mem_singleton.2 rfl
  inv := []
  inv_mem := fun e => nomatch e
  ax := []
  ax_mem := fun e => nomatch e
  reg := []
  reg_mem := fun e => nomatch e
  annahme := [()]
  annahme_mem := fun _ => List.mem_singleton.2 rfl
  decFn := inferInstanceAs (DecidableEq Unit)
  decInv := fun e => nomatch e
  decAx := fun e => nomatch e
  decReg := fun e => nomatch e
  decAnnahme := inferInstanceAs (DecidableEq Unit)


/-- The numeric scheme of the witnesses: numbers by magnitude up to 3. -/
instance probeZ : Zahlen := Zahlen.exakt 3

/-- Is the head constructor `neg`? -/
def istNeg {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} : Expr D Γ Λ τ → Bool
  | .neg _ => true
  | _ => false

/-- Is the head constructor a literal? -/
def istLit {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} : Expr D Γ Λ τ → Bool
  | .lit _ => true
  | _ => false

/-- The head constructor is `slot`? -/
def istSlot {D : Deklaration} {Γ : Ctx} {Λ : List (Res D)} {τ : Ty} : Expr D Γ Λ τ → Bool
  | .slot .. => true
  | _ => false

/-! ## The generator is not empty, and the theorem puts a concrete term into it -/

/-- A literal, a negation, a table slot are generated at the sizes they have (decided by the kernel). -/
example : ((tab (genE (D := probeD) 3 3 [] []) 1).any fun p => istLit p.2) = true := by decide +kernel
example : ((tab (genE (D := probeD) 3 3 [] []) 2).any fun p => istNeg p.2) = true := by decide +kernel
example : ((tab (genE (D := probeD) 4 4 [] []) 4).any fun p => istSlot p.2) = true := by decide +kernel

/-- The concrete term `-0` (size 2) is in the bucket of size 2 -- from the completeness theorem. -/
example : (⟨_, Expr.neg (Expr.lit 0)⟩ : SE probeD [] []) ∈ tab (genE 2 2 [] []) 2 :=
  genE_vollst 2 2 [] [] _ _ (by decide) (by decide) (by decide)

/-! ## The planted defect: a generator that skips the constructor `neg` -/

/-- `exprS` without the clause of `neg`. -/
def exprSOhneNeg {D : Deklaration} [Aufz D] [Zahlen] {Γ : Ctx} {Λ : List (Res D)}
    (Q : (Γ' : Ctx) → Nat → Sz (SE D Γ' Λ)) (E : Sz (SE D Γ Λ)) : Sz (SE D Γ Λ) :=
  Sz.alle [gLit, gBool, gVar Γ, gGlob, gSlot E, gThru E, gPtrOf, gFnref, gOldG, gOldS E, gWiden E, gAdd E,
    gSub E, gMul E, gDiv E, gRem E, gSdiv E, gSrem E, gGetBytes E, gBand E, gBor E, gBxor E, gShl E,
    gShr E, gLt E, gLe E, gEq E, gFllt E, gFlle E, gAnd E, gOr E, gNot E, gNone, gSome E, gIstSome E, gCase E,
    gWhy, gForall Q, gExists Q, gReaches E]

/-- The defective table of the expressions (bucket `k` from `exprSOhneNeg`). -/
def genEOhneNeg {D : Deklaration} [Aufz D] [Zahlen] : Nat → Nat → (Γ : Ctx) → (Λ : List (Res D)) →
    List (List (SE D Γ Λ))
  | 0, n, _, _ => List.replicate (n + 1) []
  | f + 1, n, Γ, Λ => buckets [] (fun prev k => exprSOhneNeg (fun Γ' j => tab (genEOhneNeg f j Γ' Λ)) (tab prev) k) n

/-- The defective generator never produces a `neg` (decided by the kernel on the probe). -/
theorem ohneNeg_keine_neg : ((tab (genEOhneNeg (D := probeD) 3 3 [] []) 2).any fun p => istNeg p.2) = false := by
  decide +kernel

/-- **The bounded instance of completeness FAILS for the defective generator**: `-0` has size 2 and is not in the
    bucket of size 2 -- whereas the real generator contains it (`example` above). -/
theorem defekt_luecke : (⟨_, Expr.neg (Expr.lit 0)⟩ : SE probeD [] []) ∉ tab (genEOhneNeg 3 3 [] []) 2 := by
  intro h
  have h1 : ((tab (genEOhneNeg (D := probeD) 3 3 [] []) 2).any fun p => istNeg p.2) = true :=
    List.any_eq_true.2 ⟨_, h, rfl⟩
  rw [ohneNeg_keine_neg] at h1
  exact Bool.false_ne_true h1

/-! ## A valid skeleton, and the theorems' instances on it -/

/-- The skeleton of the probe: the one body is `return;`, no handler. -/
def probeH : Haut probeD where
  rumpf := fun _ => .ret .empty (List.Perm.refl [])
  unterbricht := fun _ => false

/-- No lock family (there is no lock). -/
def probeS : SperrInv probeD where
  orte := fun e => nomatch e
  inv := fun e => nomatch e

/-- The probe program is accepted by the checker's Bool (decided by the kernel). -/
theorem probeH_gueltig : AkzeptiertX probeH.programm probeS [()] [] [.inl (), .inr ()] [()] = true := by
  decide +kernel

/-- **(C) at a concrete valid program**: it is generated at its size. -/
theorem probeH_erzeugt : probeH.programm ∈ genGueltig probeS [()] [] [.inl (), .inr ()] [()] 3 (groesseHaut probeH) :=
  gueltig_vollst (fun _ => List.mem_singleton.2 rfl) probeH probeH_gueltig (fun f => by cases f; decide) (fun f => by cases f; decide)

/-- The same program with ONE root declared twice (`ws = [(), ()]`) is refused by exactly component 6 (the
    single-pool component: a start declared once running on several threads), accepted by the other nine. -/
theorem probeH_nur_an_6 : NurAn 6 probeH.programm probeS [()] [] [.inl (), .inr ()] [(), ()] := by
  unfold NurAn
  decide +kernel

/-- **(C) for a single-fault refusal**: it is generated at its size, under its label. -/
theorem probeH_bad_erzeugt :
    probeH.programm ∈ genBad 6 probeS [()] [] [.inl (), .inr ()] [(), ()] 3 (groesseHaut probeH) :=
  bad_vollst (fun _ => List.mem_singleton.2 rfl) probeH probeH_nur_an_6 (fun f => by cases f; decide) (fun f => by cases f; decide)

end Gabbro.Grammatik.Gen
