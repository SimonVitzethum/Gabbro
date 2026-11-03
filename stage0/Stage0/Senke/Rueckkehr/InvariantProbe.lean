/- Non-degenerate global-only and mixed-carrier epilogue fixtures. -/
module
public import Stage0.Senke.Images.BildLese
public import Grammatik.Proben.InvGlobalZeuge
@[expose] public section

namespace Gabbro.Stage0.Senke.InvariantProbe
open Gabbro.Grammatik Runner.IR Runner.Mem
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Both predicates are owed by the global-only writer; the mixed group has two guards. -/
def D (mixed : Bool) : Deklaration := { cgD with
  Inv := Bool
  traeger := fun _ => if mixed then [.inl (), .inr ()] else [.inr ()]
  invs := [false, true]
  invarianten_gehalten := by
    intro n i owed c member lock held
    cases lock <;> decide }

def globalAccess (mixed i : Bool) : gdarf (D mixed) () (invSicht (D mixed) i) := by
  intro w hw
  cases mixed <;> simp_all [D, invSicht, cgD, Res.von]

def tableAccess (i : Bool) : darf (D true) () (invSicht (D true) i) := by
  intro w hw
  simp_all [D, invSicht, cgD, Res.von]

def predicate : (mixed : Bool) → Bool → Expr (D mixed) [] (invSicht (D mixed) false) .bool
  | false, _ => .eq (.glob () (globalAccess false false)) (.lit 0)
  | true, _ => .eq (.glob () (globalAccess true false))
      (.slot () () (.widen (by decide) (by decide) (.lit 0)) (tableAccess false))

def postAccess (mixed : Bool) (f : (D mixed).Fn) :
    gdarf (D mixed) () (vertragVon (D mixed) f).ende := by
  intro w hw
  cases f <;> simp_all [D, cgD, cgSig, vertragVon, Vertrag.vonSig, Vertrag.ende,
    Deklaration.signatur, Res.von]

def program (mixed : Bool) : Programm (D mixed) where
  invariante i := by
    have sight : invSicht (D mixed) i = invSicht (D mixed) false := rfl
    rw [sight]
    exact predicate mixed i
  requires _ := .tru
  ensures f := .eq (.oldG () (postAccess mixed f)) (.glob () (postAccess mixed f))
  rumpf f := match f with
    | .nurGlob =>
      .cons (.assignGlob () (.widen (by decide) (by decide) (.lit 1))
          (by decide) (postAccess mixed CgFn.nurGlob))
        (.cons (.assignGlob () (.widen (by decide) (by decide) (.lit 0))
            (by decide) (postAccess mixed CgFn.nurGlob))
          (.ret .empty (.refl _)))
    | .nurTab | .frei => .ret .empty (.refl _)

def world (mixed : Bool) (global : Zahl 0 10) : World (D mixed) where
  slots _ _ _ := ⟨0, by decide, by decide⟩
  globs _ := global
  spur := []

def layout (mixed : Bool) : Lay (D mixed) where
  col _ _ := 16400
  ga _ := 16384
  lo := 16384
  hi := 16416
  tor a := nomatch a
  byte _ := none

def emitted (mixed : Bool) : List II × Nat :=
  (lowPost (layout mixed) (functionFrame (program mixed) CgFn.nurGlob)
    (program mixed) CgFn.nurGlob 6).getD ([], 0)

theorem lower (mixed : Bool) :
    lowPost (layout mixed) (functionFrame (program mixed) CgFn.nurGlob)
      (program mixed) CgFn.nurGlob 6 = some (emitted mixed) := by
  cases mixed <;> decide +kernel

def memory (code : List II) : Runner.Mem where
  b a := ((code.flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

theorem frame (code : List II) : FrameOK (memory code) 8192 32 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem lay (mixed : Bool) : LayIn (layout mixed) := by
  refine ⟨?_, ?_, by decide⟩
  · intro t field k hk
    change (k : Int) < 2 at hk
    change 16384 ≤ 16400 + 8 * k ∧ 16400 + 8 * k + 8 ≤ 16416
    omega
  · intro g
    exact ⟨by decide, by decide⟩

theorem represented [Kern] (mixed : Bool) :
    WeltAt (memory (emitted mixed).1) (layout mixed) (world mixed ⟨0, by decide, by decide⟩) := by
  refine ⟨?_, ?_, fun _ _ _ => rfl⟩
  · intro t field k hk
    have bound : k = 0 ∨ k = 1 := by change (k : Int) < 2 at hk; omega
    rcases bound with rfl | rfl <;> cases mixed <;>
      exact ValueAt.ofCellWord (w := 0) (by decide) (by decide +kernel) rfl
  · intro g
    cases mixed <;> exact ValueAt.ofCellWord (w := 0) (by decide) (by decide +kernel) rfl

theorem loaded (mixed : Bool) : CodeAt (memory (emitted mixed).1) 0 (emitted mixed).1 := by
  apply codeAt_bytes (emitted mixed).1 0 (by cases mixed <;> decide +kernel)
  intro i hi
  refine ⟨rfl, rfl, ?_⟩
  have lengthBound : ((emitted mixed).1.flatMap encII).length < 2 ^ 64 := by
    cases mixed <;> decide +kernel
  simp only [memory, Nat.zero_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), List.getElem?_eq_getElem hi, Option.getD_some]

theorem pre [Kern] (mixed : Bool) :
    PreS (layout mixed) (memory (emitted mixed).1) 0 8192 32 6 (emitted mixed).1
      (Env.nil : Env (D mixed) []) 1 := by
  refine ⟨by decide, by decide, frame _, loaded mixed, ?_, (fun _ x => nomatch x),
    trivial, wstab_true _ _⟩
  cases mixed <;> unfold CodeFar <;> decide +kernel

theorem snapshots [Kern] (mixed : Bool) :
    EntrySnapshots.At (layout mixed) (world mixed ⟨0, by decide, by decide⟩)
      (memory (emitted mixed).1) 8192 (oldCells ((program mixed).ensures CgFn.nurGlob)) 4 := by
  cases mixed <;>
    exact ⟨ValueAt.of_enc (w := 0) (by decide) (by decide +kernel) rfl, trivial⟩

/-- All simulation premises hold together, with a real old-global snapshot and two owed predicates. -/
theorem lowPost_ok_zeuge [Kern] (mixed : Bool) :
    schuldet (D := D mixed) CgFn.nurGlob false = true ∧
    schuldet (D := D mixed) CgFn.nurGlob true = true ∧
    ∃ m', Star ⟨0, 8192⟩ (memory (emitted mixed).1)
      ⟨BitVec.ofNat 64 (16 * (emitted mixed).1.length), 8192⟩ m' ∧
      Agree 8192 6 32 (memory (emitted mixed).1) m' := by
  refine ⟨by cases mixed <;> decide, by cases mixed <;> decide, ?_⟩
  have result := lowPost_ok (program mixed) CgFn.nurGlob
    (world mixed ⟨0, by decide, by decide⟩) (world mixed ⟨0, by decide, by decide⟩) .nil ()
    (lower mixed) (by cases mixed <;> decide +kernel) (by decide) (lay mixed) (by decide) (memory (emitted mixed).1) 0 (pre mixed)
    (represented mixed) (snapshots mixed)
  have noFault : returnFault (program mixed) CgFn.nurGlob
      (world mixed ⟨0, by decide, by decide⟩) (world mixed ⟨0, by decide, by decide⟩) .nil () = 0 := by
    cases mixed <;> decide +kernel
  simpa only [noFault, ne_eq, not_true_eq_false, if_false, BitVec.zero_add] using result

/-- Ensures failure wins over a simultaneously false invariant. -/
theorem ensures_first_zeuge :
    returnFault (program false) CgFn.nurGlob (world false ⟨0, by decide, by decide⟩)
      (world false ⟨1, by decide, by decide⟩) .nil () = 102 := by decide +kernel

/-- Equal entry/exit globals satisfy ensures; the first declaration is still the first failing group. -/
theorem first_failure_zeuge (mixed : Bool) :
    returnFault (program mixed) CgFn.nurGlob (world mixed ⟨1, by decide, by decide⟩)
      (world mixed ⟨1, by decide, by decide⟩) .nil () = 103 ∧
    owedFailure (program mixed) CgFn.nurGlob
      (owedWorld (program mixed) CgFn.nurGlob (world mixed ⟨1, by decide, by decide⟩)) = some false := by
  cases mixed <;> decide +kernel

/-- The actual function path accepts both carrier sets instead of rejecting every owed group. -/
theorem lowFun_zeuge (mixed : Bool) :
    (lowFun 1 (program mixed) (fun _ => 0) (layout mixed) CgFn.nurGlob).isSome = true := by
  cases mixed <;> decide +kernel

/-- Raw G invariants may contain old; their evaluation uses the current world. -/
def ordinaryOld : Programm (D false) := { program false with
  invariante := fun i => .eq (.oldG () (globalAccess false i)) (.lit 0) }

theorem ordinary_old_invariant_zeuge :
    (lowFunE 1 ordinaryOld (layout false) (fun _ => "global-writer")
      (fun _ => 0) CgFn.nurGlob).isOk = true := by
  decide +kernel

/-- A reason-capable declaration keeps the same owed global/mixed predicates. -/
def reasonD (mixed : Bool) : Deklaration := { D mixed with
  sigNr := fun n => { (D mixed).sigNr n with gruende := 1 }
  passt_ok := by
    intro f n h
    have same := of_decide_eq_true h
    subst n
    exact SigPasst.refl _ _ }

def reasonProgram (mixed : Bool) : Programm (reasonD mixed) where
  invariante _ := .fls
  requires _ := .tru
  ensures _ := .fls
  rumpf _ := .retWhy ⟨0, by decide⟩ (.refl _)

def reasonOracle (mixed : Bool) : Orakel (reasonD mixed) where
  wirkt a := nomatch a
  regLies r := nomatch r
  regSchreib r := nomatch r
  sichtbar _ _ := true

def reasonWorld (mixed : Bool) : World (reasonD mixed) where
  slots _ _ _ := ⟨0, by decide, by decide⟩
  globs _ := ⟨0, by decide, by decide⟩
  spur := []

/-- The runtime propagates a reason even when both ensures and owed predicates are false.
    Restoration on that path is the user's `InvGutGrundA` obligation. -/
theorem reason_bypasses_epilogue_zeuge (mixed : Bool) :
    schuldet (D := reasonD mixed) CgFn.nurGlob false = true ∧
    (match rufAt (reasonProgram mixed) (reasonOracle mixed) 1 1 CgFn.nurGlob
      (reasonWorld mixed) .nil with | .why _ r => r.val = 0 | _ => False) := by
  cases mixed <;> decide +kernel

end Gabbro.Stage0.Senke.InvariantProbe
