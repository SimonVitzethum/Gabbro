/- C13 snapshot witness: the arithmetic operand reads entry 19, while the exit global is 3. -/
module
public import Stage0.Senke.Ausdruck.Old.Sound
public import Stage0.Senke.Ausdruck.Old.Source
public import Stage0.Senke.Welt.Anordnung
@[expose] public section

namespace Gabbro.Stage0.Senke.BuiltinOldProbe
open Gabbro.Grammatik Gabbro.Grammatik.Parser.Uebersetze
  Gabbro.Grammatik.Parser.UebersetzeAllg Runner.IR
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def unit : UProg := { tabs := [], locks := [], fns := [],
                      globs := [{name := "counter", ty := .int 0 255, init := 0}] }
abbrev D := declOf unit
abbrev global : D.Glob := ⟨0, by decide⟩

theorem access : gdarf D global [] := by intro w hw; change w ∈ [] at hw; cases hw

def expression : Expr D [] [] (.int 0 255) :=
  .intBuiltin2 (.addW 7) (.oldG global access) (.widen (by decide) (by decide) (.lit 250))

def world (n : Zahl 0 255) : World D where
  slots t := Fin.elim0 t
  globs g := by
    obtain ⟨g, hg⟩ := g
    have zero : g = 0 := by change g < 1 at hg; omega
    subst g
    exact n
  spur := []

def entry := world ⟨19, by decide, by decide⟩
def exitWorld := world ⟨3, by decide, by decide⟩

def layout : Lay D where
  col t := Fin.elim0 t
  ga _ := 131072
  lo := 131072
  hi := 131080
  tor a := Fin.elim0 a
  byte _ := none

def frameLayout : FrameLayout := ⟨[], none, 0, 1, 0⟩
def compiled : List II × Nat := (lowEns layout frameLayout expression 8).getD ([], 0)

theorem emitted : lowEns layout frameLayout expression 8 = some compiled ∧ compiled.2 ≤ 256 := by
  decide +kernel

def memory : Runner.Mem where
  b a := if a.toNat = 65568 then 19 else if a.toNat = 131072 then 3
    else ((compiled.1.flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

theorem bytes : BytesAt memory 0 (compiled.1.flatMap encII) := by
  intro i hi
  have size : (compiled.1.flatMap encII).length < 65536 := by decide +kernel
  have address : (BitVec.ofNat 64 i).toNat = i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨rfl, rfl, ?_⟩
  rw [Nat.zero_add]
  simp only [memory, address, if_neg (show i ≠ 65568 by omega),
    if_neg (show i ≠ 131072 by omega), List.getElem?_eq_getElem hi, Option.getD_some]

theorem pre [Kern] : PreS layout memory 0 65536 256 8 compiled.1 (Env.nil : Env D []) 1 := by
  refine ⟨by decide, by decide, ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩,
    codeAt_bytes compiled.1 0 (by decide +kernel) bytes, ?_, ?_, trivial, wstab_true _ _⟩
  · unfold CodeFar; decide +kernel
  · intro _ x; nomatch x

theorem lay : LayIn layout := by
  refine ⟨(fun t => Fin.elim0 t), ?_, by decide⟩
  intro g
  have same : g = global := by
    apply Fin.ext
    have bound := g.isLt
    change g.val < 1 at bound
    change g.val = 0
    omega
  subst same
  decide +kernel

theorem loaded [Kern] : WeltAt memory layout exitWorld := by
  refine ⟨(fun t => Fin.elim0 t), ?_, fun _ _ _ => rfl⟩
  intro g
  have same : g = global := by
    apply Fin.ext
    have bound := g.isLt
    change g.val < 1 at bound
    change g.val = 0
    omega
  subst same
  exact ValueAt.ofCellWord (w := 3) (by decide) (by decide +kernel) rfl

theorem saved : EntrySnapshots.At layout entry memory 65536 (oldCells expression) 4 := by
  exact ⟨ValueAt.of_enc (w := 19) (by decide) (by decide +kernel) rfl, trivial⟩

/-- The postcondition proof consumes a real entry snapshot and produces 13;
    evaluating the same expression at the exit state would instead produce 253. -/
theorem lowEns_ok_zeuge [Kern] :
    lowEns layout frameLayout expression 8 = some compiled ∧
    EntrySnapshots.At layout entry memory 65536 (oldCells expression) 4 ∧
    eval entry expression exitWorld .nil ≠ eval exitWorld expression exitWorld .nil ∧
    ValueOk layout memory 0 65536 256 8 compiled.1 (.int 0 255) ⟨13, by decide, by decide⟩ := by
  refine ⟨emitted.1, saved, ?_, ?_⟩
  · intro same
    have same := congrArg Zahl.n same
    change (13 : Int) = 253 at same
    omega
  · exact lowEns_ok frameLayout entry exitWorld (fun _ h => h) lay expression 8
      compiled.1 compiled.2 emitted.1 emitted.2 memory 0 .nil
      (PreS.welt pre (by decide) loaded lay (by decide)) saved rfl

theorem count_entry_refused_zeuge :
    lowEns layout frameLayout
      (Expr.count 4 (.eq (.oldG global access) (.lit 19)) : Expr D [] [] (.int 0 4)) 8 = none := by
  decide +kernel

def globalCount : Expr D [] [] (.int 0 4) :=
  .count 4 (.lt (.var .here) (.glob global access))

theorem global_count_zeuge :
    Zahl.n (eval entry globalCount exitWorld .nil) = 3 ∧
    (lowE layout globalCount 8).isSome = true := by decide +kernel

def function : UFn := {name := "snapshot", params := [], kinds := [], res := some (0, 255),
                        held := [], puts := [], gives := [], body := [], ret := .val (.lit 0)}

/-- The source restoration calls the same checked builtin exporter and retains
    the entry read before the final restored-program checker runs. -/
theorem source_old_builtin_zeuge :
    (Gabbro.Stage0.OldSource.side unit [] [] function none
      (.bin "+%" (.old (.variable "counter")) (.lit 250))
      (.ib2 .addW 8 (.glob "counter") (.lit 250))).map
        (fun (s : LowSide unit [] []) =>
          (show Zahl s.range.1 s.range.2 from eval entry s.term exitWorld .nil).n) = .ok 13 := by
  decide +kernel

theorem source_old_builtin_mismatch_refused_zeuge :
    (Gabbro.Stage0.OldSource.side unit [] [] function none
      (.bin "-%" (.old (.variable "counter")) (.lit 250))
      (.ib2 .addW 8 (.glob "counter") (.lit 250))).isOk = false := by
  decide +kernel

end Gabbro.Stage0.Senke.BuiltinOldProbe
