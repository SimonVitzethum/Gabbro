/- Ordinary old reads follow the current world, even when a distinct entry snapshot exists. -/
module
public import Stage0.Senke.Ausdruck.Old.FunctionProbe
public import Stage0.Senke.Ausdruck.Old.Admission
@[expose] public section

namespace Gabbro.Stage0.Senke.CurrentOldProbe
open Gabbro.Grammatik Gabbro.Grammatik.Zielsatz Runner.IR Runner.Mem
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open OldProbe (layout entry exitWorld expr)
def code : List II := [ci 1 5 2048 0, ci 15 5 5 0]

/-- The same memory contains current global 80 and saved entry global 64. -/
theorem code_at : CodeAt (OldProbe.memory code) 0 code := by
  intro k hk
  have cases : k = 0 ∨ k = 1 := by change k < 2 at hk; omega
  rcases cases with rfl | rfl <;> constructor <;> decide +kernel +revert

theorem pre [Kern] :
    PreS layout (OldProbe.memory code) 0 1024 16 5 code
      (Env.nil : Env FnptrProben.D []) 1 :=
  ⟨by decide, by decide, OldProbe.frame _, code_at,
    by unfold CodeFar; decide +kernel, (fun _ x => nomatch x), trivial, wstab_true _ _⟩

/-- All premises of the generic ordinary expression theorem hold jointly. Its result
    is the current function pointer, although an entry snapshot of another pointer exists. -/
theorem lowE_oldG_ok_zeuge [Kern] :
    lowE layout expr 5 1 = some (code, 6) ∧
    PreS layout (OldProbe.memory code) 0 1024 16 5 code (Env.nil : Env FnptrProben.D []) 1 ∧
    EntrySnapshots.At layout entry (OldProbe.memory code) 1024 (oldCells expr) 4 ∧
    eval entry expr exitWorld .nil ≠ eval exitWorld expr exitWorld .nil ∧
    ValueOk layout (OldProbe.memory code) 0 1024 16 5 code (.fnptr 0)
      (eval exitWorld expr exitWorld .nil) := by
  refine ⟨by decide +kernel, pre, ?_, ?_, ?_⟩
  · exact ⟨ValueAt.of_enc (w := 64) (by decide) (by decide +kernel) rfl, trivial⟩
  · intro equal
    have value := congrArg (fun v : Wert FnptrProben.D (.fnptr 0) => v.1.val) equal
    change (0 : Nat) = 1 at value
    omega
  · exact lowE_ok (same := by intro _; rfl) exitWorld exitWorld (fun _ h => h) OldProbe.lay
      expr 5 code 6 (by decide +kernel) (by decide) (OldProbe.memory code) 0 .nil
      (PreS.welt pre (Nat.le_refl _) (OldProbe.world code) OldProbe.lay (by decide))

/-- A dynamic ordinary old-slot index uses the same emitter as an ordinary slot read;
    its value is None in the current world, while the entry field was Some(2). -/
theorem lowE_oldS_current_zeuge :
    lowE RuntimeOldProbe.layout RuntimeOldProbe.expr 9 4 =
      lowE RuntimeOldProbe.layout
        (Expr.slot QuantProbe.tab QuantProbe.field (.var .here) QuantProbe.access :
          Expr QuantProbe.D [.index 4] [] (.opt 4)) 9 4 ∧
    eval RuntimeOldProbe.exitWorld RuntimeOldProbe.expr RuntimeOldProbe.exitWorld RuntimeOldProbe.params = none ∧
    eval RuntimeOldProbe.entry RuntimeOldProbe.expr RuntimeOldProbe.exitWorld RuntimeOldProbe.params =
      some ⟨2, by decide, by decide⟩ := by
  exact ⟨rfl, rfl, rfl⟩

open OldFunctionProbe (D global tab field function global_access table_access)

/-- Both old forms appear after writes in the actual body, not in ensures. -/
def body : Endblock D (vertragVon D function) false [.index 4] [] :=
  .cons (.assignGlob global (.widen (by decide) (by decide) (.lit 1)) (by decide) global_access)
    (.cons (.assignSlot tab field (.var .here) (.oldG global global_access) (by decide) table_access)
      (.ret (.val (.oldS tab field (.var .here) table_access)) (.refl [])))

def program : Programm D := { OldFunctionProbe.program with
  requires := fun _ => .lt (.oldG global global_access) (.lit 10)
  rumpf := fun f => by
    obtain ⟨f, bound⟩ := f
    have zero : f = 0 := by change f < 1 at bound; omega
    subst f
    exact body }

/-- The canonical checker accepts these raw-model old occurrences outside ensures.
    The enumeration covers the complete singleton function, table and global domains. -/
theorem raw_model_admission_zeuge :
    AkzeptiertX program (SperrInv.leer D) [function] [] [.inl tab, .inr global] [] = true := by
  decide +kernel

/-- The connected function compiler accepts old in raw-model requires and body expressions.
    G returns the just-written 1, not the entry field 0, and the original ensures is preserved. -/
theorem ordinary_old_function_zeuge :
    (lowFun 1 program (fun _ => 0)
      (layU OldFunctionProbe.unit (fun _ => none) 8192) function).isSome = true ∧
    (match rufAt program OldFunctionProbe.oracle 1 1 function
        OldFunctionProbe.initial OldFunctionProbe.params with
      | .ok final value => value.n = 1 ∧ (final.globs global).n = 1 ∧ (final.slots tab 1 field).n = 1
      | _ => False) := by
  exact ⟨by decide +kernel, by decide +kernel⟩

end Gabbro.Stage0.Senke.CurrentOldProbe
