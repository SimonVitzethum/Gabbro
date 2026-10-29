/- Jointly inhabited entry/exit snapshot fixtures and explicit fragment refusals. -/
import Stage0.Senke.Ausdruck.Old.Capture
import Stage0.Senke.Ausdruck.FnptrProben
import Stage0.Senke.Ausdruck.Quant.Proben

namespace Gabbro.Stage0.Senke.OldProbe
open Gabbro.Grammatik Runner.IR Runner.Mem
open FnptrProben (D)
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

def layout : Lay D := FnptrProben.refLayout

def entry := FnptrProben.world

def exitWorld : World D := { entry with globs := fun _ => ⟨1, by decide⟩ }

def expr : Expr D [] [] (.fnptr 0) := .oldG () (by intro w h; cases h)

def readCode : List II := [ci 2 4 3 0]
def captureCode : List II := [ci 1 3 2048 0, ci 15 3 3 0]

/-- The exit global is 80; the saved entry word is 64. The code lies outside the frame. -/
def memory (code : List II) : Runner.Mem where
  b a := if a.toNat = 2048 then 80 else if a.toNat = 1048 then 64
    else if (2048 < a.toNat ∧ a.toNat < 2056) ∨ (1048 < a.toNat ∧ a.toNat < 1056) then 0
    else ((code.flatMap encII)[a.toNat]?).getD 0
  rd _ := true
  wr _ := true

theorem frame (c : List II) : FrameOK (memory c) 1024 16 :=
  ⟨by decide, fun _ _ => rfl, fun _ _ => rfl⟩

theorem lay : LayIn layout := by
  refine ⟨(fun t => nomatch t), ?_, by decide⟩
  intro g
  cases g
  decide +kernel

theorem world (c : List II) : WeltAt (memory c) layout exitWorld := by
  refine ⟨(fun t => nomatch t), ?_, fun _ _ _ => rfl⟩
  intro g
  cases g
  refine ⟨80, ?_, rfl⟩
  change (memory c).rd64 2048 = some 80
  simp [Runner.Mem.rd64, Runner.Mem.all, Runner.Mem.le, memory]

theorem read_at : CodeAt (memory readCode) 0 readCode := by
  intro k hk
  have : k = 0 := by simp only [readCode, List.length_singleton] at hk; omega
  subst k
  change InsAt (memory readCode) 0 2 (II.f 4) (II.f 3) (II.f 0)
  constructor <;> decide +kernel

theorem capture_at : CodeAt (memory captureCode) 0 captureCode := by
  intro k hk
  have : k = 0 ∨ k = 1 := by simp only [captureCode, List.length_cons, List.length_nil] at hk; omega
  rcases this with rfl | rfl
  · change InsAt (memory captureCode) 0 1 (II.f 3) (II.f 2048) (II.f 0)
    constructor <;> decide +kernel
  · change InsAt (memory captureCode) 16 15 (II.f 3) (II.f 3) (II.f 0)
    constructor <;> decide +kernel

theorem read_pre [Kern] : PreS layout (memory readCode) 0 1024 16 4 readCode (Env.nil : Env D []) := by
  refine ⟨by decide, by decide, frame _, read_at, ?_, (fun _ x => nomatch x), trivial, wstab_true _ _⟩
  unfold CodeFar
  decide +kernel

theorem saved : SnapAt layout (oldCells expr) entry (memory readCode) 1024 := by
  intro c hc
  simp only [expr, oldCells, List.mem_singleton] at hc
  subst c
  exact ⟨64, by decide +kernel, rfl⟩

/-- A real entry word differing from the exit global satisfies every simulation premise. -/
theorem lowEns_ok_zeuge [Kern] :
    lowEns layout expr 4 = some (readCode, 5) ∧
    PreS layout (memory readCode) 0 1024 16 4 readCode (Env.nil : Env D []) ∧
    SnapAt layout (oldCells expr) entry (memory readCode) 1024 ∧
    eval entry expr exitWorld .nil ≠ eval exitWorld expr exitWorld .nil ∧
    Ok (memory readCode) 0 1024 16 4 readCode (Enc layout (.fnptr 0) (eval entry expr exitWorld .nil)) := by
  refine ⟨rfl, read_pre, saved, ?_, ?_⟩
  · intro h
    have hh := congrArg (fun v : Wert D (.fnptr 0) => v.1.val) h
    change (0 : Nat) = 1 at hh
    omega
  · exact lowEns_ok entry exitWorld (fun _ h => h) expr 4 readCode 5 rfl (by decide)
      (memory readCode) 0 .nil (PreS.welt read_pre (Nat.le_refl _) (world readCode) lay (by decide)) saved

/-- Capture starts from a different header word and obtains the current world's global. -/
theorem snapC_ok_zeuge [Kern] :
    snapC layout [.glob ()] = some captureCode ∧
    ∃ m', Star ⟨0, 1024⟩ (memory captureCode) ⟨32, 1024⟩ m' ∧
      SnapAt layout [.glob ()] exitWorld m' 1024 := by
  refine ⟨by decide +kernel, ?_⟩
  obtain ⟨m', hs, _, hp, _⟩ := snapC_ok (L := layout) (cs := [.glob ()]) (c := captureCode)
    (m := memory captureCode) (pc := 0) (fp := 1024) (K := 16) (σ := exitWorld)
    (by decide +kernel) (frame _) (by decide) (by decide) capture_at (by unfold CodeFar; decide +kernel)
    (world captureCode) lay (by decide)
  exact ⟨m', hs, hp⟩

def tableLayout : Lay QuantProbe.D where
  col _ _ := 2048
  ga g := nomatch g
  lo := 2048
  hi := 2080
  tor _ := none
  byte _ := none

def slotExpr : Expr QuantProbe.D [] [] (.opt 4) :=
  .oldS QuantProbe.tab QuantProbe.field (QuantProbe.index 1 (by decide)) QuantProbe.access

theorem oldS_literal_zeuge : lowEns tableLayout slotExpr 4 = some (readCode, 5) := rfl

theorem oldS_parameter_refused_zeuge :
    lowEns tableLayout (Expr.oldS (Γ := [.index 4]) QuantProbe.tab QuantProbe.field
      (.var .here) QuantProbe.access) 5 = none := rfl

theorem multiple_occurrences_refused_zeuge : snapC layout [.glob (), .glob ()] = none := rfl

end Gabbro.Stage0.Senke.OldProbe
